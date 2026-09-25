"""表达式 DAG -> R1CS 编译、见证生成与逐约束审计（域 p=97）。

公开数据结构（见 README「接口」）::

    Node(kind, value=None, inputs=(), name=None)
    Constraint(index, node, tag, origin, a, b, c)
    VariableInfo(slot, role, node, name, kind)
    CompiledCircuit(p, n_vars, constraints, sources, inputs, nodes)
    ConstraintResult(index, node, tag, origin, satisfied, lhs, rhs, difference)
    AuditReport(ok, results, failures)

约束的稀疏表示：``a`` / ``b`` / ``c`` 均为 ``tuple[(var_index, coeff)]``，
按变量下标升序、系数已模 p 规约、零系数被剔除。完整见证向量记作 ``z``，
第 0 位恒为 1，约束语义为 ``<a,z> * <b,z> == <c,z> (mod p)``。
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Mapping

from .field import P, parse_scalar
from .errors import (
    CircuitBuildError,
    CircuitLimitError,
    CompileError,
    AuditError,
    UnknownInputError,
    UnexpectedInputError,
    NonBooleanSelectError,
    AssertEqualError,
    LookupTableError,
    LookupMembershipError,
)

MAX_NODES = 200

_CONST = "const"
_INPUT = "input"
_ADD = "add"
_MUL = "mul"
_SELECT = "select"
_ASSERT = "assert_equal"
_LOOKUP = "lookup"

_VALID_KINDS = frozenset(
    {_CONST, _INPUT, _ADD, _MUL, _SELECT, _ASSERT, _LOOKUP}
)
# 每种节点的子节点引用个数。
_ARITY = {
    _CONST: 0,
    _INPUT: 0,
    _ADD: 2,
    _MUL: 2,
    _SELECT: 3,
    _ASSERT: 2,
    _LOOKUP: 1,
}

#: lookup 表的长度上下限（题目契约：1..8 个互不相同的域元素）。
MAX_LOOKUP_TABLE = 8


# ---------------------------------------------------------------------------
# 公开数据结构
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Node:
    """表达式 DAG 节点。

    kind:
        - "const":        常量，value 为其 int 值（构造时模 97 规约）
        - "input":        命名输入，name 为输入名
        - "add"/"mul":    二元算术，inputs=(x, y) 为被引用节点的下标
        - "select":       inputs=(b, x, y)，b 非 0/1 时见证生成失败
        - "assert_equal": inputs=(x, y)，x!=y 时见证生成失败；输出值取 x
        - "lookup":       inputs=(value,)，table 为 1..8 个互不相同的规范
                          域元素；输出等于 value 且约束 value 属于该表
    """

    kind: str
    value: int | None = None
    inputs: tuple[int, ...] = ()
    name: str | None = None
    table: tuple[int, ...] | None = None


@dataclass(frozen=True)
class Constraint:
    """一条稀疏 R1CS 约束 ``<a,z>*<b,z>=<c,z>``。"""

    index: int
    node: int | None
    tag: str
    origin: str
    a: tuple[tuple[int, int], ...]
    b: tuple[tuple[int, int], ...]
    c: tuple[tuple[int, int], ...]


@dataclass(frozen=True)
class VariableInfo:
    """见证槽位来源说明（变量来源可审计）。"""

    slot: int
    role: str  # "constant_one" | "input" | "intermediate"
    node: int | None
    name: str | None
    kind: str | None


@dataclass(frozen=True)
class CompiledCircuit:
    p: int
    n_vars: int
    constraints: tuple[Constraint, ...]
    sources: tuple[VariableInfo, ...]
    inputs: Mapping[str, int]
    nodes: tuple[Node, ...]

    def source_of(self, slot: int) -> VariableInfo:
        return self.sources[slot]


@dataclass(frozen=True)
class ConstraintResult:
    index: int
    node: int | None
    tag: str
    origin: str
    satisfied: bool
    lhs: int
    rhs: int
    difference: int


@dataclass(frozen=True)
class AuditReport:
    ok: bool
    results: tuple[ConstraintResult, ...]

    @property
    def failures(self) -> tuple[ConstraintResult, ...]:
        return tuple(r for r in self.results if not r.satisfied)


# ---------------------------------------------------------------------------
# DAG 构建
# ---------------------------------------------------------------------------


class Circuit:
    """表达式 DAG 构造器。

    节点按下标顺序追加；任何被引用节点的下标都必须严格小于当前节点，
    因此 DAG 无环且节点插入顺序本身就是一个拓扑序。共享子表达式只需把
    同一个节点下标传给多个父节点——编译时只为其分配一个见证槽。

    所有构造方法在入参非法时直接抛异常且不追加节点（不留部分变更）。
    """

    def __init__(self) -> None:
        self._nodes: list[Node] = []
        self._input_names: set[str] = set()
        # 相同的表复用同一个规范化元组对象（常量结构共享）。
        self._tables: dict[tuple[int, ...], tuple[int, ...]] = {}

    # -- 基础属性 -----------------------------------------------------------

    @property
    def nodes(self) -> tuple[Node, ...]:
        return tuple(self._nodes)

    def __len__(self) -> int:
        return len(self._nodes)

    def get_node(self, index: int) -> Node:
        self._check_ref(index, "get_node")
        return self._nodes[index]

    # -- 节点构造 -----------------------------------------------------------

    def const(self, value: int) -> int:
        """追加常量节点；value 必须为 int（拒绝 bool/float/NaN/Infinity）。"""

        v = parse_scalar(value, what="const value")
        return self._append(Node(_CONST, value=v))

    def input(self, name: str) -> int:
        """追加命名输入节点；名字必须是非空 str 且电路内唯一。"""

        if not isinstance(name, str):
            raise TypeError(f"input name must be str, got {type(name).__name__}")
        if len(name) == 0:
            raise ValueError("input name must be a non-empty string")
        if name in self._input_names:
            raise CircuitBuildError(f"duplicate input name: {name!r}")
        # 先追加（可能触发节点上限），成功后再登记名字，保证失败无部分变更。
        index = self._append(Node(_INPUT, name=name))
        self._input_names.add(name)
        return index

    def add(self, x: int, y: int) -> int:
        self._check_ref(x, "add x")
        self._check_ref(y, "add y")
        return self._append(Node(_ADD, inputs=(x, y)))

    def mul(self, x: int, y: int) -> int:
        self._check_ref(x, "mul x")
        self._check_ref(y, "mul y")
        return self._append(Node(_MUL, inputs=(x, y)))

    def select(self, b: int, x: int, y: int) -> int:
        """追加 select(b,x,y) 节点：b∈{0,1} 时输出 b*x+(1-b)*y。"""

        self._check_ref(b, "select b")
        self._check_ref(x, "select x")
        self._check_ref(y, "select y")
        return self._append(Node(_SELECT, inputs=(b, x, y)))

    def assert_equal(self, x: int, y: int) -> int:
        """追加 assert_equal(x,y) 节点：见证生成时要求 x==y (mod 97)。"""

        self._check_ref(x, "assert_equal x")
        self._check_ref(y, "assert_equal y")
        return self._append(Node(_ASSERT, inputs=(x, y)))

    def lookup(self, value: int, table: object) -> int:
        """追加 lookup(value, table) 节点。

        ``table`` 必须是 1..8 个**互不相同**的**规范域元素**
        （``int`` 且 ``0 <= v < 97``；拒绝 bool）。空表、重复元素、
        非规范值（如 97 / -1）或非法类型在构建期直接拒绝。

        节点输出值等于 ``value``；编译时额外用成员多项式
        ``prod_j (value - t_j) = 0`` 拆成的原始 R1CS 乘法门约束
        ``value`` 属于表——不引入任何没有约束的宿主布尔判断。
        表元素的顺序被保留（影响连乘中间槽的计算顺序），相同的表
        结构在电路内复用同一个规范化对象。
        """

        self._check_ref(value, "lookup value")
        norm = self._intern_table(_validate_lookup_table(table))
        return self._append(Node(_LOOKUP, inputs=(value,), table=norm))

    def _intern_table(self, norm: tuple[int, ...]) -> tuple[int, ...]:
        existing = self._tables.get(norm)
        if existing is None:
            self._tables[norm] = norm
            return norm
        return existing

    # -- 内部 ---------------------------------------------------------------

    def _check_ref(self, ref: object, what: str) -> None:
        if isinstance(ref, bool) or not isinstance(ref, int):
            raise TypeError(
                f"{what} node reference must be int, got {type(ref).__name__}"
            )
        if not (0 <= ref < len(self._nodes)):
            raise CircuitBuildError(
                f"{what} references node {ref}, which is out of range "
                f"[0, {len(self._nodes)})"
            )

    def _append(self, node: Node) -> int:
        if len(self._nodes) >= MAX_NODES:
            raise CircuitLimitError(
                f"circuit node limit exceeded: at most {MAX_NODES} nodes"
            )
        self._nodes.append(node)
        return len(self._nodes) - 1


def _validate_lookup_table(table: object) -> tuple[int, ...]:
    """校验 lookup 表并返回规范化元组（顺序保留）。

    规则（构建期确定性拒绝，不静默纠正）:
      - 必须是 list/tuple（不接受集合等无序对象，以保留可复现的
        连乘顺序）；长度 1..MAX_LOOKUP_TABLE。
      - 每个元素必须是规范域元素：int、非 bool、0 <= v < P。
        负数与 >= P 的值在这里直接拒绝（不做模规约），因为题目要求
        「非规范域值先拒绝」。
      - 元素不得重复。
    """

    if not isinstance(table, (list, tuple)):
        raise TypeError(
            "lookup table must be a list or tuple of canonical field "
            f"elements, got {type(table).__name__}"
        )
    if len(table) == 0:
        raise LookupTableError("lookup table must contain 1..8 elements, got 0")
    if len(table) > MAX_LOOKUP_TABLE:
        raise LookupTableError(
            f"lookup table too large: {len(table)} elements, at most "
            f"{MAX_LOOKUP_TABLE}"
        )
    seen: set[int] = set()
    normalized: list[int] = []
    for idx, item in enumerate(table):
        if isinstance(item, bool):
            raise TypeError(
                f"lookup table[{idx}] must be int, got bool (booleans are "
                "not accepted)"
            )
        if not isinstance(item, int):
            if isinstance(item, float):
                if math.isnan(item):
                    raise ValueError(f"lookup table[{idx}] must be int, got NaN")
                if math.isinf(item):
                    raise ValueError(
                        f"lookup table[{idx}] must be int, got Infinity"
                    )
            raise TypeError(
                f"lookup table[{idx}] must be int, got {type(item).__name__}"
            )
        if not (0 <= item < P):
            raise ValueError(
                f"lookup table[{idx}]={item} is not a canonical field "
                f"element [0, {P - 1}]; values are not reduced here"
            )
        if item in seen:
            raise LookupTableError(
                f"lookup table contains duplicate element {item} at index {idx}"
            )
        seen.add(item)
        normalized.append(item)
    return tuple(normalized)


# ---------------------------------------------------------------------------
# 编译：DAG -> R1CS
# ---------------------------------------------------------------------------


def _sparse(terms: Mapping[int, int]) -> tuple[tuple[int, int], ...]:
    """把 {槽位: 系数} 规约为排序后的稀疏元组，剔除模 p 为 0 的系数。"""

    out: list[tuple[int, int]] = []
    for slot in sorted(terms):
        coeff = terms[slot] % P
        if coeff:
            out.append((slot, coeff))
    return tuple(out)


def compile_circuit(circuit: Circuit) -> CompiledCircuit:
    """把 DAG 编译为稀疏 R1CS。

    每个非常量节点恰占用一个见证槽（共享节点不重复分配）；槽 0 恒为 1。
    编译失败抛 CompileError，且不产生任何部分结果。
    """

    if not isinstance(circuit, Circuit):
        raise TypeError(f"compile_circuit expects Circuit, got {type(circuit).__name__}")

    nodes = circuit.nodes
    n = len(nodes)

    # 防御式结构校验（正常经 Circuit 构造的 DAG 不会触发）。
    for i, node in enumerate(nodes):
        if node.kind not in _VALID_KINDS:
            raise CompileError(f"node {i} has unknown kind {node.kind!r}")
        if len(node.inputs) != _ARITY[node.kind]:
            raise CompileError(
                f"node {i} ({node.kind}) expects {_ARITY[node.kind]} inputs, "
                f"got {len(node.inputs)}"
            )
        for ref in node.inputs:
            if not (0 <= ref < i):
                raise CompileError(
                    f"node {i} references {ref}; references must point to an "
                    f"earlier node in [0, {i})"
                )
        if node.kind == _LOOKUP:
            if not isinstance(node.table, tuple) or not (
                1 <= len(node.table) <= MAX_LOOKUP_TABLE
            ):
                raise CompileError(
                    f"lookup node {i} has an invalid table structure"
                )
            if any(not isinstance(t, int) or isinstance(t, bool)
                   or not (0 <= t < P) for t in node.table):
                raise CompileError(
                    f"lookup node {i} table holds non-canonical elements"
                )
            if len(set(node.table)) != len(node.table):
                raise CompileError(f"lookup node {i} table has duplicates")

    # -- 槽位分配（节点下标顺序即拓扑序）------------------------------------
    # lookup 节点除输出槽外，还要为成员多项式连乘分配 k 个中间槽 m_0..m_{k-1}：
    # 每个 lookup 独享自己的中间槽（即使多个 lookup 共用同一张表，
    # 不同 value 的中间值也绝不共享）。
    slot_of: dict[int, int] = {}
    lookup_aux_slots: dict[int, tuple[int, ...]] = {}
    sources: list[VariableInfo] = [
        VariableInfo(0, "constant_one", None, None, None)
    ]
    input_slots: dict[str, int] = {}
    next_slot = 1
    for i, node in enumerate(nodes):
        if node.kind == _CONST:
            continue
        if node.kind == _LOOKUP:
            assert node.table is not None
            aux: list[int] = []
            for _t in node.table:
                sources.append(
                    VariableInfo(next_slot, "intermediate", i, None,
                                 "lookup_aux")
                )
                aux.append(next_slot)
                next_slot += 1
            lookup_aux_slots[i] = tuple(aux)
        slot_of[i] = next_slot
        role = "input" if node.kind == _INPUT else "intermediate"
        sources.append(VariableInfo(next_slot, role, i, node.name, node.kind))
        if node.kind == _INPUT:
            assert node.name is not None
            input_slots[node.name] = next_slot
        next_slot += 1

    # -- 逐节点生成约束 ------------------------------------------------------
    #
    # 常量节点不占见证槽：在约束中把它内联为常数槽 0 上的系数。
    # lin(i) 表示「节点 i 的值」的线性项：常量 -> {0: 值}，其余 -> {槽: 1}。
    const_value: dict[int, int] = {
        i: nd.value for i, nd in enumerate(nodes) if nd.kind == _CONST
    }

    def lin(node_id: int) -> dict[int, int]:
        if node_id in const_value:
            return {0: const_value[node_id]}
        return {slot_of[node_id]: 1}

    def merge(*parts: tuple[Mapping[int, int], int]) -> dict[int, int]:
        """合并若干 (线性项, 正负号)，系数可抵消，零值交由 _sparse 剔除。"""

        out: dict[int, int] = {}
        for terms, sign in parts:
            for slot, coeff in terms.items():
                out[slot] = out.get(slot, 0) + sign * coeff
        return out

    constraints: list[Constraint] = []

    def emit(node_id: int | None, tag: str, origin: str,
             a: Mapping[int, int], b: Mapping[int, int],
             c: Mapping[int, int]) -> None:
        constraints.append(
            Constraint(
                index=len(constraints),
                node=node_id,
                tag=tag,
                origin=origin,
                a=_sparse(a),
                b=_sparse(b),
                c=_sparse(c),
            )
        )

    for i, node in enumerate(nodes):
        if node.kind == _ADD:
            x, y = node.inputs
            v = slot_of[i]
            # 1 * v = lin(x) + lin(y)（常量在此内联为常数系数）
            emit(i, "add", f"add node {i}: v = x + y",
                 {0: 1}, {v: 1}, merge((lin(x), 1), (lin(y), 1)))
        elif node.kind == _MUL:
            x, y = node.inputs
            # lin(x) * lin(y) = v
            emit(i, "mul", f"mul node {i}: v = x * y",
                 lin(x), lin(y), {slot_of[i]: 1})
        elif node.kind == _SELECT:
            b, x, y = node.inputs
            sv = slot_of[i]
            # 选择位也允许是常量节点：lin(b) 在常量时落在常数槽上，
            # 非布尔常量会产生不可满足约束，见证生成同样会报错。
            lb = lin(b)
            # 1) b * (lin(x) - lin(y)) = v - lin(y)
            #    配合布尔性约束，恰好等价于 v = b*x + (1-b)*y。
            emit(i, "select_value",
                 f"select node {i}: b*(x-y) = v-y",
                 lb,
                 merge((lin(x), 1), (lin(y), -1)),
                 merge(({sv: 1}, 1), (lin(y), -1)))
            # 2) b * (b - 1) = 0 —— 强制 b∈{0,1}
            emit(i, "select_booleanity",
                 f"select node {i}: b*(b-1) = 0 (boolean selector)",
                 lb, merge((lb, 1), ({0: 1}, -1)), {})
        elif node.kind == _ASSERT:
            x, y = node.inputs
            v = slot_of[i]
            # 输出槽定义：1 * v = lin(x)
            emit(i, "assert_value",
                 f"assert_equal node {i}: output v takes left operand",
                 {0: 1}, {v: 1}, lin(x))
            # 相等性：(lin(x) - lin(y)) * 1 = 0
            emit(i, "assert_equal",
                 f"assert_equal node {i}: x - y = 0",
                 merge((lin(x), 1), (lin(y), -1)), {0: 1}, {})
        elif node.kind == _LOOKUP:
            (value_ref,) = node.inputs
            table = node.table
            assert table is not None
            k = len(table)
            v = slot_of[i]
            aux_slots = lookup_aux_slots[i]
            lv = lin(value_ref)

            # 成员多项式 P(x) = prod_j (x - t_j)。在域 p=97 上：
            #   value 属于表  <=>  P(value) = 0
            # （表元素互异；即使表含 0 也成立。）不引入宿主布尔判断，
            # 全部拆成原始 R1CS 乘法门，每个连乘中间值独占见证槽。
            #
            # m_0 = value - t_0
            t0 = table[0]
            emit(i, "lookup_head",
                 f"lookup node {i}: m0 = value - {t0}",
                 {0: 1}, {aux_slots[0]: 1},
                 merge((lv, 1), ({0: t0}, -1)))
            # m_j = m_{j-1} * (value - t_j), j = 1..k-1
            for j in range(1, k):
                emit(i, "lookup_chain",
                     f"lookup node {i}: m{j} = m{j-1} * (value - {table[j]})",
                     {aux_slots[j - 1]: 1},
                     merge((lv, 1), ({0: table[j]}, -1)),
                     {aux_slots[j]: 1})
            # 输出 v = value，同时末尾因子积 m_{k-1} 必须为 0：
            #   1 * v = lin(value)
            emit(i, "lookup_value",
                 f"lookup node {i}: output v = value",
                 {0: 1}, {v: 1}, lv)
            #   m_{k-1} * 1 = 0
            emit(i, "lookup_membership",
                 f"lookup node {i}: membership product m{k-1} = 0",
                 {aux_slots[-1]: 1}, {0: 1}, {})

    return CompiledCircuit(
        p=P,
        n_vars=next_slot,
        constraints=tuple(constraints),
        sources=tuple(sources),
        inputs=dict(input_slots),
        nodes=nodes,
    )


# ---------------------------------------------------------------------------
# 见证生成（直接在域上按 DAG 求值；不求解矩阵）
# ---------------------------------------------------------------------------


def _check_user_inputs(raw: object) -> Mapping[str, object]:
    if not isinstance(raw, Mapping):
        raise TypeError(
            f"inputs must be a mapping of name->int, got {type(raw).__name__}"
        )
    return raw


def generate_witness(compiled: CompiledCircuit,
                      user_inputs: Mapping[str, object]) -> list[int]:
    """根据命名输入生成完整见证向量 z（z[0]=1）。

    失败语义（均在返回前抛出，绝不返回部分见证）:
      - 多余/未声明输入名，或输入名不是 str: UnexpectedInputError / TypeError
      - 缺失输入: UnknownInputError（确定无解；本库无搜索，故不存在预算耗尽）
      - 输入值非 int 有限标量（bool / NaN / Infinity 等）: TypeError/ValueError
      - select 选择位非布尔: NonBooleanSelectError
      - assert_equal 不成立: AssertEqualError
      - lookup 的 value 不属于表: LookupMembershipError

    中间槽全部由本函数按 DAG 重新计算，调用方无法通过 user_inputs 覆盖。
    """

    if not isinstance(compiled, CompiledCircuit):
        raise TypeError("generate_witness expects a CompiledCircuit")
    mapping = _check_user_inputs(user_inputs)

    # 键类型先做一次显式检查，给出可定位错误。
    for key in mapping:
        if not isinstance(key, str):
            raise TypeError(
                f"input names must be str, got {type(key).__name__}: {key!r}"
            )

    declared = set(compiled.inputs)
    extra = set(mapping) - declared
    if extra:
        raise UnexpectedInputError(sorted(extra)[0])

    n_vars = compiled.n_vars
    z: list[int] = [0] * n_vars
    z[0] = 1
    vals: dict[int, int] = {}

    # 由变量来源表预计算 节点->主见证槽（常量节点不在表中）。
    slot_of_node: dict[int, int] = {
        info.node: info.slot
        for info in compiled.sources
        if info.node is not None and info.kind != "select_aux"
    }

    # lookup 节点 -> 连乘中间槽（按 m_0..m_{k-1} 排序）。每次 lookup
    # 各自独立；同一张表被两个 lookup 共享时中间槽也互不相同。
    lookup_aux_of_node: dict[int, list[int]] = {}
    for info in compiled.sources:
        if info.kind == "lookup_aux":
            lookup_aux_of_node.setdefault(info.node, []).append(info.slot)
    for node_id in lookup_aux_of_node:
        lookup_aux_of_node[node_id].sort()

    # 先做输入取值与缺失检查（parse_scalar 负责 NaN/Infinity/bool 语义），
    # 保证进入逐节点计算前所有外部值已确定，失败即整体失败。
    input_values: dict[int, int] = {}
    for name, slot in compiled.inputs.items():
        if name not in mapping:
            raise UnknownInputError(name)
        input_values[slot] = parse_scalar(mapping[name], what=f"input {name!r}")

    for i, node in enumerate(compiled.nodes):
        if node.kind == _CONST:
            vals[i] = node.value  # type: ignore[assignment]
            continue

        slot = slot_of_node[i]

        if node.kind == _INPUT:
            v = input_values[slot]
        elif node.kind == _ADD:
            x, y = node.inputs
            v = (vals[x] + vals[y]) % P
        elif node.kind == _MUL:
            x, y = node.inputs
            v = (vals[x] * vals[y]) % P
        elif node.kind == _SELECT:
            b, x, y = node.inputs
            bv, xv, yv = vals[b], vals[x], vals[y]
            if bv not in (0, 1):
                raise NonBooleanSelectError(i, bv)
            v = (bv * xv + (1 - bv) * yv) % P
        elif node.kind == _LOOKUP:
            (value_ref,) = node.inputs
            assert node.table is not None
            vv = vals[value_ref]
            product = 1
            for j, tj in enumerate(node.table):
                product = (product * (vv - tj)) % P
                z[lookup_aux_of_node[i][j]] = product
            # 连乘末槽非 0 => value 不属于表；对任何伪造的中间值，
            # 审计侧的 R1CS 门同样会失败（见 lookup_* 约束）。
            if product != 0:
                raise LookupMembershipError(i, vv, node.table)
            v = vv
        else:  # assert_equal
            x, y = node.inputs
            if vals[x] != vals[y]:
                raise AssertEqualError(i, vals[x], vals[y])
            v = vals[x]

        z[slot] = v
        vals[i] = v

    return z


# ---------------------------------------------------------------------------
# 审计
# ---------------------------------------------------------------------------


def _check_witness_shape(compiled: CompiledCircuit, witness: object) -> list[int]:
    if not isinstance(witness, (list, tuple)):
        raise AuditError(
            f"witness must be a list/tuple, got {type(witness).__name__}"
        )
    if len(witness) != compiled.n_vars:
        raise AuditError(
            f"witness length {len(witness)} != compiled n_vars "
            f"{compiled.n_vars}"
        )
    for idx, item in enumerate(witness):
        if isinstance(item, bool):
            raise AuditError(f"witness[{idx}] is bool; field elements must be int")
        if isinstance(item, float):
            if math.isnan(item):
                raise AuditError(f"witness[{idx}] is NaN")
            if math.isinf(item):
                raise AuditError(f"witness[{idx}] is Infinity")
            raise AuditError(f"witness[{idx}] is float; field elements must be int")
        if not isinstance(item, int):
            raise AuditError(
                f"witness[{idx}] must be int, got {type(item).__name__}"
            )
        if not (0 <= item < P):
            raise AuditError(
                f"witness[{idx}]={item} is not a canonical field element "
                f"[0, {P - 1}]"
            )
    if witness[0] != 1:
        raise AuditError("witness[0] must be the constant 1")
    return list(witness)


def _dot(sparse: tuple[tuple[int, int], ...], z: list[int]) -> int:
    total = 0
    for slot, coeff in sparse:
        total += coeff * z[slot]
    return total % P


def audit(compiled: CompiledCircuit, witness: object) -> AuditReport:
    """逐条重算 R1CS 约束，返回每条约束的通过/失败明细。

    见证形状非法（长度、类型、值域、z[0]!=1）时抛 AuditError；
    形状合法时始终返回 AuditReport，由 ``report.ok`` 与
    ``report.failures`` 给出逐约束定位，绝不静默丢弃失败。
    """

    if not isinstance(compiled, CompiledCircuit):
        raise TypeError("audit expects a CompiledCircuit")
    z = _check_witness_shape(compiled, witness)

    results: list[ConstraintResult] = []
    for con in compiled.constraints:
        lhs = (_dot(con.a, z) * _dot(con.b, z)) % P
        rhs = _dot(con.c, z)
        results.append(
            ConstraintResult(
                index=con.index,
                node=con.node,
                tag=con.tag,
                origin=con.origin,
                satisfied=(lhs == rhs),
                lhs=lhs,
                rhs=rhs,
                difference=(lhs - rhs) % P,
            )
        )
    return AuditReport(ok=all(r.satisfied for r in results),
                       results=tuple(results))
