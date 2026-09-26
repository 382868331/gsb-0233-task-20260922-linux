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
    NonBooleanGuardSelectorError,
    AssertEqualError,
    GuardedEqualError,
)

MAX_NODES = 200

_CONST = "const"
_INPUT = "input"
_ADD = "add"
_MUL = "mul"
_SELECT = "select"
_ASSERT = "assert_equal"
_GUARDED = "guarded_equal"

_VALID_KINDS = frozenset({
    _CONST, _INPUT, _ADD, _MUL, _SELECT, _ASSERT, _GUARDED,
})
# 每种节点的子节点引用个数。
_ARITY = {
    _CONST: 0,
    _INPUT: 0,
    _ADD: 2,
    _MUL: 2,
    _SELECT: 3,
    _ASSERT: 2,
    _GUARDED: 3,
}


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
        - "guarded_equal": inputs=(b, x, y)，仅 b=1 要求 x==y；输出值取 x
    """

    kind: str
    value: int | None = None
    inputs: tuple[int, ...] = ()
    name: str | None = None


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

    def guarded_equal(self, b: int, x: int, y: int) -> int:
        """追加 guarded_equal(b,x,y)：仅 b=1 时要求 x==y；输出始终取 x。"""

        self._check_ref(b, "guarded_equal b")
        self._check_ref(x, "guarded_equal x")
        self._check_ref(y, "guarded_equal y")
        return self._append(Node(_GUARDED, inputs=(b, x, y)))

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

    # -- 槽位分配（节点下标顺序即拓扑序）------------------------------------
    slot_of: dict[int, int] = {}
    sources: list[VariableInfo] = [
        VariableInfo(0, "constant_one", None, None, None)
    ]
    input_slots: dict[str, int] = {}
    next_slot = 1
    for i, node in enumerate(nodes):
        if node.kind == _CONST:
            continue
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
        elif node.kind == _GUARDED:
            b, x, y = node.inputs
            v = slot_of[i]
            lb = lin(b)

            # 输出槽始终取左侧；b=0 时该槽也由见证生成器明确赋值。
            emit(i, "guarded_value",
                 f"guarded_equal node {i}: output v takes left operand",
                 {0: 1}, {v: 1}, lin(x))
            # 选择位必须是布尔值；不能只靠见证生成器拒绝 b=2。
            emit(i, "guarded_booleanity",
                 f"guarded_equal node {i}: b*(b-1) = 0 (boolean selector)",
                 lb, merge((lb, 1), ({0: 1}, -1)), {})
            # b=1 时 x-y=0；b=0 时左因子为 0，整式自动成立。
            emit(i, "guarded_equal",
                 f"guarded_equal node {i}: b*(x-y) = 0",
                 lb,
                 merge((lin(x), 1), (lin(y), -1)),
                 {})

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
      - select/guarded_equal 选择位非布尔: 对应 NonBoolean* 错误
      - assert_equal 不成立: AssertEqualError
      - guarded_equal 在 b=1 时不成立: GuardedEqualError

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
        elif node.kind == _ASSERT:
            x, y = node.inputs
            if vals[x] != vals[y]:
                raise AssertEqualError(i, vals[x], vals[y])
            v = vals[x]
        else:  # guarded_equal
            b, x, y = node.inputs
            bv = vals[b]
            if bv not in (0, 1):
                raise NonBooleanGuardSelectorError(i, bv)
            if bv == 1 and vals[x] != vals[y]:
                raise GuardedEqualError(i, vals[x], vals[y])
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
