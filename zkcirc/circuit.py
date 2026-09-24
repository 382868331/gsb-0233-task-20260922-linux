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
from .field import (
    check_width,
    signed_range,
    signed_to_bits,
)
from .errors import (
    CircuitBuildError,
    CircuitLimitError,
    CompileError,
    AuditError,
    UnknownInputError,
    UnexpectedInputError,
    NonBooleanSelectError,
    AssertEqualError,
    SignedInputError,
)

MAX_NODES = 200

_CONST = "const"
_INPUT = "input"
_ADD = "add"
_MUL = "mul"
_SELECT = "select"
_ASSERT = "assert_equal"
# 2..8 位有符号整数（二补码）族节点。
_SIGNED_INPUT = "signed_input"
_SIGNED_CONST = "signed_const"
_SADD = "sadd"
_SSUB = "ssub"
_SLT = "slt"   # 有符号 a < b，输出 0/1
_SLE = "sle"   # 有符号 a <= b，输出 0/1
_SEQ = "seq"   # 有符号 a == b，输出 0/1

# 带 w 位二补码数据的节点（可作为有符号运算/比较的操作数）。
_SIGNED_VALUE_KINDS = frozenset(
    {_SIGNED_INPUT, _SIGNED_CONST, _SADD, _SSUB}
)

_VALID_KINDS = frozenset({
    _CONST, _INPUT, _ADD, _MUL, _SELECT, _ASSERT,
    _SIGNED_INPUT, _SIGNED_CONST, _SADD, _SSUB, _SLT, _SLE, _SEQ,
})
# 每种节点的子节点引用个数。
_ARITY = {
    _CONST: 0,
    _INPUT: 0,
    _ADD: 2,
    _MUL: 2,
    _SELECT: 3,
    _ASSERT: 2,
    _SIGNED_INPUT: 0,
    _SIGNED_CONST: 0,
    _SADD: 2,
    _SSUB: 2,
    _SLT: 2,
    _SLE: 2,
    _SEQ: 2,
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
        - "signed_input": 2..8 位有符号命名输入，width 为位宽，
                          合法值 [-2**(w-1), 2**(w-1)-1]
        - "signed_const": 同范围有符号常量，value 为其有符号 int 值
        - "sadd"/"ssub":  w 位有符号加/减，溢出仅回绕
        - "slt"/"sle"/"seq": 有符号 < / <= / ==，输出 0/1 标志
    """

    kind: str
    value: int | None = None
    inputs: tuple[int, ...] = ()
    name: str | None = None
    width: int | None = None


@dataclass(frozen=True)
class SignedLayout:
    """一个 w 位有符号「值」节点的见证槽布局（源码映射）。

    bit_slots:  小端 w 个比特槽（bit_slots[0]=LSB，末位即符号位），
                每个槽被布尔性约束钉在 {0,1}。
    carry_slots: 仅 sadd/ssub 非空：w+1 个进位/借位槽，carry_slots[0]
                被钉为 0，逐位全加/全减约束钉住其余。
    word_slot:  该节点的主槽（= 旧意义上的节点槽），存放比特拼出的
                二补码无符号字 Σ 2**i·b_i mod 97，由线性组合约束钉住。
    """

    node: int
    width: int
    bit_slots: tuple[int, ...]
    carry_slots: tuple[int, ...]
    word_slot: int


@dataclass(frozen=True)
class SignedCmpLayout:
    """有符号比较节点（slt/sle/seq）的见证槽布局。

    flag_slot:  节点主槽，比较结果 0/1。
    diff_bits/borrows: slt/sle 使用的内部 w 位差值与 w+1 个借位。
    eq_prod/eq_chain:  seq 使用的逐位乘积辅助 t_i 与 w 个链辅助
                （链尾即 flag_slot）。
    """

    node: int
    width: int
    op: str  # "slt" | "sle" | "seq"
    flag_slot: int
    diff_bits: tuple[int, ...]
    borrows: tuple[int, ...]
    eq_prod: tuple[int, ...]
    eq_chain: tuple[int, ...]


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
    # 有符号能力新增（旧字段语义全部不变）：
    # 普通输入（input）与有符号输入（signed_input）名空间共用、
    # 都登记在 inputs 中；signed_inputs 只列出有符号输入的额外元信息。
    signed_inputs: Mapping[str, int] = field(default_factory=dict)
    # 节点下标 -> 有符号值/比较节点的逐位槽位布局（源码映射）。
    signed_layouts: Mapping[int, SignedLayout] = field(default_factory=dict)
    signed_cmp_layouts: Mapping[int, SignedCmpLayout] = field(default_factory=dict)

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
        # 普通输入与有符号输入共用同一名字空间。
        self._input_names: set[str] = set()
        # 有符号值节点（signed_input/signed_const/sadd/ssub）的位宽登记。
        self._width_of: dict[int, int] = {}

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

    # -- 2..8 位有符号整数 --------------------------------------------------

    def signed_input(self, name: str, width: int) -> int:
        """追加 w 位有符号命名输入（二补码）。

        合法值闭区间 [-2**(w-1), 2**(w-1)-1]，w∈[2,8]。见证生成时调用方
        仍只按名字给一个普通 Python int；越界/类型非法都会被明确拒绝。
        """

        w = check_width(width)
        if not isinstance(name, str):
            raise TypeError(f"input name must be str, got {type(name).__name__}")
        if len(name) == 0:
            raise ValueError("input name must be a non-empty string")
        if name in self._input_names:
            raise CircuitBuildError(f"duplicate input name: {name!r}")
        index = self._append(Node(_SIGNED_INPUT, name=name, width=w))
        self._input_names.add(name)
        self._width_of[index] = w
        return index

    def signed_const(self, value: int, width: int) -> int:
        """追加 w 位有符号常量；value 必须落在该位宽区间内（不静默回绕）。"""

        w = check_width(width)
        if isinstance(value, bool) or not isinstance(value, int):
            raise TypeError(
                f"signed const value must be int, got {type(value).__name__}"
            )
        low, high = signed_range(w)
        if not (low <= value <= high):
            raise ValueError(
                f"signed const value {value} out of range [{low}, {high}] "
                f"for width {w}"
            )
        index = self._append(Node(_SIGNED_CONST, value=value, width=w))
        self._width_of[index] = w
        return index

    def sadd(self, x: int, y: int) -> int:
        """w 位有符号加法（溢出仅按二补码回绕）；x、y 必须同宽。"""

        return self._signed_binop(_SADD, x, y)

    def ssub(self, x: int, y: int) -> int:
        """w 位有符号减法（溢出仅按二补码回绕）；x、y 必须同宽。"""

        return self._signed_binop(_SSUB, x, y)

    def slt(self, x: int, y: int) -> int:
        """有符号比较 x < y；输出一个被布尔性约束钉住的 0/1 标志节点。"""

        return self._signed_binop(_SLT, x, y)

    def sle(self, x: int, y: int) -> int:
        """有符号比较 x <= y；输出 0/1 标志节点。"""

        return self._signed_binop(_SLE, x, y)

    def seq(self, x: int, y: int) -> int:
        """有符号比较 x == y；输出 0/1 标志节点。"""

        return self._signed_binop(_SEQ, x, y)

    def _signed_binop(self, kind: str, x: int, y: int) -> int:
        what = kind
        self._check_ref(x, f"{what} x")
        self._check_ref(y, f"{what} y")
        wx = self._width_of.get(x)
        wy = self._width_of.get(y)
        if wx is None:
            raise CircuitBuildError(
                f"{what} operand x (node {x}) is not a signed value node "
                f"(signed_input/signed_const/sadd/ssub)"
            )
        if wy is None:
            raise CircuitBuildError(
                f"{what} operand y (node {y}) is not a signed value node "
                f"(signed_input/signed_const/sadd/ssub)"
            )
        if wx != wy:
            raise CircuitBuildError(
                f"{what} operands must have equal signed width, got "
                f"node {x} width {wx} and node {y} width {wy}"
            )
        index = self._append(Node(kind, inputs=(x, y), width=wx))
        # sadd/ssub 的结果仍是同宽有符号值；比较结果是 0/1 标志，不登记。
        if kind in (_SADD, _SSUB):
            self._width_of[index] = wx
        return index

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
        if node.kind in (_SADD, _SSUB, _SLT, _SLE, _SEQ):
            x, y = node.inputs
            kx, ky = nodes[x].kind, nodes[y].kind
            if kx not in _SIGNED_VALUE_KINDS or ky not in _SIGNED_VALUE_KINDS:
                raise CompileError(
                    f"node {i} ({node.kind}) operands must be signed value "
                    f"nodes, got {kx!r}/{ky!r}"
                )
            if nodes[x].width != node.width or nodes[y].width != node.width:
                raise CompileError(
                    f"node {i} ({node.kind}) operand width mismatch"
                )
        if node.kind in (_SIGNED_INPUT, _SIGNED_CONST, _SADD, _SSUB):
            if node.width is None:
                raise CompileError(f"node {i} ({node.kind}) missing width")
        if node.kind == _SIGNED_CONST:
            low, high = signed_range(node.width)  # type: ignore[arg-type]
            if not (low <= (node.value or 0) <= high):
                raise CompileError(
                    f"node {i} signed_const value out of range"
                )

    # -- 槽位分配（节点下标顺序即拓扑序）------------------------------------
    #
    # 普通非常量节点各占 1 个主槽。有符号节点展开为多个见证槽：
    #   signed_input : w 个比特槽 + 1 个字槽（字槽登记为命名输入槽）
    #   signed_const : 不占槽（比特/字都以内联常数出现，沿用「常量不占槽」）
    #   sadd/ssub    : w 个结果比特槽 + w+1 个进位/借位槽 + 1 个字槽
    #   slt/sle      : w 个差值比特槽 + w+1 个借位槽 + 1 个标志槽
    #   seq          : w 个逐位同或槽 + w 个链槽（链尾即标志槽）
    slot_of: dict[int, int] = {}
    main_slot: dict[int, int] = {}
    sources: list[VariableInfo] = [
        VariableInfo(0, "constant_one", None, None, None)
    ]
    input_slots: dict[str, int] = {}
    signed_input_widths: dict[str, int] = {}
    signed_layouts: dict[int, SignedLayout] = {}
    signed_cmp_layouts: dict[int, SignedCmpLayout] = {}
    next_slot = 1

    def alloc(role: str, node_id: int, name: str | None,
              kind: str) -> int:
        nonlocal next_slot
        s = next_slot
        sources.append(VariableInfo(s, role, node_id, name, kind))
        next_slot += 1
        return s

    for i, node in enumerate(nodes):
        if node.kind in (_CONST, _SIGNED_CONST):
            continue  # 常量不占槽
        w = node.width
        if node.kind == _SIGNED_INPUT:
            assert w is not None and node.name is not None
            bit_slots = tuple(
                alloc("intermediate", i, node.name, "signed_bit")
                for _ in range(w)
            )
            word = alloc("input", i, node.name, "signed_word")
            slot_of[i] = word
            main_slot[i] = word
            input_slots[node.name] = word
            signed_input_widths[node.name] = w
            signed_layouts[i] = SignedLayout(i, w, bit_slots, (), word)
        elif node.kind in (_SADD, _SSUB):
            assert w is not None
            bit_slots = tuple(
                alloc("intermediate", i, None, "signed_bit") for _ in range(w)
            )
            carry_slots = tuple(
                alloc("intermediate", i, None, "signed_carry")
                for _ in range(w + 1)
            )
            word = alloc("intermediate", i, None, "signed_word")
            slot_of[i] = word
            main_slot[i] = word
            signed_layouts[i] = SignedLayout(i, w, bit_slots, carry_slots, word)
        elif node.kind in (_SLT, _SLE):
            assert w is not None
            diff_bits = tuple(
                alloc("intermediate", i, None, "signed_diff_bit")
                for _ in range(w)
            )
            borrows = tuple(
                alloc("intermediate", i, None, "signed_borrow")
                for _ in range(w + 1)
            )
            flag = alloc("intermediate", i, None, "signed_flag")
            main_slot[i] = flag
            signed_cmp_layouts[i] = SignedCmpLayout(
                i, w, node.kind, flag, diff_bits, borrows, (), ()
            )
        elif node.kind == _SEQ:
            assert w is not None
            eq_prod = tuple(
                alloc("intermediate", i, None, "signed_eq_prod")
                for _ in range(w)
            )
            eq_chain = tuple(
                alloc("intermediate", i, None, "signed_eq_chain")
                for _ in range(w)
            )
            main_slot[i] = eq_chain[-1]
            signed_cmp_layouts[i] = SignedCmpLayout(
                i, w, node.kind, eq_chain[-1], (), (), eq_prod, eq_chain
            )
        else:
            s = alloc(
                "input" if node.kind == _INPUT else "intermediate",
                i, node.name, node.kind,
            )
            slot_of[i] = s
            main_slot[i] = s
            if node.kind == _INPUT:
                assert node.name is not None
                input_slots[node.name] = s

    # -- 逐节点生成约束 ------------------------------------------------------
    #
    # 常量节点不占见证槽：在约束中把它内联为常数槽 0 上的系数。
    # 普通 const 的字值模 97；signed_const 的「字」是其二补码无符号表示
    # (value mod 2**w)，与比特槽拼出的字口径一致。
    const_value: dict[int, int] = {}
    for i, nd in enumerate(nodes):
        if nd.kind == _CONST:
            const_value[i] = nd.value % P  # type: ignore[operator]
        elif nd.kind == _SIGNED_CONST:
            w = nd.width
            assert w is not None
            const_value[i] = nd.value % (1 << w)  # type: ignore[operator]

    def lin(node_id: int) -> dict[int, int]:
        if node_id in const_value:
            return {0: const_value[node_id]}
        return {main_slot[node_id]: 1}

    def sbit(node_id: int, k: int) -> dict[int, int]:
        """有符号值节点 node_id 的第 k 位（小端）线性项。

        signed_const 的位是字面 0/1，内联在常数槽上；其余取比特见证槽。
        """

        nd = nodes[node_id]
        if nd.kind == _SIGNED_CONST:
            return {0: (nd.value >> k) & 1}  # type: ignore[operator]
        return {signed_layouts[node_id].bit_slots[k]: 1}

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

    def bool_pin(node_id: int, tag: str, slot: int, what: str) -> None:
        """发一条 b*(b-1)=0，把见证槽钉在 {0,1}。"""

        emit(node_id, tag, f"node {node_id}: {what} booleanity b*(b-1)=0",
             {slot: 1}, merge(({slot: 1}, 1), ({0: 1}, -1)), {})

    def word_terms_of_bits(bit_slots: tuple[int, ...]) -> dict[int, int]:
        return {bs: (1 << k) % P for k, bs in enumerate(bit_slots)}

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
        elif node.kind == _SIGNED_INPUT:
            lay = signed_layouts[i]
            for k, bs in enumerate(lay.bit_slots):
                bool_pin(i, "sbit_booleanity", bs,
                         f"input bit {k} (LSB=0)")
            # 字槽 = Σ 2^k·b_k (mod 97)：字槽与逐位分解互相钉住。
            emit(i, "signed_word",
                 f"signed_input node {i}: word = sum 2^k * bit_k (mod {P})",
                 {0: 1}, {lay.word_slot: 1}, word_terms_of_bits(lay.bit_slots))
        elif node.kind in (_SADD, _SSUB):
            lay = signed_layouts[i]
            w = node.width
            assert w is not None
            x, y = node.inputs
            is_add = node.kind == _SADD
            carries = lay.carry_slots
            emit(i, "signed_carry0",
                 f"node {i}: {'carry' if is_add else 'borrow'}[0] = 0",
                 {0: 1}, {carries[0]: 1}, {})
            for k in range(w):
                xk, yk = sbit(x, k), sbit(y, k)
                ck, cn = {carries[k]: 1}, {carries[k + 1]: 1}
                if is_add:
                    # 全加器：s = x + y + c - 2c'；配 s、c' 的布尔性
                    # 恰唯一确定标准进位；c_w 被丢弃即溢出回绕。
                    rel = merge((xk, 1), (yk, 1), (ck, 1), (cn, -2))
                    origin = f"node {i}: sadd bit {k} full-adder relation"
                else:
                    # 全减器：d = x - y - r + 2r'；配 d、r' 布尔性唯一确定借位。
                    rel = merge((xk, 1), (yk, -1), (ck, -1), (cn, 2))
                    origin = f"node {i}: ssub bit {k} full-subtractor relation"
                emit(i, "sadd_bit" if is_add else "ssub_bit", origin,
                     {0: 1}, {lay.bit_slots[k]: 1}, rel)
                bool_pin(i, "sbit_booleanity", lay.bit_slots[k],
                         f"result bit {k}")
                bool_pin(i, "scarry_booleanity", carries[k + 1],
                         f"{'carry' if is_add else 'borrow'} {k + 1}")
            emit(i, "signed_word",
                 f"node {i}: wrapped result word = sum 2^k * bit_k (mod {P})",
                 {0: 1}, {lay.word_slot: 1},
                 word_terms_of_bits(lay.bit_slots))
        elif node.kind in (_SLT, _SLE):
            lay = signed_cmp_layouts[i]
            w = node.width
            assert w is not None
            x, y = node.inputs
            # 有符号比较：翻转两数符号位后做 w 位无符号减法。
            # slt: u_x - u_y，结果借位 r_w=1 当且仅当有符号 x<y。
            # sle: u_y - u_x，r_w=1 当且仅当有符号 y<x，故 f = 1-r_w。
            left, right = (x, y) if node.kind == _SLT else (y, x)

            def ubit(operand: int, k: int) -> dict[int, int]:
                if k == w - 1:
                    return merge(({0: 1}, 1), (sbit(operand, k), -1))
                return sbit(operand, k)

            borrows = lay.borrows
            emit(i, "signed_borrow0", f"node {i}: borrow[0] = 0",
                 {0: 1}, {borrows[0]: 1}, {})
            for k in range(w):
                xk, yk = ubit(left, k), ubit(right, k)
                rk, rn = {borrows[k]: 1}, {borrows[k + 1]: 1}
                rel = merge((xk, 1), (yk, -1), (rk, -1), (rn, 2))
                emit(i, "signed_cmp_bit",
                     f"node {i}: sign-flipped subtraction bit {k} "
                     f"(full-subtractor)",
                     {0: 1}, {lay.diff_bits[k]: 1}, rel)
                bool_pin(i, "sbit_booleanity", lay.diff_bits[k],
                         f"diff bit {k}")
                bool_pin(i, "scarry_booleanity", borrows[k + 1],
                         f"borrow {k + 1}")
            if node.kind == _SLT:
                emit(i, "signed_flag",
                     f"node {i}: slt flag = top borrow (signed x < y)",
                     {0: 1}, {lay.flag_slot: 1}, {borrows[w]: 1})
            else:
                emit(i, "signed_flag",
                     f"node {i}: sle flag = 1 - top borrow (signed x <= y)",
                     {0: 1}, {lay.flag_slot: 1},
                     merge(({0: 1}, 1), ({borrows[w]: 1}, -1)))
            bool_pin(i, "sbit_booleanity", lay.flag_slot, "compare flag")
        elif node.kind == _SEQ:
            lay = signed_cmp_layouts[i]
            w = node.width
            assert w is not None
            x, y = node.inputs
            # 逐位同或：2·x_k·y_k = e_k - 1 + x_k + y_k（A=2x_k 为单变量，
            # 常系数 2 在 p=97 上非零；操作数为 signed_const 时 A 落在常数槽，
            # 此时两侧都是常数，约束直接不可满足当且仅当该位不相等）。
            for k in range(w):
                xk, yk = sbit(x, k), sbit(y, k)
                emit(i, "seq_prod",
                     f"node {i}: bit {k} XNOR: 2*x*y = e - 1 + x + y",
                     merge((xk, 2),), yk,
                     merge(({lay.eq_prod[k]: 1}, 1), ({0: 1}, -1),
                           (xk, 1), (yk, 1)))
                bool_pin(i, "sbit_booleanity", lay.eq_prod[k],
                         f"xnor bit {k}")
            # 与链：q_0 = e_0；q_k = q_{k-1}·e_k；标志 f = q_{w-1}。
            q = lay.eq_chain
            emit(i, "signed_pin", f"node {i}: equality chain[0] = e_0",
                 {0: 1}, {q[0]: 1}, {lay.eq_prod[0]: 1})
            for k in range(1, w):
                emit(i, "seq_chain",
                     f"node {i}: equality chain[{k}] = chain[{k-1}] * e_{k}",
                     {q[k - 1]: 1}, {lay.eq_prod[k]: 1}, {q[k]: 1})
            for k, qs in enumerate(q):
                bool_pin(i, "scarry_booleanity", qs,
                         f"equality chain {k}")

    return CompiledCircuit(
        p=P,
        n_vars=next_slot,
        constraints=tuple(constraints),
        sources=tuple(sources),
        inputs=dict(input_slots),
        nodes=nodes,
        signed_inputs=signed_input_widths,
        signed_layouts=signed_layouts,
        signed_cmp_layouts=signed_cmp_layouts,
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


def _parse_signed_input(raw: object, name: str, width: int) -> int:
    """有符号输入的严格取值：有限 int 且落在 w 位区间内。

    与普通域输入不同，这里**不做模 97 规约、也不回绕**：回绕只是运算溢出
    策略，非法输入（越界）抛 SignedInputError；类型非法沿用全局契约：
    bool/普通 float -> TypeError，NaN/Infinity -> ValueError。
    """

    low, high = signed_range(width)
    if isinstance(raw, bool):
        raise TypeError(
            f"signed input {name!r} must be int, got bool "
            f"(booleans are not accepted)"
        )
    if isinstance(raw, float):
        if math.isnan(raw):
            raise ValueError(f"signed input {name!r} must be finite int, got NaN")
        if math.isinf(raw):
            raise ValueError(
                f"signed input {name!r} must be finite int, got Infinity"
            )
        raise TypeError(
            f"signed input {name!r} must be int, got float {raw!r}"
        )
    if not isinstance(raw, int):
        raise TypeError(
            f"signed input {name!r} must be int, got {type(raw).__name__}"
        )
    if not (low <= raw <= high):
        raise SignedInputError(name, width, raw, kind="range")
    return raw


def generate_witness(compiled: CompiledCircuit,
                      user_inputs: Mapping[str, object]) -> list[int]:
    """根据命名输入生成完整见证向量 z（z[0]=1）。

    失败语义（均在返回前抛出，绝不返回部分见证）:
      - 多余/未声明输入名，或输入名不是 str: UnexpectedInputError / TypeError
      - 缺失输入: UnknownInputError（确定无解；本库无搜索，故不存在预算耗尽）
      - 普通输入值非 int 有限标量: TypeError/ValueError
      - 有符号输入越界或类型非法: SignedInputError
      - select 选择位非布尔: NonBooleanSelectError
      - assert_equal 不成立: AssertEqualError

    中间槽（含有符号节点的逐位/进位槽）全部由本函数按 DAG 重新计算，
    调用方无法通过 user_inputs 覆盖。
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
    # 旧语义：每个节点的主域值（有符号值节点取其二补码字 mod 97，
    # 比较节点取 0/1 标志），供旧 add/mul/select/assert 引用。
    vals: dict[int, int] = {}
    # 有符号值节点的真实 Python 有符号整数（在 w 位区间内）。
    svals: dict[int, int] = {}

    # 节点 -> 主见证槽（每个节点唯一；逐位/进位槽不算主槽）。
    main_slot_of: dict[int, int] = {}
    for nd_id, lay in compiled.signed_layouts.items():
        main_slot_of[nd_id] = lay.word_slot
    for nd_id, lay in compiled.signed_cmp_layouts.items():
        main_slot_of[nd_id] = lay.flag_slot
    for info in compiled.sources:
        if info.node is not None and info.kind in (
            "signed_bit", "signed_carry", "signed_diff_bit", "signed_borrow",
            "signed_eq_prod", "signed_eq_chain",
        ):
            continue
        if info.node is not None and info.node not in main_slot_of:
            main_slot_of[info.node] = info.slot

    # 先做输入取值与缺失检查，保证进入逐节点计算前所有外部值已确定。
    field_input_values: dict[str, int] = {}
    signed_input_values: dict[str, int] = {}
    for name in compiled.inputs:
        if name not in mapping:
            raise UnknownInputError(name)
        if name in compiled.signed_inputs:
            signed_input_values[name] = _parse_signed_input(
                mapping[name], name, compiled.signed_inputs[name]
            )
        else:
            field_input_values[name] = parse_scalar(
                mapping[name], what=f"input {name!r}"
            )

    def fill_word_of_signed(nd_id: int, svalue: int) -> None:
        """把有符号值节点的比特槽与字槽写入见证。"""

        w = compiled.nodes[nd_id].width
        assert w is not None
        lay = compiled.signed_layouts[nd_id]
        bits = signed_to_bits(svalue, w)
        for k, bs in enumerate(lay.bit_slots):
            z[bs] = bits[k]
        unsigned = sum(b << k for k, b in enumerate(bits))
        z[lay.word_slot] = unsigned % P
        svals[nd_id] = svalue
        vals[nd_id] = unsigned % P

    for i, node in enumerate(compiled.nodes):
        if node.kind == _CONST:
            vals[i] = node.value % P  # type: ignore[operator]
            continue
        if node.kind == _SIGNED_CONST:
            w = node.width
            assert w is not None
            unsigned = node.value % (1 << w)  # type: ignore[operator]
            vals[i] = unsigned % P
            svals[i] = node.value  # type: ignore[assignment]
            continue

        slot = main_slot_of[i]

        if node.kind == _INPUT:
            v = field_input_values[node.name]  # type: ignore[index]
            z[slot] = v
            vals[i] = v
        elif node.kind == _SIGNED_INPUT:
            fill_word_of_signed(
                i, signed_input_values[node.name]  # type: ignore[index]
            )
        elif node.kind == _ADD:
            x, y = node.inputs
            v = (vals[x] + vals[y]) % P
            z[slot] = v
            vals[i] = v
        elif node.kind == _MUL:
            x, y = node.inputs
            v = (vals[x] * vals[y]) % P
            z[slot] = v
            vals[i] = v
        elif node.kind == _SELECT:
            b, x, y = node.inputs
            bv, xv, yv = vals[b], vals[x], vals[y]
            if bv not in (0, 1):
                raise NonBooleanSelectError(i, bv)
            v = (bv * xv + (1 - bv) * yv) % P
            z[slot] = v
            vals[i] = v
        elif node.kind == _ASSERT:
            x, y = node.inputs
            if vals[x] != vals[y]:
                raise AssertEqualError(i, vals[x], vals[y])
            v = vals[x]
            z[slot] = v
            vals[i] = v
        elif node.kind in (_SADD, _SSUB):
            w = node.width
            assert w is not None
            x, y = node.inputs
            ax, ay = svals[x], svals[y]
            if node.kind == _SADD:
                r = (ax + ay + (1 << (w - 1))) % (1 << w) - (1 << (w - 1))
            else:
                r = (ax - ay + (1 << (w - 1))) % (1 << w) - (1 << (w - 1))
            fill_word_of_signed(i, r)
            # 填充进位/借位辅助槽。
            lay = compiled.signed_layouts[i]
            bx = signed_to_bits(ax, w)
            by = signed_to_bits(ay, w)
            br = signed_to_bits(r, w)
            carries = lay.carry_slots
            z[carries[0]] = 0
            if node.kind == _SADD:
                c = 0
                for k in range(w):
                    total = bx[k] + by[k] + c
                    assert br[k] == total % 2
                    c = total // 2
                    z[carries[k + 1]] = c
            else:
                rr = 0
                for k in range(w):
                    diff = bx[k] - by[k] - rr
                    assert br[k] == diff % 2
                    rr = 1 if diff < 0 else 0
                    z[carries[k + 1]] = rr
        elif node.kind in (_SLT, _SLE):
            w = node.width
            assert w is not None
            x, y = node.inputs
            ax, ay = svals[x], svals[y]
            bias = 1 << (w - 1)
            ux = (ax + bias) % (1 << w)  # 符号位翻转后的无符号值
            uy = (ay + bias) % (1 << w)
            lay = compiled.signed_cmp_layouts[i]
            if node.kind == _SLT:
                flag = 1 if ax < ay else 0
                left_u, right_u = ux, uy
            else:
                flag = 1 if ax <= ay else 0
                left_u, right_u = uy, ux
            z[lay.flag_slot] = flag
            # 差值比特与借位：对翻转后的无符号值做 w 位减法。
            bl = tuple((left_u >> k) & 1 for k in range(w))
            brt = tuple((right_u >> k) & 1 for k in range(w))
            z[lay.borrows[0]] = 0
            rr = 0
            for k in range(w):
                d = bl[k] - brt[k] - rr
                z[lay.diff_bits[k]] = d % 2
                rr = 1 if d < 0 else 0
                z[lay.borrows[k + 1]] = rr
            vals[i] = flag
        elif node.kind == _SEQ:
            w = node.width
            assert w is not None
            x, y = node.inputs
            ax, ay = svals[x], svals[y]
            lay = compiled.signed_cmp_layouts[i]
            bx = signed_to_bits(ax, w)
            by = signed_to_bits(ay, w)
            qv = 1
            for k in range(w):
                e = 1 if bx[k] == by[k] else 0
                z[lay.eq_prod[k]] = e
                qv &= e
                z[lay.eq_chain[k]] = qv
            assert qv == (1 if ax == ay else 0)
            z[lay.flag_slot] = qv
            vals[i] = qv

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
