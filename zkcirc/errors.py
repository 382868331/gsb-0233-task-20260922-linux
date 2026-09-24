"""zkcirc 的错误类型层次。

所有错误都带可定位信息（节点索引 / 约束索引 / 输入名 / 槽位索引），
绝不静默纠正非法输入。
"""

from __future__ import annotations


class ZkCircError(Exception):
    """本库所有异常的基类。"""


class CircuitBuildError(ZkCircError):
    """构造表达式 DAG 时的非法操作（节点参数/引用非法等）。"""

    def __init__(self, message: str, *, node: int | None = None):
        super().__init__(message)
        self.node = node

    def __str__(self) -> str:  # pragma: no cover - 简单拼接
        if self.node is not None:
            return f"[node {self.node}] {super().__str__()}"
        return super().__str__()


class CircuitLimitError(CircuitBuildError):
    """超过公开接口上限（节点数 > 200）。

    这是确定的「不可能满足」类拒绝，与任何运行期预算无关。
    """


class CompileError(ZkCircError):
    """DAG -> R1CS 编译失败（结构不合法）。"""


class WitnessError(ZkCircError):
    """见证生成失败的基类（见各子类）。"""


class NonBooleanSelectError(WitnessError):
    """select 的选择位 b 在域内不是 0 或 1。

    属性:
        node: 触发问题的 select 节点索引。
        b: 实际域值（0..p-1 的 int）。
    """

    def __init__(self, node: int, b: int):
        super().__init__(
            f"select node {node} selector is non-boolean: b={b} (field p=97, "
            f"only 0/1 allowed)"
        )
        self.node = node
        self.b = b


class AssertEqualError(WitnessError):
    """assert_equal 节点两侧值不相等。

    属性:
        node: assert_equal 节点索引。
        left, right: 两侧实际域值。
    """

    def __init__(self, node: int, left: int, right: int):
        super().__init__(
            f"assert_equal node {node} failed: {left} != {right} (mod 97)"
        )
        self.node = node
        self.left = left
        self.right = right


class UnknownInputError(WitnessError):
    """命名输入缺失（无解），区分于「预算耗尽」。

    本库不存在搜索过程，故没有独立的预算耗尽异常；输入缺失即确定无解。
    """

    def __init__(self, name: str):
        super().__init__(f"unknown or missing named input: {name!r}")
        self.name = name


class UnexpectedInputError(WitnessError):
    """调用方提供了电路未声明的输入，或试图覆盖非输入槽。"""

    def __init__(self, name: str, *, reason: str = "not declared by circuit"):
        super().__init__(f"input {name!r} {reason}")
        self.name = name
        self.reason = reason


class SignedInputError(WitnessError):
    """有符号整数输入不在其位宽允许的范围内（含类型非法：bool/float 等）。

    属性:
        name: 输入名。
        width: 有符号位宽（2..8）。
        low, high: 该位宽的合法闭区间 [-2**(w-1), 2**(w-1)-1]。
        value: 触发问题的值（int 越界时为实际 int；类型错误时可能为任意对象）。
        kind: "range" | "type"，区分越界与类型非法。
    """

    def __init__(self, name: str, width: int, value: object, *,
                 kind: str = "range"):
        low = -(1 << (width - 1))
        high = (1 << (width - 1)) - 1
        if kind == "range":
            msg = (f"signed input {name!r} (width {width}) must be an int in "
                   f"[{low}, {high}] (two's complement, wrap-around only), "
                   f"got {value!r}")
        else:
            msg = (f"signed input {name!r} (width {width}) must be a finite "
                   f"int in [{low}, {high}], got {type(value).__name__}")
        super().__init__(msg)
        self.name = name
        self.width = width
        self.low = low
        self.high = high
        self.value = value
        self.kind = kind


class AuditError(ZkCircError):
    """对见证做审计时，见证向量形状不合法（长度不符/含越界值）。"""
