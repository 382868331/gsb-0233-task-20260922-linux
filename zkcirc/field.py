"""模 p=97 素数域的最小工具。

契约要点:
- 域元素一律用 0..p-1 的 Python ``int`` 表示；不存在浮点域元素。
- 标量入参只接受 int，且明确拒绝 bool（``True`` 在 Python 中也是 int，
  但按题目契约整数参数必须拒绝 bool）。
- 拒绝 float NaN / Infinity（即便它们根本不会被接受为标量，也要给出
  明确的、可定位的错误，而不是隐式转 int）。
"""

from __future__ import annotations

import math

P = 97


def parse_scalar(value: object, *, what: str = "scalar") -> int:
    """把外部传入的标量规约为 0..p-1 的域元素。

    - bool（含 True/False）一律拒绝，即使它是 int 的子类型。
    - int：按模 p 规约，允许负数（负值有确定的数学含义，不算错误）。
    - float：仅当它是有限数时拒绝并提示需要 int；NaN / +Inf / -Inf
      单独点名，满足「拒绝 NaN/Infinity」的契约。
    - 其他类型拒绝。

    ``what`` 用于错误信息定位（例如 "const value" / "input 'x'"）。
    """

    if isinstance(value, bool):
        raise TypeError(f"{what} must be int, got bool (booleans are not accepted)")
    if isinstance(value, int):
        return value % P
    if isinstance(value, float):
        if math.isnan(value):
            raise ValueError(f"{what} must be finite int, got NaN")
        if math.isinf(value):
            raise ValueError(f"{what} must be finite int, got Infinity")
        raise TypeError(
            f"{what} must be int (field arithmetic is exact, no floats); "
            f"got float {value!r}"
        )
    raise TypeError(f"{what} must be int, got {type(value).__name__}")


def fadd(a: int, b: int) -> int:
    return (a + b) % P


def fmul(a: int, b: int) -> int:
    return (a * b) % P


def fsub(a: int, b: int) -> int:
    return (a - b) % P


def finv(a: int) -> int:
    """模逆（本模块目前仅测试/工具用途；a=0 抛 ZeroDivisionError）。"""

    if a == 0:
        raise ZeroDivisionError("no modular inverse of 0")
    return pow(a, P - 2, P)


# ---------------------------------------------------------------------------
# 2..8 位有符号整数（二补码）工具
# ---------------------------------------------------------------------------
#
# 本库支持的有符号整数位宽闭区间。p=97 足以无损容纳 w 位运算所需的全部
# 整数：无符号值最大 2**8-1=255 会超过 96，但所有约束只使用「单比特
# 0/1 与进位比特」，见证里从不存放整个无符号字；二补码数值本身落在
# [-128,127]，进入域时按模 97 规约（仅用于展示/与旧域电路互通）。

MIN_SIGNED_WIDTH = 2
MAX_SIGNED_WIDTH = 8


def check_width(width: object) -> int:
    """校验有符号位宽：必须是 int（拒绝 bool）且在 2..8。"""

    if isinstance(width, bool) or not isinstance(width, int):
        raise TypeError(
            f"signed width must be int, got {type(width).__name__}"
        )
    if not (MIN_SIGNED_WIDTH <= width <= MAX_SIGNED_WIDTH):
        raise ValueError(
            f"signed width must be in [{MIN_SIGNED_WIDTH}, "
            f"{MAX_SIGNED_WIDTH}], got {width}"
        )
    return width


def signed_range(width: int) -> tuple[int, int]:
    """返回 w 位有符号整数的合法闭区间 (-2**(w-1), 2**(w-1)-1)。"""

    w = check_width(width)
    return (-(1 << (w - 1)), (1 << (w - 1)) - 1)


def wrap_signed(value: int, width: int) -> int:
    """把任意 Python int 按 w 位二补码回绕到合法区间（溢出策略：仅回绕）。"""

    w = check_width(width)
    mask = 1 << w
    return ((value + (1 << (w - 1))) % mask) - (1 << (w - 1))


def signed_to_bits(value: int, width: int) -> tuple[int, ...]:
    """合法 w 位有符号整数 -> 小端比特元组（b[0] 为 LSB，元素为 0/1 int）。"""

    w = check_width(width)
    low, high = signed_range(w)
    if not (low <= value <= high):
        raise ValueError(
            f"signed value {value} out of range [{low}, {high}] for width {w}"
        )
    return tuple((value >> i) & 1 for i in range(w))


def bits_to_signed(bits: tuple[int, ...], width: int) -> int:
    """小端比特元组 -> w 位有符号整数（最高位按符号位解释）。"""

    w = check_width(width)
    if len(bits) != w or any(b not in (0, 1) for b in bits):
        raise ValueError(f"expected {w} bits of 0/1, got {bits!r}")
    unsigned = sum(b << i for i, b in enumerate(bits))
    return unsigned - (bits[w - 1] << w)
