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
