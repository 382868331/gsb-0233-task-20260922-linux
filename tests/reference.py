"""独立参考：直接在模 97 整数域上解释表达式 DAG。

本模块刻意**不导入 zkcirc 被测核心**：它只接受朴素的节点规格
``list[dict]``（键：kind / value / name / inputs），用最直白的模运算
逐节点求值，为测试提供独立期望值。它也独立实现了稀疏 R1CS 点积校验，
仅用作往返一致性的补充检查。
"""

from __future__ import annotations

from typing import Mapping, Sequence

P = 97


def _norm(v: int) -> int:
    return v % P


def reference_eval(spec: Sequence[Mapping[str, object]],
                   inputs: Mapping[str, int]) -> list[int]:
    """按节点下标顺序直接求值，返回每个节点的域值。

    - select 的 b 必须为 0/1，否则 ValueError（独立复现契约）。
    - assert_equal 两侧不等则 ValueError，否则输出取左侧。
    """

    values: list[int] = []
    supplied: dict[str, int] = {k: _norm(v) for k, v in inputs.items()}
    for i, node in enumerate(spec):
        kind = node["kind"]
        kids = node.get("inputs", ())
        if kind == "const":
            values.append(_norm(node["value"]))
        elif kind == "input":
            if node["name"] not in supplied:
                raise ValueError(f"missing input {node['name']!r}")
            values.append(supplied[node["name"]])
        elif kind == "add":
            values.append(_norm(values[kids[0]] + values[kids[1]]))
        elif kind == "mul":
            values.append(_norm(values[kids[0]] * values[kids[1]]))
        elif kind == "select":
            b, x, y = kids
            bv = values[b]
            if bv not in (0, 1):
                raise ValueError(f"non-boolean selector at node {i}: {bv}")
            values.append(_norm(bv * values[x] + (1 - bv) * values[y]))
        elif kind == "assert_equal":
            x, y = kids
            if values[x] != values[y]:
                raise ValueError(
                    f"assert_equal at node {i}: {values[x]} != {values[y]}"
                )
            values.append(values[x])
        else:
            raise ValueError(f"unknown kind {kind!r} at node {i}")
    return values


def reference_check_constraint(a: Sequence[tuple[int, int]],
                               b: Sequence[tuple[int, int]],
                               c: Sequence[tuple[int, int]],
                               z: Sequence[int]) -> tuple[bool, int, int]:
    """独立点积实现：返回 (是否满足, 左侧, 右侧)，全部纯整数模运算。"""

    def dot(terms: Sequence[tuple[int, int]]) -> int:
        acc = 0
        for slot, coeff in terms:
            acc += coeff * z[slot]
        return acc % P

    left = (dot(a) * dot(b)) % P
    right = dot(c)
    return left == right, left, right


# ---------------------------------------------------------------------------
# 2..8 位有符号整数（二补码）独立参考
# ---------------------------------------------------------------------------
#
# 与被测核心完全独立的朴素实现：只用 Python 整数按位运算与区间检查，
# 逐节点维护「有符号整数 + 小端比特 + 标准进位/借位序列」，供测试核对
# 见证中的每个槽（含辅助槽），而不只是最终结果。

_SIGNED_KINDS = {
    "signed_input", "signed_const", "sadd", "ssub",
    "slt", "sle", "seq",
}


def ref_signed_wrap(value: int, width: int) -> int:
    """二补码回绕到 w 位有符号区间。"""

    bias = 1 << (width - 1)
    return ((value + bias) % (1 << width)) - bias


def ref_signed_bits(value: int, width: int) -> tuple[int, ...]:
    """合法 w 位有符号整数的小端比特。"""

    low = -(1 << (width - 1))
    high = (1 << (width - 1)) - 1
    if not (low <= value <= high):
        raise ValueError(f"reference: value {value} out of {width}-bit range")
    return tuple((value >> i) & 1 for i in range(width))


def ref_eval_signed(spec: Sequence[Mapping[str, object]],
                    inputs: Mapping[str, int]) -> list[dict]:
    """朴素解释有符号节点规格，返回每节点的独立计算明细。

    每个元素为 dict:
      value: 有符号整数（比较节点为 0/1 标志）
      bits:  小端比特（值节点）；比较节点为 ()
      carries: 标准加法进位 c_0..c_w（含 c_0=0）；非 sadd 为 ()
      borrows: 标准减法借位 r_0..r_w（含 r_0=0）；非 ssub/slt/sle 为 ()
      diff_bits: 比较减法（符号位翻转后）的差值比特；slt/sle 专用
      xnor/chain: seq 的逐位同或与与链

    - signed_input 越界/类型问题由 ValueError 独立复现。
    - 宽度不一致、操作数不是有符号值节点均 ValueError。
    """

    out: list[dict] = []
    supplied: dict[str, int] = dict(inputs)
    for i, node in enumerate(spec):
        kind = node["kind"]
        width = node.get("width")
        kids = node.get("inputs", ())
        if kind == "signed_input":
            if node["name"] not in supplied:
                raise ValueError(f"missing signed input {node['name']!r}")
            v = supplied[node["name"]]
            if not isinstance(v, int) or isinstance(v, bool):
                raise ValueError(f"signed input {node['name']!r} not a plain int")
            low = -(1 << (width - 1))
            high = (1 << (width - 1)) - 1
            if not (low <= v <= high):
                raise ValueError(f"signed input {node['name']!r} out of range")
            out.append({"value": v, "bits": ref_signed_bits(v, width),
                        "carries": (), "borrows": (), "diff_bits": (),
                        "xnor": (), "chain": ()})
        elif kind == "signed_const":
            v = node["value"]
            low = -(1 << (width - 1))
            high = (1 << (width - 1)) - 1
            if not (low <= v <= high):
                raise ValueError("signed const out of range")
            out.append({"value": v, "bits": ref_signed_bits(v, width),
                        "carries": (), "borrows": (), "diff_bits": (),
                        "xnor": (), "chain": ()})
        elif kind in ("sadd", "ssub"):
            ax, ay = out[kids[0]]["value"], out[kids[1]]["value"]
            if spec[kids[0]]["width"] != width or spec[kids[1]]["width"] != width:
                raise ValueError("width mismatch")
            raw = ax + ay if kind == "sadd" else ax - ay
            v = ref_signed_wrap(raw, width)
            bx, by = (ref_signed_bits(ax, width),
                      ref_signed_bits(ay, width))
            br = ref_signed_bits(v, width)
            carries: list[int] = [0]
            borrows: list[int] = [0]
            cin = 0
            for k in range(width):
                if kind == "sadd":
                    total = bx[k] + by[k] + cin
                    assert br[k] == total % 2
                    cin = total // 2
                    carries.append(cin)
                else:
                    diff = bx[k] - by[k] - cin
                    assert br[k] == diff % 2
                    cin = 1 if diff < 0 else 0
                    borrows.append(cin)
            out.append({
                "value": v, "bits": br,
                "carries": tuple(carries) if kind == "sadd" else (),
                "borrows": tuple(borrows) if kind == "ssub" else (),
                "diff_bits": (), "xnor": (), "chain": (),
            })
        elif kind in ("slt", "sle"):
            ax, ay = out[kids[0]]["value"], out[kids[1]]["value"]
            flag = 1 if (ax < ay if kind == "slt" else ax <= ay) else 0
            bias = 1 << (width - 1)
            if kind == "slt":
                ux, uy = (ax + bias) % (1 << width), (ay + bias) % (1 << width)
            else:
                ux, uy = (ay + bias) % (1 << width), (ax + bias) % (1 << width)
            bl = tuple((ux >> k) & 1 for k in range(width))
            brt = tuple((uy >> k) & 1 for k in range(width))
            diff_bits: list[int] = []
            borrows = [0]
            rr = 0
            for k in range(width):
                d = bl[k] - brt[k] - rr
                diff_bits.append(d % 2)
                rr = 1 if d < 0 else 0
                borrows.append(rr)
            assert flag == (1 if (kind == "slt" and borrows[-1] == 1 or
                                  kind == "sle" and borrows[-1] == 0) else 0)
            out.append({"value": flag, "bits": (), "carries": (),
                        "borrows": tuple(borrows),
                        "diff_bits": tuple(diff_bits),
                        "xnor": (), "chain": ()})
        elif kind == "seq":
            ax, ay = out[kids[0]]["value"], out[kids[1]]["value"]
            bx, by = (ref_signed_bits(ax, width),
                      ref_signed_bits(ay, width))
            xnor = tuple(1 if bx[k] == by[k] else 0 for k in range(width))
            chain: list[int] = []
            q = 1
            for e in xnor:
                q *= e
                chain.append(q)
            out.append({"value": 1 if ax == ay else 0, "bits": (),
                        "carries": (), "borrows": (), "diff_bits": (),
                        "xnor": xnor, "chain": tuple(chain)})
        else:
            raise ValueError(f"unknown signed kind {kind!r} at node {i}")
    return out
