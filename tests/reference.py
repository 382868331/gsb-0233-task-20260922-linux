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
        elif kind == "lookup":
            (vr,) = kids
            table = tuple(node["table"])
            vv = values[vr]
            if vv not in table:
                raise ValueError(
                    f"lookup at node {i}: value {vv} not in table {list(table)}"
                )
            values.append(vv)
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
