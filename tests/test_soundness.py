"""穷举式健全性（确定性，无随机源）。

R1CS 约束规定的是变量*关系*，不保证每个输入都可由见证唯一反推：
例如 x*x 对 x 与 -x 不可区分，b=0 的 select 不约束未选分支。
这是标准语义，在 README「已知限制」中说明。因此本测试区分：

1. 中间槽（intermediate）：每个中间节点恰有一条「定义约束」，其输出以
   系数 1 单独出现。固定其他槽后，中间槽有唯一合法值——对全部 96 个
   错误值逐一替换，审计必须报告失败（这正是「修改中间值必被定位」）。
2. 输入槽（input）：仅在可注入上下文中做穷举（v3 中输出含 3*x+4，
   乘的是非零常数 3，x 与输出一一对应）；其余电路只做独立解释器对照。
"""

import unittest

from zkcirc import (
    P,
    Circuit,
    compile_circuit,
    generate_witness,
    audit,
)

try:  # pragma: no cover
    from .reference import reference_eval
except ImportError:  # pragma: no cover
    from reference import reference_eval


# ---------------------------------------------------------------------------
# 三个确定性电路；独立规格用朴素 dict 另行手写，索引一一对应。
# ---------------------------------------------------------------------------

def build_shared_add():
    """s=x+y 被多处共享；断言 (x+y)^2 == x^2+2xy+y^2（域内恒等式）。"""

    c = Circuit()
    x, y = c.input("x"), c.input("y")
    s = c.add(x, y)
    lhs = c.mul(s, s)
    x2 = c.mul(x, x)
    y2 = c.mul(y, y)
    xy = c.mul(x, y)
    two_xy = c.mul(c.const(2), xy)
    rhs = c.add(c.add(x2, two_xy), y2)
    a = c.assert_equal(lhs, rhs)
    spec = [
        {"kind": "input", "name": "x"},                       # 0
        {"kind": "input", "name": "y"},                       # 1
        {"kind": "add", "inputs": (0, 1)},                    # 2 s
        {"kind": "mul", "inputs": (2, 2)},                    # 3 lhs
        {"kind": "mul", "inputs": (0, 0)},                    # 4 x2
        {"kind": "mul", "inputs": (1, 1)},                    # 5 y2
        {"kind": "mul", "inputs": (0, 1)},                    # 6 xy
        {"kind": "const", "value": 2},                        # 7
        {"kind": "mul", "inputs": (7, 6)},                    # 8 2xy
        {"kind": "add", "inputs": (4, 8)},                    # 9
        {"kind": "add", "inputs": (9, 5)},                    # 10 rhs
        {"kind": "assert_equal", "inputs": (3, 10)},          # 11
    ]
    return c, spec, a


def build_select_chain():
    """sel=b?x*x:y+1；用独立的算术展开断言 sel==b*x*x+(1-b)*(y+1)。"""

    c = Circuit()
    b, x, y = c.input("b"), c.input("x"), c.input("y")
    t = c.mul(x, x)
    u = c.add(y, c.const(1))
    sel = c.select(b, t, u)
    # (1-b)
    one_minus_b = c.add(c.const(1), c.mul(c.const(-1), b))
    r0 = c.mul(b, t)
    r1 = c.mul(one_minus_b, u)
    rhs = c.add(r0, r1)
    a = c.assert_equal(sel, rhs)
    spec = [
        {"kind": "input", "name": "b"},                       # 0
        {"kind": "input", "name": "x"},                       # 1
        {"kind": "input", "name": "y"},                       # 2
        {"kind": "mul", "inputs": (1, 1)},                    # 3 t
        {"kind": "const", "value": 1},                        # 4
        {"kind": "add", "inputs": (2, 4)},                    # 5 u
        {"kind": "select", "inputs": (0, 3, 5)},              # 6 sel
        {"kind": "const", "value": 1},                        # 7
        {"kind": "const", "value": -1},                       # 8
        {"kind": "mul", "inputs": (8, 0)},                    # 9 -b
        {"kind": "add", "inputs": (7, 9)},                    # 10 1-b
        {"kind": "mul", "inputs": (0, 3)},                    # 11 b*t
        {"kind": "mul", "inputs": (10, 5)},                   # 12 (1-b)u
        {"kind": "add", "inputs": (11, 12)},                  # 13 rhs
        {"kind": "assert_equal", "inputs": (6, 13)},          # 14
    ]
    return c, spec, a


def build_const_inline():
    """常量内联：out = (3*x+4)*2，全程乘非零常数，x 可由输出唯一反推。"""

    c = Circuit()
    x = c.input("x")
    a1 = c.mul(c.const(3), x)
    a = c.add(a1, c.const(4))
    out = c.mul(a, c.const(2))
    eq = c.assert_equal(out, out)  # 输出自等：给出 assert_value 定位锚点
    spec = [
        {"kind": "input", "name": "x"},                       # 0
        {"kind": "const", "value": 3},                        # 1
        {"kind": "mul", "inputs": (1, 0)},                    # 2 a1
        {"kind": "const", "value": 4},                        # 3
        {"kind": "add", "inputs": (2, 3)},                    # 4 a
        {"kind": "const", "value": 2},                        # 5
        {"kind": "mul", "inputs": (4, 5)},                    # 6 out
        {"kind": "assert_equal", "inputs": (6, 6)},           # 7
    ]
    return c, spec, eq


GRID = (0, 1, 2, 48, 96)


class TestExhaustiveSoundness(unittest.TestCase):
    def _feeds(self, names):
        if list(names) == ["x", "y"]:
            return [{"x": a, "y": b} for a in GRID for b in GRID]
        if list(names) == ["b", "x", "y"]:
            return [
                {"b": bb, "x": a, "y": d}
                for bb in (0, 1) for a in GRID for d in GRID
            ]
        return [{names[0]: v} for v in GRID]

    def test_reference_match(self):
        for name, builder in (("shared_add", build_shared_add),
                              ("select_chain", build_select_chain),
                              ("const_inline", build_const_inline)):
            with self.subTest(circuit=name):
                c, spec, _ = builder()
                cc = compile_circuit(c)
                for feeds in self._feeds(tuple(cc.inputs)):
                    z = generate_witness(cc, feeds)
                    self.assertEqual(z[0], 1)
                    self.assertTrue(all(0 <= v < P for v in z))
                    report = audit(cc, z)
                    self.assertTrue(report.ok, msg=[
                        (r.index, r.tag, r.lhs, r.rhs)
                        for r in report.results if not r.satisfied
                    ])
                    expected = reference_eval(spec, feeds)
                    for node_id, ev in enumerate(expected):
                        info = next(
                            (s for s in cc.sources if s.node == node_id), None
                        )
                        if info is None:
                            self.assertEqual(cc.nodes[node_id].kind, "const")
                        else:
                            self.assertEqual(z[info.slot], ev)

    def test_intermediate_slot_tamper_always_caught(self):
        for name, builder in (("shared_add", build_shared_add),
                              ("select_chain", build_select_chain),
                              ("const_inline", build_const_inline)):
            with self.subTest(circuit=name):
                c, _, _ = builder()
                cc = compile_circuit(c)
                for feeds in self._feeds(tuple(cc.inputs)):
                    z = generate_witness(cc, feeds)
                    for info in cc.sources:
                        if info.role != "intermediate":
                            continue
                        good = z[info.slot]
                        for wrong in range(P):
                            if wrong == good:
                                continue
                            zz = z.copy()
                            zz[info.slot] = wrong
                            report = audit(cc, zz)
                            self.assertFalse(
                                report.ok,
                                msg=(f"{name} feeds={feeds} slot={info.slot} "
                                     f"node={info.node} wrong={wrong} accepted"),
                            )
                            # 定义该槽的节点必须出现在失败定位中。
                            self.assertIn(info.node,
                                          {f.node for f in report.failures})

    def test_input_slot_injective_circuit_pinned(self):
        # const_inline 中 3*x+4 对 x 是置换（3 可逆）：改 x 必失败。
        c, _, _ = build_const_inline()
        cc = compile_circuit(c)
        x_slot = cc.inputs["x"]
        for feeds in ({"x": v} for v in GRID):
            z = generate_witness(cc, feeds)
            for wrong in range(P):
                if wrong == z[x_slot]:
                    continue
                zz = z.copy()
                zz[x_slot] = wrong
                self.assertFalse(audit(cc, zz).ok,
                                 msg=f"x={feeds['x']} tampered to {wrong}")

    def test_non_injective_input_is_known_limitation(self):
        # x*x 电路：x 与 -x 产生同一见证的其余部分——关系约束而非唯一见证。
        c = Circuit()
        x = c.input("x")
        m = c.mul(x, x)
        cc = compile_circuit(c)
        z = generate_witness(cc, {"x": 10})
        zz = z.copy()
        zz[cc.inputs["x"]] = (-10) % P
        # x 与 -x 都满足 m=x*x；中间槽 m 未被篡改，仍然合法。
        self.assertTrue(audit(cc, zz).ok)
        # 但篡改中间槽 m 必然失败。
        m_slot = next(s.slot for s in cc.sources if s.node == m)
        zz[m_slot] = (z[m_slot] + 1) % P
        self.assertFalse(audit(cc, zz).ok)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
