"""编译/见证/审计的核心测试。

期望值来自 tests.reference 中独立编写的朴素域解释器（不导入 zkcirc）；
reference_check_constraint 的独立点积仅作往返一致性补充。
"""

import math
import unittest

from zkcirc import (
    P,
    Circuit,
    compile_circuit,
    generate_witness,
    audit,
    NonBooleanSelectError,
    AssertEqualError,
    UnknownInputError,
    UnexpectedInputError,
    AuditError,
)

# discover -s tests 会把 tests/ 放到 sys.path 上以裸模块名导入，
# 作为包导入时则使用相对导入；两种方式都要能工作。
try:  # pragma: no cover - 取决于 unittest 的发现方式
    from .reference import reference_eval, reference_check_constraint
except ImportError:  # pragma: no cover
    from reference import reference_eval, reference_check_constraint


# ---------------------------------------------------------------------------
# 确定性夹具：电路与独立规格分别手工构建，索引在两个世界中保持一一对应。
#
#   0: input x
#   1: input y
#   2: input b
#   3: add  s = x + y            （共享子表达式，被节点 4 与节点 7 复用）
#   4: mul  t = s * s
#   5: const 2
#   6: select out_sel = b ? t : 2
#   7: mul  out = out_sel * s
#
# 独立参考规格（朴素 dict，不经过 zkcirc）：
POLY_SPEC = [
    {"kind": "input", "name": "x"},
    {"kind": "input", "name": "y"},
    {"kind": "input", "name": "b"},
    {"kind": "add", "inputs": (0, 1)},
    {"kind": "mul", "inputs": (3, 3)},
    {"kind": "const", "value": 2},
    {"kind": "select", "inputs": (2, 4, 5)},
    {"kind": "mul", "inputs": (6, 3)},
]


def build_poly_circuit() -> Circuit:
    c = Circuit()
    x = c.input("x")
    y = c.input("y")
    b = c.input("b")
    s = c.add(x, y)
    t = c.mul(s, s)
    k = c.const(2)
    sel = c.select(b, t, k)
    out = c.mul(sel, s)
    assert (x, y, b, s, t, k, sel, out) == (0, 1, 2, 3, 4, 5, 6, 7)
    return c


class TestAgainstIndependentReference(unittest.TestCase):
    def test_witness_matches_reference_for_many_inputs(self):
        c = build_poly_circuit()
        cc = compile_circuit(c)
        slot_of = {info.node: info.slot for info in cc.sources
                   if info.node is not None and info.kind != "select_aux"}

        # 确定性取值网格（不使用随机源）。
        for x in range(0, 20, 5):
            for y in (0, 1, 33, 96, -10):
                for b in (0, 1):
                    feeds = {"x": x, "y": y, "b": b}
                    expected = reference_eval(POLY_SPEC, feeds)
                    z = generate_witness(cc, feeds)

                    # 每个非常量节点的见证槽必须等于独立解释器结果。
                    for node_id, ev in enumerate(expected):
                        if cc.nodes[node_id].kind == "const":
                            continue
                        self.assertEqual(
                            z[slot_of[node_id]], ev,
                            msg=f"node {node_id}, inputs {feeds}",
                        )
                    # 常量节点的值内联在约束里，不占槽。
                    self.assertEqual(cc.nodes[5].value, 2)

                    # 补充：独立点积复算，所有约束必须满足。
                    report = audit(cc, z)
                    self.assertTrue(report.ok, msg=[
                        (r.index, r.tag, r.lhs, r.rhs)
                        for r in report.results if not r.satisfied
                    ])
                    for con in cc.constraints:
                        ok, lhs, rhs = reference_check_constraint(
                            con.a, con.b, con.c, z
                        )
                        self.assertTrue(ok, msg=f"constraint {con.index}")
                        res = report.results[con.index]
                        self.assertEqual((res.lhs, res.rhs), (lhs, rhs))

    def test_constant_operands_are_inlined_into_constant_slot(self):
        # 独立规格：(40 + 7) * 2
        spec = [
            {"kind": "const", "value": 40},
            {"kind": "const", "value": 7},
            {"kind": "add", "inputs": (0, 1)},
            {"kind": "const", "value": 2},
            {"kind": "mul", "inputs": (2, 3)},
        ]
        c = Circuit()
        a = c.const(40)
        b = c.const(7)
        d = c.add(a, b)
        e = c.mul(d, c.const(2))
        cc = compile_circuit(c)
        z = generate_witness(cc, {})
        expected = reference_eval(spec, {})
        self.assertEqual(z[slot(cc, d)], expected[2])
        self.assertEqual(z[slot(cc, e)], expected[4])
        self.assertTrue(audit(cc, z).ok)
        # 常量不占槽，只有 z0=1、d、e 共 3 个变量。
        self.assertEqual(cc.n_vars, 3)


def slot(cc, node_id):
    return next(i.slot for i in cc.sources if i.node == node_id)


class TestSharedSubgraph(unittest.TestCase):
    def test_shared_node_gets_one_slot_and_sound_constraints(self):
        c = build_poly_circuit()
        cc = compile_circuit(c)
        # 节点 3（s=x+y）被节点 4 与节点 7 共享，但只占一个见证槽。
        s_slots = [info.slot for info in cc.sources if info.node == 3]
        self.assertEqual(s_slots, [4])  # 槽位：1=x,2=y,3=b,4=s
        # 约束数量：add 1 + mul 2 个 + select 2 = 5。
        tags = [con.tag for con in cc.constraints]
        self.assertEqual(tags.count("add"), 1)
        self.assertEqual(tags.count("mul"), 2)
        self.assertEqual(tags.count("select_value"), 1)
        self.assertEqual(tags.count("select_booleanity"), 1)

        # 篡改共享槽的任何一个错误值（枚举全 97 个域值），审计必失败。
        z = generate_witness(cc, {"x": 10, "y": 12, "b": 1})
        good = z[4]
        for wrong in range(P):
            if wrong == good:
                continue
            zz = z.copy()
            zz[4] = wrong
            report = audit(cc, zz)
            self.assertFalse(
                report.ok, msg=f"shared-slot value {wrong} unexpectedly accepted"
            )
            # 至少一条失败定位到共享槽定义本身（add 节点 3）或其消费者。
            hit = {f.node for f in report.failures}
            self.assertTrue(
                hit & {3, 4, 7}, msg=f"unexpected failure nodes: {hit}"
            )


class TestSelectBooleanity(unittest.TestCase):
    def setUp(self):
        self.cc = compile_circuit(build_poly_circuit())

    def test_non_boolean_selector_rejected_at_witness_generation(self):
        for bad in (2, 3, 50, 96, -1):
            with self.assertRaises(NonBooleanSelectError) as ctx:
                generate_witness(self.cc, {"x": 1, "y": 2, "b": bad})
            self.assertEqual(ctx.exception.node, 6)
            self.assertEqual(ctx.exception.b, bad % P)

    def test_booleanity_constraint_rejects_every_non_01_value(self):
        z = generate_witness(self.cc, {"x": 1, "y": 2, "b": 1})
        b_slot = self.cc.inputs["b"]
        bool_idx = next(
            con.index for con in self.cc.constraints
            if con.tag == "select_booleanity"
        )
        for bv in range(P):
            zz = z.copy()
            zz[b_slot] = bv
            report = audit(self.cc, zz)
            res = report.results[bool_idx]
            self.assertIs(res.satisfied, bv in (0, 1), msg=f"b={bv}")
            if bv not in (0, 1):
                # b*(b-1) 的独立期望值作为差分校验。
                self.assertEqual(res.difference, (bv * (bv - 1)) % P)

    def test_constant_non_boolean_selector_makes_constraints_unsatisfiable(self):
        c = Circuit()
        x = c.input("x")
        y = c.input("y")
        c.select(c.const(2), x, y)
        cc = compile_circuit(c)
        # 无法生成见证：选择位是常量 2。
        with self.assertRaises(NonBooleanSelectError):
            generate_witness(cc, {"x": 1, "y": 2})
        # 且对任何 v（枚举全部域值）布尔性约束都不可能满足。
        bool_con = next(con for con in cc.constraints
                        if con.tag == "select_booleanity")
        for v in range(P):
            ok, _, _ = reference_check_constraint(
                bool_con.a, bool_con.b, bool_con.c,
                [1, 0, 0, v],
            )
            self.assertFalse(ok, msg=f"v={v}")


class TestIntermediateTamperIsLocated(unittest.TestCase):
    def test_every_wrong_intermediate_value_fails_audit(self):
        c = Circuit()
        x = c.input("x")
        y = c.input("y")
        s = c.add(x, y)
        m = c.mul(s, c.const(3))
        cc = compile_circuit(c)
        z = generate_witness(cc, {"x": 20, "y": 40})

        intermediate_slots = [
            info.slot for info in cc.sources
            if info.role == "intermediate"
        ]
        self.assertEqual(sorted(intermediate_slots), [3, 4])
        for sidx in intermediate_slots:
            good = z[sidx]
            for wrong in range(P):
                if wrong == good:
                    continue
                zz = z.copy()
                zz[sidx] = wrong
                report = audit(cc, zz)
                self.assertFalse(report.ok)
                for f in report.failures:
                    # 每条失败都能定位到节点/约束索引/两侧值/差。
                    self.assertIsInstance(f.index, int)
                    self.assertIn(f.node, (s, m))
                    self.assertTrue(f.origin)
                    self.assertNotEqual(f.lhs, f.rhs)
                    self.assertEqual(f.difference, (f.lhs - f.rhs) % P)

    def test_input_slot_role_distinct_from_intermediate(self):
        cc = compile_circuit(build_poly_circuit())
        input_slots = set(cc.inputs.values())
        inter = {i.slot for i in cc.sources if i.role == "intermediate"}
        self.assertTrue(input_slots.isdisjoint(inter))
        # 见证 API 只按名字接收输入，调用方没有任何途径指定中间槽。
        self.assertEqual(set(cc.inputs), {"x", "y", "b"})


class TestAssertEqual(unittest.TestCase):
    def _circuit(self):
        # 断言 (x+1)*(x-1) == x*x-1（在域内恒等）。
        c = Circuit()
        x = c.input("x")
        one = c.const(1)
        lhs = c.mul(c.add(x, one), c.add(x, c.const(-1)))
        x2 = c.mul(x, x)
        rhs = c.add(x2, c.const(-1))
        a = c.assert_equal(lhs, rhs)
        out = c.mul(a, c.const(2))  # 断言节点输出可取左值继续参与运算
        return c, x, a, out

    def test_identity_holds_for_all_field_elements(self):
        c, x, a, out = self._circuit()
        cc = compile_circuit(c)
        for xv in range(P):
            z = generate_witness(cc, {"x": xv})
            self.assertTrue(audit(cc, z).ok, msg=f"x={xv}")
            self.assertEqual(z[slot(cc, a)], (xv * xv - 1) % P)
            self.assertEqual(z[slot(cc, out)], (2 * (xv * xv - 1)) % P)

    def test_mismatch_rejected_with_located_error(self):
        c = Circuit()
        x = c.input("x")
        node = c.assert_equal(x, c.const(10))
        cc = compile_circuit(c)
        with self.assertRaises(AssertEqualError) as ctx:
            generate_witness(cc, {"x": 11})
        self.assertEqual(ctx.exception.node, node)
        self.assertEqual((ctx.exception.left, ctx.exception.right), (11, 10))

    def test_audit_catches_tampered_assert_witness(self):
        c = Circuit()
        x = c.input("x")
        a = c.assert_equal(x, c.const(5))
        cc = compile_circuit(c)
        z = generate_witness(cc, {"x": 5})

        # 篡改操作数（输入槽）：相等性约束 (x-5)*1=0 必须失败并定位到该断言。
        z1 = z.copy()
        z1[cc.inputs["x"]] = 6
        report = audit(cc, z1)
        self.assertFalse(report.ok)
        eq_fail = [f for f in report.failures if f.tag == "assert_equal"]
        self.assertEqual(len(eq_fail), 1)
        self.assertEqual(eq_fail[0].node, a)
        self.assertEqual((eq_fail[0].lhs, eq_fail[0].rhs), (1, 0))

        # 篡改断言输出槽：定义该槽的 assert_value 约束必须失败。
        z2 = z.copy()
        z2[slot(cc, a)] = 6
        report2 = audit(cc, z2)
        self.assertFalse(report2.ok)
        val_fail = [f for f in report2.failures if f.tag == "assert_value"]
        self.assertEqual(len(val_fail), 1)
        self.assertEqual(val_fail[0].node, a)


class TestWitnessInputErrors(unittest.TestCase):
    def setUp(self):
        self.cc = compile_circuit(build_poly_circuit())

    def test_unknown_input_is_infeasible_not_budget(self):
        with self.assertRaises(UnknownInputError) as ctx:
            generate_witness(self.cc, {"x": 1, "y": 2})  # 缺 b
        self.assertEqual(ctx.exception.name, "b")

    def test_extra_input_rejected(self):
        with self.assertRaises(UnexpectedInputError):
            generate_witness(self.cc, {"x": 1, "y": 2, "b": 0, "q": 1})

    def test_bool_nan_inf_float_inputs_rejected(self):
        with self.assertRaises(TypeError):
            generate_witness(self.cc, {"x": True, "y": 2, "b": 0})
        with self.assertRaises(ValueError):
            generate_witness(self.cc, {"x": float("nan"), "y": 2, "b": 0})
        with self.assertRaises(ValueError):
            generate_witness(self.cc, {"x": float("inf"), "y": 2, "b": 0})
        with self.assertRaises(TypeError):
            generate_witness(self.cc, {"x": 1.5, "y": 2, "b": 0})

    def test_non_mapping_and_non_str_key(self):
        with self.assertRaises(TypeError):
            generate_witness(self.cc, [("x", 1)])
        with self.assertRaises(TypeError):
            generate_witness(self.cc, {1: 1, "y": 2, "b": 0})

    def test_negative_ints_are_modular_not_rejected(self):
        z = generate_witness(self.cc, {"x": -1, "y": 0, "b": 0})
        self.assertEqual(z[self.cc.inputs["x"]], 96)


class TestAuditShape(unittest.TestCase):
    def setUp(self):
        self.cc = compile_circuit(build_poly_circuit())
        self.z = generate_witness(self.cc, {"x": 1, "y": 2, "b": 0})

    def test_wrong_length(self):
        with self.assertRaises(AuditError):
            audit(self.cc, self.z[:-1])

    def test_bad_element_types_and_values(self):
        for bad in (True, 1.0, float("nan"), float("inf"), "1", 97, -1):
            zz = self.z.copy()
            zz[1] = bad
            with self.assertRaises(AuditError, msg=f"bad={bad!r}"):
                audit(self.cc, zz)

    def test_z0_must_be_one(self):
        zz = self.z.copy()
        zz[0] = 2
        with self.assertRaises(AuditError):
            audit(self.cc, zz)


class TestSparseFormat(unittest.TestCase):
    def test_sparse_terms_sorted_reduced_nonzero(self):
        c = Circuit()
        x = c.input("x")
        # s = x + (-1)，C 中常数项系数为 96，且槽位按升序排列。
        s = c.add(x, c.const(-1))
        cc = compile_circuit(c)
        con = cc.constraints[0]
        self.assertEqual(con.node, s)
        self.assertEqual(con.a, ((0, 1),))
        self.assertEqual(con.b, ((slot(cc, s), 1),))
        self.assertEqual(con.c, ((0, P - 1), (cc.inputs["x"], 1)))

    def test_zero_coefficients_cancel_out(self):
        c = Circuit()
        x = c.input("x")
        # (x + 0) 的常数 0 项不得出现在稀疏表示中。
        s = c.add(x, c.const(0))
        cc = compile_circuit(c)
        con = cc.constraints[0]
        self.assertEqual(con.c, ((cc.inputs["x"], 1),))

    def test_sources_table(self):
        cc = compile_circuit(build_poly_circuit())
        self.assertEqual(cc.sources[0].role, "constant_one")
        self.assertEqual(cc.sources[0].slot, 0)
        for info in cc.sources[1:]:
            self.assertIn(info.role, ("input", "intermediate"))
            self.assertIsNotNone(info.node)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
