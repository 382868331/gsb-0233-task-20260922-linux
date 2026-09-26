"""select 与 guarded_equal 条件语义的专项测试。

约束期望值使用 tests.reference 的独立朴素点积复算；参考解释器不导入
zkcirc，避免用被测编译器给被测编译器作证。
"""

import unittest

from zkcirc import (
    P,
    Circuit,
    compile_circuit,
    generate_witness,
    audit,
    NonBooleanGuardSelectorError,
    GuardedEqualError,
)

try:  # pragma: no cover
    from .reference import reference_eval, reference_check_constraint
except ImportError:  # pragma: no cover
    from reference import reference_eval, reference_check_constraint


def build_conditional_inverse_circuit():
    """b=1 时要求 x*inv=1；b=0 时允许 x=0,inv=0，不强制逆元。

    另用 select(b,x,fallback) 选择输出，fallback 是明确求值的加法节点。
    guarded_equal 自身也输出左值 product，占用一个已初始化中间槽。
    """

    c = Circuit()
    b = c.input("b")
    x = c.input("x")
    inv = c.input("inv")
    fallback_base = c.input("fallback_base")
    product = c.mul(x, inv)
    one = c.const(1)
    guard = c.guarded_equal(b, product, one)
    fallback = c.add(fallback_base, one)
    chosen = c.select(b, x, fallback)
    spec = [
        {"kind": "input", "name": "b"},
        {"kind": "input", "name": "x"},
        {"kind": "input", "name": "inv"},
        {"kind": "input", "name": "fallback_base"},
        {"kind": "mul", "inputs": (1, 2)},
        {"kind": "const", "value": 1},
        {"kind": "guarded_equal", "inputs": (0, 4, 5)},
        {"kind": "add", "inputs": (3, 5)},
        {"kind": "select", "inputs": (0, 1, 7)},
    ]
    nodes = {
        "b": b, "x": x, "inv": inv, "fallback_base": fallback_base,
        "product": product, "guard": guard,
        "fallback": fallback, "chosen": chosen,
    }
    return c, spec, nodes


def independent_audit(compiled, witness):
    """完全绕开 zkcirc.audit 的逐条参考审计。"""

    results = []
    for con in compiled.constraints:
        ok, lhs, rhs = reference_check_constraint(
            con.a, con.b, con.c, witness
        )
        results.append((con, ok, lhs, rhs))
    return results


class TestGuardedReference(unittest.TestCase):
    def test_witness_matches_independent_interpreter(self):
        c, spec, _ = build_conditional_inverse_circuit()
        cc = compile_circuit(c)
        inv_two = pow(2, P - 2, P)
        cases = (
            {"b": 0, "x": 0, "inv": 0, "fallback_base": 5},
            {"b": 1, "x": 2, "inv": inv_two, "fallback_base": 5},
        )
        slot_of = {info.node: info.slot for info in cc.sources
                   if info.node is not None}

        for feeds in cases:
            expected = reference_eval(spec, feeds)
            z = generate_witness(cc, feeds)
            for node_id, value in enumerate(expected):
                if cc.nodes[node_id].kind == "const":
                    continue
                self.assertEqual(z[slot_of[node_id]], value)
            self.assertTrue(audit(cc, z).ok)
            self.assertTrue(all(ok for _, ok, _, _ in independent_audit(cc, z)))

    def test_constraint_sources_identify_new_intermediates(self):
        c, _, nodes = build_conditional_inverse_circuit()
        cc = compile_circuit(c)
        guard_info = next(i for i in cc.sources if i.node == nodes["guard"])
        self.assertEqual(guard_info.role, "intermediate")
        self.assertEqual(guard_info.kind, "guarded_equal")
        tags = {con.tag: con for con in cc.constraints}
        self.assertEqual(
            tags["guarded_value"].origin,
            f"guarded_equal node {nodes['guard']}: output v takes left operand",
        )
        self.assertEqual(
            tags["guarded_booleanity"].origin,
            f"guarded_equal node {nodes['guard']}: b*(b-1) = 0 "
            "(boolean selector)",
        )
        self.assertEqual(
            tags["guarded_equal"].origin,
            f"guarded_equal node {nodes['guard']}: b*(x-y) = 0",
        )


class TestGuardedInverseBranch(unittest.TestCase):
    def setUp(self):
        c, _, self.nodes = build_conditional_inverse_circuit()
        self.cc = compile_circuit(c)
        self.slot_of = {info.node: info.slot for info in self.cc.sources
                        if info.node is not None}

    def test_closed_branch_allows_zero_without_inverse(self):
        feeds = {"b": 0, "x": 0, "inv": 0, "fallback_base": 5}
        z = generate_witness(self.cc, feeds)
        self.assertEqual(z[self.slot_of[self.nodes["product"]]], 0)
        self.assertEqual(z[self.slot_of[self.nodes["guard"]]], 0)
        self.assertEqual(z[self.slot_of[self.nodes["chosen"]]], 6)
        self.assertTrue(all(0 <= v < P for v in z))
        self.assertTrue(all(ok for _, ok, _, _ in independent_audit(self.cc, z)))

    def test_open_branch_rejects_missing_inverse(self):
        with self.assertRaises(GuardedEqualError) as ctx:
            generate_witness(
                self.cc,
                {"b": 1, "x": 0, "inv": 0, "fallback_base": 5},
            )
        self.assertEqual(ctx.exception.node, self.nodes["guard"])
        self.assertEqual((ctx.exception.left, ctx.exception.right), (0, 1))

    def test_open_branch_accepts_real_inverse(self):
        inv_two = pow(2, P - 2, P)
        z = generate_witness(
            self.cc,
            {"b": 1, "x": 2, "inv": inv_two, "fallback_base": 5},
        )
        self.assertEqual(z[self.slot_of[self.nodes["chosen"]]], 2)
        self.assertTrue(all(ok for _, ok, _, _ in independent_audit(self.cc, z)))

    def test_selector_two_is_rejected_by_circuit_not_generator_only(self):
        feeds = {"b": 0, "x": 1, "inv": 1, "fallback_base": 5}
        z = generate_witness(self.cc, feeds)
        z[self.cc.inputs["b"]] = 2

        with self.assertRaises(NonBooleanGuardSelectorError):
            generate_witness(self.cc, {**feeds, "b": 2})

        by_tag = {con.tag: (con, ok, lhs, rhs)
                  for con, ok, lhs, rhs in independent_audit(self.cc, z)}
        self.assertFalse(by_tag["guarded_booleanity"][1])
        # product=1 时，单看 b*(product-1)=0 会在 b=2 下成立；
        # 布尔性约束仍然拦住这种插值绕过。
        self.assertTrue(by_tag["guarded_equal"][1])
        self.assertFalse(audit(self.cc, z).ok)

    def test_every_domain_selector_other_than_01_is_rejected(self):
        closed_feeds = {"b": 0, "x": 0, "inv": 0, "fallback_base": 5}
        open_feeds = {
            "b": 1, "x": 2, "inv": pow(2, P - 2, P), "fallback_base": 5,
        }
        for base_feeds, accepted in ((closed_feeds, 0), (open_feeds, 1)):
            base_z = generate_witness(self.cc, base_feeds)
            for selector in range(P):
                zz = base_z.copy()
                zz[self.cc.inputs["b"]] = selector
                independent_ok = all(
                    ok for _, ok, _, _ in independent_audit(self.cc, zz)
                )
                self.assertIs(
                    independent_ok,
                    selector == accepted,
                    msg=f"base={accepted}, selector={selector}",
                )

    def test_tampered_selected_branch_value_is_rejected(self):
        inv_two = pow(2, P - 2, P)
        feeds = {"b": 1, "x": 2, "inv": inv_two, "fallback_base": 5}
        z = generate_witness(self.cc, feeds)
        z[self.slot_of[self.nodes["product"]]] = 0

        results = independent_audit(self.cc, z)
        guarded = next(item for item in results if item[0].tag == "guarded_equal")
        self.assertFalse(guarded[1])
        self.assertFalse(audit(self.cc, z).ok)

    def test_tampered_nonselected_value_has_defined_slot_but_no_spurious_guard(self):
        inv_two = pow(2, P - 2, P)
        feeds = {"b": 1, "x": 2, "inv": inv_two, "fallback_base": 5}
        z = generate_witness(self.cc, feeds)
        fallback_slot = self.slot_of[self.nodes["fallback"]]
        self.assertEqual(z[fallback_slot], 6)
        z[fallback_slot] = 7

        results = {con.tag: ok for con, ok, _, _ in
                   independent_audit(self.cc, z)}
        self.assertTrue(results["guarded_equal"])
        self.assertTrue(results["select_value"])
        self.assertFalse(results["add"])
        self.assertFalse(audit(self.cc, z).ok)

    def test_closed_inverse_requirement_stays_inactive_after_tamper(self):
        feeds = {"b": 0, "x": 0, "inv": 0, "fallback_base": 5}
        z = generate_witness(self.cc, feeds)
        z[self.cc.inputs["x"]] = 1  # product 仍为 0，关闭分支不要求逆元。
        results = {con.tag: ok for con, ok, _, _ in
                   independent_audit(self.cc, z)}
        self.assertTrue(results["guarded_equal"])
        self.assertTrue(results["select_value"])
        self.assertTrue(audit(self.cc, z).ok)


class TestGuardedBuilder(unittest.TestCase):
    def test_references_are_validated(self):
        c = Circuit()
        with self.assertRaises(TypeError):
            c.guarded_equal(True, 0, 0)
        with self.assertRaises(Exception):
            c.guarded_equal(0, 1, 2)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
