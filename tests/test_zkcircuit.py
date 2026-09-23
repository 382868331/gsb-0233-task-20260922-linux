"""Test suite for the zkcircuit package.

The independent oracle is ``zkcircuit.interp.evaluate`` (a direct DAG
interpreter that never calls the compiler or witness generator); a few
hand-computed GF(97) values are also asserted literally.
"""

import unittest

from zkcircuit import (
    MAX_NODES,
    PRIME,
    AssertionViolationError,
    Circuit,
    DuplicateInputNameError,
    IntermediateOverrideError,
    MissingInputError,
    NodeLimitError,
    NonBooleanSelectError,
    UnknownInputError,
    ValidationError,
    audit,
    evaluate,
    generate_witness,
    validate_field_value,
)


def build_sample():
    """Sample circuit exercising sharing, select and assert_equal.

    DAG:
        three = const 3;  x, y inputs
        shared = x * y          (shared by total and the identity check)
        total  = shared + x
        picked = select(y, total, three)       # y*total + (1-y)*3
        # independent recomputation of the same mux, then asserted equal:
        ny       = 1 + (-1)*y
        picked2  = y*total + ny*three
        assert_equal(picked, picked2)
    """
    c = Circuit()
    three = c.const(3)
    x = c.input("x")
    y = c.input("y")
    shared = c.mul(x, y)          # shared by total and picked2
    total = c.add(shared, x)      # x*y + x
    picked = c.select(y, total, three)
    neg_one = c.const(PRIME - 1)
    ny = c.add(c.const(1), c.mul(neg_one, y))
    picked2 = c.add(c.mul(y, total), c.mul(ny, three))
    c.assert_equal(picked, picked2)
    return c, dict(three=three, x=x, y=y, shared=shared,
                   total=total, picked=picked, picked2=picked2)


class TestFieldValidation(unittest.TestCase):
    def test_rejects_bool(self):
        with self.assertRaises(ValidationError):
            validate_field_value(True, where="t")
        with self.assertRaises(ValidationError):
            validate_field_value(False, where="t")

    def test_rejects_nan_and_infinity(self):
        for bad in (float("nan"), float("inf"), float("-inf")):
            with self.assertRaises(ValidationError):
                validate_field_value(bad, where="t")

    def test_rejects_non_integral_float(self):
        with self.assertRaises(ValidationError):
            validate_field_value(2.5, where="t")

    def test_accepts_integral_float(self):
        self.assertEqual(validate_field_value(3.0, where="t"), 3)

    def test_rejects_out_of_range(self):
        for bad in (-1, 97, 10**9):
            with self.assertRaises(ValidationError):
                validate_field_value(bad, where="t")

    def test_rejects_other_types(self):
        for bad in ("3", None, [1]):
            with self.assertRaises(ValidationError):
                validate_field_value(bad, where="t")

    def test_accepts_canonical_ints(self):
        for v in (0, 1, 96):
            self.assertEqual(validate_field_value(v, where="t"), v)


class TestCircuitBuilder(unittest.TestCase):
    def test_node_limit(self):
        c = Circuit()
        nodes = [c.const(1)]
        while len(c) < MAX_NODES:
            nodes.append(c.add(nodes[-1], nodes[0]))
        self.assertEqual(len(c), MAX_NODES)
        with self.assertRaises(NodeLimitError):
            c.add(nodes[-1], nodes[0])
        # failed call must not have mutated the circuit
        self.assertEqual(len(c), MAX_NODES)

    def test_duplicate_input_name_rejected(self):
        c = Circuit()
        c.input("a")
        with self.assertRaises(DuplicateInputNameError):
            c.input("a")

    def test_bad_input_name(self):
        c = Circuit()
        for bad in ("", 3, True, None):
            with self.assertRaises(ValidationError):
                c.input(bad)

    def test_foreign_child_rejected(self):
        c1, c2 = Circuit(), Circuit()
        a = c1.const(1)
        b = c2.const(2)
        with self.assertRaises(ValidationError):
            c1.add(a, b)

    def test_non_node_child_rejected(self):
        c = Circuit()
        a = c.const(1)
        with self.assertRaises(ValidationError):
            c.add(a, 5)

    def test_const_validates_value(self):
        c = Circuit()
        with self.assertRaises(ValidationError):
            c.const(float("nan"))
        with self.assertRaises(ValidationError):
            c.const(True)
        with self.assertRaises(ValidationError):
            c.const(97)


class TestCompileStructure(unittest.TestCase):
    def test_wire_zero_is_one_and_inputs_first(self):
        c, n = build_sample()
        cc = c.compile()
        self.assertEqual(cc.origins[0]["kind"], "constant")
        self.assertEqual(cc.origins[0]["value"], 1)
        self.assertEqual(cc.input_wires, {"x": 1, "y": 2})

    def test_shared_node_gets_single_wire(self):
        c, n = build_sample()
        cc = c.compile()
        wires = [w for w in cc.node_wires.values()]
        self.assertEqual(len(wires), len(set(wires)))
        # 'shared' (mul) is referenced by two parents but owns one wire
        shared_wire = cc.wire_of(n["shared"])
        self.assertEqual(
            sum(1 for o in cc.origins if o.get("node") == n["shared"].index),
            1,
        )
        self.assertEqual(cc.origins[shared_wire]["kind"], "mul")

    def test_assert_equal_owns_no_wire(self):
        c = Circuit()
        x = c.input("x")
        a = c.assert_equal(x, c.const(1))
        cc = c.compile()
        self.assertNotIn(a.index, cc.node_wires)
        with self.assertRaises(ValueError):
            cc.wire_of(a)

    def test_select_emits_booleanity_constraint(self):
        c, n = build_sample()
        cc = c.compile()
        labels = [con.label for con in cc.constraints]
        self.assertIn(f"select_bool#{n['picked'].index}", labels)
        # booleanity constraint is exactly z_b*(z_b - 1) = 0
        con = next(con for con in cc.constraints
                   if con.label == f"select_bool#{n['picked'].index}")
        bwire = cc.wire_of(n["y"])
        self.assertEqual(con.A, {bwire: 1})
        self.assertEqual(con.B, {bwire: 1, 0: PRIME - 1})
        self.assertEqual(con.C, {})

    def test_constraints_are_sparse(self):
        c, _ = build_sample()
        cc = c.compile()
        for con in cc.constraints:
            for vec in (con.A, con.B, con.C):
                for coef in vec.values():
                    self.assertNotEqual(coef % PRIME, 0)
                    self.assertTrue(0 < coef < PRIME)


class TestWitnessGeneration(unittest.TestCase):
    def test_witness_matches_interpreter(self):
        c, n = build_sample()
        cc = c.compile()
        inputs = {"x": 5, "y": 1}
        z = generate_witness(cc, inputs)
        ref = evaluate(c, inputs)
        for node in c.nodes:
            if node.op == "assert_equal":
                continue
            self.assertEqual(z[cc.node_wires[node.index]],
                             ref.values[node.index],
                             f"node#{node.index} {node.op}")
        self.assertEqual(z[0], 1)

    def test_hand_computed_values(self):
        # x=5, y=1: shared=5, total=5+5=10, picked=total=10
        c, n = build_sample()
        cc = c.compile()
        z = generate_witness(cc, {"x": 5, "y": 1})
        self.assertEqual(z[cc.wire_of(n["shared"])], 5)
        self.assertEqual(z[cc.wire_of(n["total"])], 10)
        self.assertEqual(z[cc.wire_of(n["picked"])], 10)
        # y=0 branch: picked = const 3
        z0 = generate_witness(cc, {"x": 5, "y": 0})
        self.assertEqual(z0[cc.wire_of(n["picked"])], 3)

    def test_modular_wraparound(self):
        c = Circuit()
        a = c.input("a")
        b = c.input("b")
        s = c.add(a, b)
        m = c.mul(a, b)
        cc = c.compile()
        z = generate_witness(cc, {"a": 96, "b": 96})
        self.assertEqual(z[cc.wire_of(s)], (96 + 96) % 97)   # 95
        self.assertEqual(z[cc.wire_of(m)], (96 * 96) % 97)   # 1

    def test_missing_input(self):
        c, _ = build_sample()
        cc = c.compile()
        with self.assertRaises(MissingInputError):
            generate_witness(cc, {"x": 1})

    def test_unknown_input(self):
        c, _ = build_sample()
        cc = c.compile()
        with self.assertRaises(UnknownInputError):
            generate_witness(cc, {"x": 1, "y": 1, "zzz": 2})

    def test_intermediate_override_rejected(self):
        c, _ = build_sample()
        cc = c.compile()
        with self.assertRaises(IntermediateOverrideError):
            generate_witness(cc, {"x": 1, "y": 1, "#3": 7})

    def test_input_values_validated(self):
        c, _ = build_sample()
        cc = c.compile()
        for bad in (True, float("nan"), float("inf"), 97, -1, 2.5, "1"):
            with self.assertRaises(ValidationError):
                generate_witness(cc, {"x": bad, "y": 1})

    def test_non_boolean_select_rejected(self):
        c = Circuit()
        b = c.input("b")
        one = c.const(1)
        two = c.const(2)
        c.select(b, one, two)
        cc = c.compile()
        with self.assertRaises(ValidationError):
            generate_witness(cc, {"b": 2})

    def test_inputs_mapping_not_mutated(self):
        c, _ = build_sample()
        cc = c.compile()
        inputs = {"x": 4, "y": 1}
        generate_witness(cc, inputs)
        self.assertEqual(inputs, {"x": 4, "y": 1})


class TestAudit(unittest.TestCase):
    def test_valid_witness_passes(self):
        c, _ = build_sample()
        cc = c.compile()
        z = generate_witness(cc, {"x": 7, "y": 1})
        report = audit(cc, z)
        self.assertTrue(report.ok, report.summary())
        self.assertEqual(report.checked, len(cc.constraints))
        self.assertEqual(report.failures, [])

    def test_tampered_intermediate_wire_located(self):
        c, n = build_sample()
        cc = c.compile()
        z = generate_witness(cc, {"x": 5, "y": 1})
        bad = list(z)
        bad[cc.wire_of(n["shared"])] = (bad[cc.wire_of(n["shared"])] + 1) % PRIME
        report = audit(cc, bad)
        self.assertFalse(report.ok)
        failed_labels = {f.label for f in report.failures}
        # the mul constraint that produced 'shared' must be reported
        self.assertIn(f"mul#{n['shared'].index}", failed_labels)
        for f in report.failures:
            self.assertNotEqual(f.lhs, f.rhs)

    def test_tampered_input_wire_located(self):
        c, n = build_sample()
        cc = c.compile()
        z = generate_witness(cc, {"x": 5, "y": 1})
        bad = list(z)
        bad[cc.wire_of(n["x"])] = (bad[cc.wire_of(n["x"])] + 1) % PRIME
        report = audit(cc, bad)
        self.assertFalse(report.ok)
        self.assertIn(f"mul#{n['shared'].index}",
                      {f.label for f in report.failures})

    def test_non_boolean_select_witness_fails_audit(self):
        c = Circuit()
        b = c.input("b")
        one = c.const(1)
        two = c.const(2)
        s = c.select(b, one, two)
        cc = c.compile()
        # hand-build a witness with b=2 (generator rightly refuses this)
        z = generate_witness(cc, {"b": 1})
        z[cc.wire_of(b)] = 2
        z[cc.wire_of(s)] = 1  # arbitrary claimed select output
        report = audit(cc, z)
        self.assertFalse(report.ok)
        self.assertIn(f"select_bool#{s.index}",
                      {f.label for f in report.failures})

    def test_assert_equal_violation_located(self):
        c = Circuit()
        x = c.input("x")
        a = c.assert_equal(x, c.const(10))
        cc = c.compile()
        z = generate_witness(cc, {"x": 11})
        report = audit(cc, z)
        self.assertFalse(report.ok)
        self.assertEqual([f.label for f in report.failures],
                         [f"assert_equal#{a.index}"])
        f = report.failures[0]
        self.assertEqual((f.lhs - f.rhs) % PRIME, 1)

    def test_malformed_witness_rejected(self):
        c, _ = build_sample()
        cc = c.compile()
        z = generate_witness(cc, {"x": 1, "y": 1})
        with self.assertRaises(ValidationError):
            audit(cc, z[:-1])                      # wrong length
        with self.assertRaises(ValidationError):
            audit(cc, [0] + z[1:])                 # z[0] != 1
        bad = list(z); bad[2] = True
        with self.assertRaises(ValidationError):
            audit(cc, bad)                         # bool entry
        bad = list(z); bad[2] = 97
        with self.assertRaises(ValidationError):
            audit(cc, bad)                         # out of range
        with self.assertRaises(ValidationError):
            audit(cc, "not a vector")


class TestInterpreter(unittest.TestCase):
    def test_interpreter_matches_witness_for_many_inputs(self):
        c, n = build_sample()
        cc = c.compile()
        for x in (0, 1, 13, 96):
            for y in (0, 1):
                inputs = {"x": x, "y": y}
                ref = evaluate(c, inputs)
                z = generate_witness(cc, inputs)
                self.assertEqual(z[cc.wire_of(n["picked"])],
                                 ref.of(n["picked"]))
                self.assertTrue(audit(cc, z).ok)

    def test_interpreter_assert_violation(self):
        c = Circuit()
        x = c.input("x")
        c.assert_equal(x, c.const(5))
        with self.assertRaises(AssertionViolationError):
            evaluate(c, {"x": 6})
        evaluate(c, {"x": 5})  # no raise

    def test_interpreter_non_boolean_select(self):
        c = Circuit()
        b = c.input("b")
        c.select(b, c.const(1), c.const(2))
        with self.assertRaises(NonBooleanSelectError):
            evaluate(c, {"b": 3})

    def test_interpreter_input_validation(self):
        c, _ = build_sample()
        with self.assertRaises(MissingInputError):
            evaluate(c, {"x": 1})
        with self.assertRaises(UnknownInputError):
            evaluate(c, {"x": 1, "y": 1, "q": 1})
        with self.assertRaises(ValidationError):
            evaluate(c, {"x": float("nan"), "y": 1})


class TestSharedSubgraphEvaluation(unittest.TestCase):
    def test_shared_subgraph_single_evaluation_and_wire(self):
        c = Circuit()
        x = c.input("x")
        shared = c.mul(x, x)
        # use the shared node many times
        acc = c.add(shared, shared)
        acc = c.mul(acc, shared)
        acc = c.add(acc, shared)
        cc = c.compile()
        # exactly one wire and one mul-constraint for 'shared'
        mul_wires = [o for o in cc.origins if o["kind"] == "mul"]
        self.assertEqual(len(mul_wires), 2)  # shared + the later mul
        self.assertEqual(
            sum(1 for o in cc.origins if o.get("node") == shared.index), 1)
        z = generate_witness(cc, {"x": 4})
        # x=4: shared=16, acc=((16+16)*16+16) mod 97 = (32*16+16)=528 mod 97
        self.assertEqual(z[cc.wire_of(shared)], 16)
        self.assertEqual(z[cc.wire_of(acc)], 528 % 97)
        self.assertEqual(evaluate(c, {"x": 4}).of(acc), 528 % 97)
        self.assertTrue(audit(cc, z).ok)


if __name__ == "__main__":
    unittest.main()
