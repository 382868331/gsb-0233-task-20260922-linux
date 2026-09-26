"""guarded_assert 条件节点与 guarded 约束的测试。

期望值来自 tests.reference 中独立编写的朴素域解释器（不导入 zkcirc）；
篡改检测由独立审计器（reference_check_constraint 独立点积）复算，
不依赖 zkcirc.audit 的结论。
"""

import unittest

from zkcirc import (
    P,
    Circuit,
    compile_circuit,
    generate_witness,
    audit,
    CircuitBuildError,
    NonBooleanSelectError,
    GuardedAssertError,
)

try:  # pragma: no cover - 取决于 unittest 的发现方式
    from .reference import reference_eval, reference_check_constraint
except ImportError:  # pragma: no cover
    from reference import reference_eval, reference_check_constraint


# ---------------------------------------------------------------------------
# 确定性夹具：select + guarded_assert 组合电路。
#
#   0: input b                选择位
#   1: input x                「选中」分支值
#   2: input y                「非选中」分支值
#   3: select s = b ? x : y
#   4: guarded_assert g = (b, x, y)   b=1 时强制 x==y；输出取 x
#   5: mul out = s * g
#
# 独立参考规格（朴素 dict，不经过 zkcirc）：
GUARD_SPEC = [
    {"kind": "input", "name": "b"},
    {"kind": "input", "name": "x"},
    {"kind": "input", "name": "y"},
    {"kind": "select", "inputs": (0, 1, 2)},
    {"kind": "guarded_assert", "inputs": (0, 1, 2)},
    {"kind": "mul", "inputs": (3, 4)},
]


def build_guard_circuit() -> Circuit:
    c = Circuit()
    b = c.input("b")
    x = c.input("x")
    y = c.input("y")
    s = c.select(b, x, y)
    g = c.guarded_assert(b, x, y)
    out = c.mul(s, g)
    assert (b, x, y, s, g, out) == (0, 1, 2, 3, 4, 5)
    return c


def independent_audit(cc, z):
    """独立约束审计器：只用 reference 的朴素点积逐条复算，返回失败下标。"""

    failed = []
    for con in cc.constraints:
        ok, _lhs, _rhs = reference_check_constraint(con.a, con.b, con.c, z)
        if not ok:
            failed.append(con.index)
    return failed


def slot_of_node(cc, node):
    for info in cc.sources:
        if info.node == node:
            return info.slot
    raise AssertionError(f"node {node} has no slot")


class TestGuardedAgainstReference(unittest.TestCase):
    def test_witness_matches_reference_on_grid(self):
        cc = compile_circuit(build_guard_circuit())
        slot_of = {info.node: info.slot for info in cc.sources
                   if info.node is not None}
        for b in (0, 1):
            for x in (0, 1, 5, 42, 96, -3):
                for y in (0, 1, 5, 77, 96, 200):
                    inputs = {"b": b, "x": x, "y": y}
                    try:
                        expected = reference_eval(GUARD_SPEC, inputs)
                    except ValueError:
                        with self.assertRaises(GuardedAssertError):
                            generate_witness(cc, inputs)
                        continue
                    z = generate_witness(cc, inputs)
                    for node, value in enumerate(expected):
                        if GUARD_SPEC[node]["kind"] == "const":
                            continue
                        self.assertEqual(z[slot_of[node]], value,
                                         f"node {node} inputs={inputs}")
                    self.assertTrue(audit(cc, z).ok)

    def test_guard_off_allows_unequal_branches(self):
        # b=0：等式不生效，x!=y 也能生成见证并通过审计。
        cc = compile_circuit(build_guard_circuit())
        z = generate_witness(cc, {"b": 0, "x": 10, "y": 20})
        self.assertTrue(audit(cc, z).ok)
        # 两支见证槽都有明确赋值（x=10、y=20），不留未初始化槽。
        self.assertEqual(z[slot_of_node(cc, 1)], 10)
        self.assertEqual(z[slot_of_node(cc, 2)], 20)
        self.assertEqual(z[slot_of_node(cc, 4)], 10)  # 输出取左支

    def test_guard_on_rejects_unequal_branches(self):
        cc = compile_circuit(build_guard_circuit())
        with self.assertRaises(GuardedAssertError) as ctx:
            generate_witness(cc, {"b": 1, "x": 10, "y": 20})
        err = ctx.exception
        self.assertEqual(err.node, 4)
        self.assertEqual(err.selector, 1)
        self.assertEqual((err.left, err.right), (10, 20))

    def test_guard_on_accepts_equal_branches(self):
        cc = compile_circuit(build_guard_circuit())
        z = generate_witness(cc, {"b": 1, "x": 33, "y": 33})
        self.assertTrue(audit(cc, z).ok)

    def test_non_boolean_selector_rejected(self):
        cc = compile_circuit(build_guard_circuit())
        for bad in (2, 3, 96):
            with self.assertRaises(NonBooleanSelectError) as ctx:
                generate_witness(cc, {"b": bad, "x": 5, "y": 5})
            self.assertEqual(ctx.exception.b, bad % P)


class TestGuardedConstraintShape(unittest.TestCase):
    def test_guarded_constraints_and_sources(self):
        cc = compile_circuit(build_guard_circuit())
        tags = [con.tag for con in cc.constraints if con.node == 4]
        self.assertEqual(tags,
                         ["guarded_value", "guarded_equal", "guarded_booleanity"])
        for con in cc.constraints:
            if con.node == 4:
                self.assertIn("guarded_assert node 4", con.origin)
        info = cc.sources[slot_of_node(cc, 4)]
        self.assertEqual((info.role, info.kind), ("intermediate", "guarded_assert"))

    def test_selector_constrained_boolean_in_compiled_r1cs(self):
        # 不经过见证生成器：直接对编译产物做独立审计，b=2 必须被
        # 电路约束本身拒绝（布尔性约束写在电路里，而非只在生成器里判断）。
        cc = compile_circuit(build_guard_circuit())
        z = generate_witness(cc, {"b": 1, "x": 7, "y": 7})
        z[slot_of_node(cc, 0)] = 2
        failed = independent_audit(cc, z)
        failed_tags = {cc.constraints[i].tag for i in failed}
        self.assertIn("select_booleanity", failed_tags)
        self.assertIn("guarded_booleanity", failed_tags)


class TestIndependentAuditTampering(unittest.TestCase):
    """用独立审计器篡改 selector、选中值、非选中值，验证必然被捕获。"""

    def setUp(self):
        self.cc = compile_circuit(build_guard_circuit())

    def _tamper_and_check(self, node, new_value, expected_tags):
        z = generate_witness(self.cc, {"b": 0, "x": 9, "y": 4})
        z[slot_of_node(self.cc, node)] = new_value % P
        failed = independent_audit(self.cc, z)
        self.assertTrue(failed, f"tampering node {node} was not detected")
        failed_tags = {self.cc.constraints[i].tag for i in failed}
        self.assertTrue(expected_tags & failed_tags,
                        f"expected {expected_tags}, got {failed_tags}")
        # zkcirc 自带审计器结论与独立审计器一致（往返一致性补充）。
        self.assertFalse(audit(self.cc, z).ok)

    def test_tamper_selector(self):
        # b: 0 -> 1（两支不等）：开启守卫后 select/guarded 约束全部对不上。
        # 注：两支相等时翻转 b 在 R1CS 关系语义下本就不可区分，
        # 因此本用例在 x!=y 的合法见证上篡改。
        self._tamper_and_check(0, 1, {"select_value", "guarded_equal"})

    def test_tamper_selected_value(self):
        # 选中分支 y: 4 -> 11（b=0 时 y 被 select 选中，被 select_value
        # 钉住，篡改必然触发）。
        self._tamper_and_check(2, 11, {"select_value"})

    def test_tamper_unselected_value(self):
        # 非选中分支 x: 9 -> 10（b=0 时 x 未被 select 选中，但被
        # guarded_value 输出定义钉住，篡改必然触发）。
        self._tamper_and_check(1, 10, {"guarded_value"})

    def test_tamper_selected_value_guard_on(self):
        # b=1 时 x 被选中且被守卫：x: 9 -> 10 触发多处约束失败。
        z = generate_witness(self.cc, {"b": 1, "x": 9, "y": 9})
        z[slot_of_node(self.cc, 1)] = 10
        failed = independent_audit(self.cc, z)
        failed_tags = {self.cc.constraints[i].tag for i in failed}
        self.assertTrue(
            {"select_value", "guarded_equal", "guarded_value"} & failed_tags)
        self.assertFalse(audit(self.cc, z).ok)

    def test_selector_two_cannot_interpolate_bypass(self):
        # 关键对抗场景：把 selector 改成 2，并按 v = 2*x - y 插值伪造
        # select 输出，试图让 select_value 等式成立以绕过条件。
        cc = self.cc
        z = generate_witness(cc, {"b": 1, "x": 9, "y": 9})
        z[slot_of_node(cc, 0)] = 2
        z[slot_of_node(cc, 3)] = (2 * 9 - 9) % P  # 满足 b*(x-y)=v-y 的伪造值
        failed = independent_audit(cc, z)
        failed_tags = {cc.constraints[i].tag for i in failed}
        # 布尔性约束 b*(b-1)=0 在 b=2 时必然失败：插值无法绕过。
        self.assertIn("select_booleanity", failed_tags)
        self.assertIn("guarded_booleanity", failed_tags)
        self.assertFalse(audit(cc, z).ok)

    def test_selector_two_cannot_satisfy_guard_either(self):
        # b=2 且 x!=y：guarded_equal 为 2*(x-y)!=0，同样被钉住。
        cc = self.cc
        z = generate_witness(cc, {"b": 0, "x": 3, "y": 8})
        z[slot_of_node(cc, 0)] = 2
        failed = independent_audit(cc, z)
        failed_tags = {cc.constraints[i].tag for i in failed}
        self.assertIn("guarded_equal", failed_tags)
        self.assertIn("guarded_booleanity", failed_tags)


class TestGuardedInverseBranch(unittest.TestCase):
    """关闭的分支不应触发仅该分支要求的「除零逆元」约束；开启时必须拒绝。

    电路：d 为被求逆的量，w 为调用方提供的候选逆元；
    guarded_assert(b, d*w, 1) 仅在 b=1 时强制 d*w == 1（即 w 是 d 的逆元）。

      0: input b
      1: input d
      2: input w
      3: const 1
      4: mul  p = d * w
      5: guarded_assert g = (b, p, const1)
    """

    SPEC = [
        {"kind": "input", "name": "b"},
        {"kind": "input", "name": "d"},
        {"kind": "input", "name": "w"},
        {"kind": "const", "value": 1},
        {"kind": "mul", "inputs": (1, 2)},
        {"kind": "guarded_assert", "inputs": (0, 4, 3)},
    ]

    def build(self):
        c = Circuit()
        b = c.input("b")
        d = c.input("d")
        w = c.input("w")
        one = c.const(1)
        p = c.mul(d, w)
        g = c.guarded_assert(b, p, one)
        assert (b, d, w, one, p, g) == (0, 1, 2, 3, 4, 5)
        return compile_circuit(c)

    def test_branch_off_zero_divisor_no_inverse_required(self):
        # b=0 且 d=0：0 没有模逆元，但分支关闭，约束不生效；
        # 见证照常生成（w 槽仍有明确赋值），审计通过。
        cc = self.build()
        z = generate_witness(cc, {"b": 0, "d": 0, "w": 55})
        self.assertTrue(audit(cc, z).ok)
        self.assertEqual(independent_audit(cc, z), [])
        expected = reference_eval(self.SPEC, {"b": 0, "d": 0, "w": 55})
        slot_of = {info.node: info.slot for info in cc.sources
                   if info.node is not None}
        for node in (0, 1, 2, 4, 5):
            self.assertEqual(z[slot_of[node]], expected[node])

    def test_branch_on_zero_divisor_rejected(self):
        # b=1 且 d=0：0*w=0 永远 != 1，任何 w 都必须被拒绝。
        cc = self.build()
        for w in (0, 1, 50, 96):
            with self.assertRaises(GuardedAssertError):
                generate_witness(cc, {"b": 1, "d": 0, "w": w})

    def test_branch_on_valid_inverse_accepted(self):
        # b=1 且 d=5：w 必须是 5 的模逆元 39（5*39 = 195 = 1 mod 97）。
        cc = self.build()
        z = generate_witness(cc, {"b": 1, "d": 5, "w": 39})
        self.assertTrue(audit(cc, z).ok)
        with self.assertRaises(GuardedAssertError):
            generate_witness(cc, {"b": 1, "d": 5, "w": 38})


class TestGuardedBuilderValidation(unittest.TestCase):
    def test_bad_references_rejected_without_partial_change(self):
        c = Circuit()
        b = c.input("b")
        x = c.input("x")
        with self.assertRaises(CircuitBuildError):
            c.guarded_assert(b, x, 99)
        with self.assertRaises(CircuitBuildError):
            c.guarded_assert(7, x, b)
        with self.assertRaises(TypeError):
            c.guarded_assert(b, True, x)  # type: ignore[arg-type]
        self.assertEqual(len(c), 2)  # 失败追加不留部分变更

    def test_witness_shape_fully_assigned(self):
        # 见证向量每个槽位都是规范域元素（无未初始化槽）。
        cc = compile_circuit(build_guard_circuit())
        z = generate_witness(cc, {"b": 0, "x": 1, "y": 2})
        self.assertEqual(len(z), cc.n_vars)
        for value in z:
            self.assertIsInstance(value, int)
            self.assertIn(value, range(P))


if __name__ == "__main__":
    unittest.main()
