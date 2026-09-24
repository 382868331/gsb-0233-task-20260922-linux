"""2..8 位有符号整数（二补码）加减与比较的测试。

期望值来源（不调用被测核心生成）:
- tests.reference.ref_eval_signed：独立朴素解释器，逐节点给出有符号值、
  小端比特、标准进位/借位序列、逐位同或与与链；
- 手算例子与解析关系（如 7+1=-8、符号位翻转后的无符号序、
  全加/全减器方程）；
- 小位宽（w=2/3/4）对全部 2^w 个输入值做确定性全枚举。

健全性：对每个见证槽枚举全部 97 个域值做单点篡改，审计必须拒绝
（每个比特槽都有 b*(b-1)=0 布尔性约束，进位/借位由逐位全加/全减
关系钉住，字槽由 word=Σ2^k·b_k 钉住，比较标志由链/最高借位钉住）。
"""

import unittest

from zkcirc import (
    P,
    Circuit,
    compile_circuit,
    generate_witness,
    audit,
    MAX_NODES,
    MIN_SIGNED_WIDTH,
    MAX_SIGNED_WIDTH,
    signed_range,
    signed_to_bits,
    bits_to_signed,
    wrap_signed,
    SignedInputError,
    UnknownInputError,
    UnexpectedInputError,
)
from zkcirc.errors import CircuitBuildError, CircuitLimitError, AuditError

try:  # pragma: no cover - 取决于 unittest 的发现方式
    from .reference import ref_eval_signed, reference_check_constraint
except ImportError:  # pragma: no cover
    from reference import ref_eval_signed, reference_check_constraint


# ---------------------------------------------------------------------------
# 手算期望值（独立于 zkcirc 实现）
# ---------------------------------------------------------------------------

def hand_wrap(value: int, w: int) -> int:
    bias = 1 << (w - 1)
    return ((value + bias) % (1 << w)) - bias


def hand_bits(value: int, w: int) -> tuple[int, ...]:
    return tuple((value >> k) & 1 for k in range(w))


def unsigned_word(svalue: int, w: int) -> int:
    return svalue % (1 << w)


# ---------------------------------------------------------------------------
# field 有符号工具
# ---------------------------------------------------------------------------

class TestSignedFieldHelpers(unittest.TestCase):
    def test_width_bounds(self):
        self.assertEqual((MIN_SIGNED_WIDTH, MAX_SIGNED_WIDTH), (2, 8))
        self.assertEqual(signed_range(2), (-2, 1))
        self.assertEqual(signed_range(3), (-4, 3))
        self.assertEqual(signed_range(8), (-128, 127))

    def test_width_validation(self):
        from zkcirc.field import check_width
        for bad in (1, 9, 0, -2):
            with self.assertRaises(ValueError):
                check_width(bad)
        for bad in (True, 3.0, "3", None):
            with self.assertRaises(TypeError):
                check_width(bad)
        for w in range(2, 9):
            self.assertEqual(check_width(w), w)

    def test_bits_roundtrip_and_hand_values(self):
        self.assertEqual(signed_to_bits(-1, 4), (1, 1, 1, 1))
        self.assertEqual(signed_to_bits(-8, 4), (0, 0, 0, 1))
        self.assertEqual(signed_to_bits(7, 4), (1, 1, 1, 0))
        self.assertEqual(signed_to_bits(-128, 8)[7], 1)
        for w in range(2, 9):
            low, high = signed_range(w)
            for v in (low, -1, 0, 1, high):
                bits = signed_to_bits(v, w)
                self.assertEqual(len(bits), w)
                self.assertTrue(all(b in (0, 1) for b in bits))
                self.assertEqual(bits_to_signed(bits, w), v)

    def test_bits_reject_out_of_range(self):
        with self.assertRaises(ValueError):
            signed_to_bits(4, 3)
        with self.assertRaises(ValueError):
            signed_to_bits(-5, 3)

    def test_wrap_hand_examples(self):
        self.assertEqual(wrap_signed(8, 4), -8)     # 7+1 回绕
        self.assertEqual(wrap_signed(-9, 4), 7)     # -8-1 回绕
        self.assertEqual(wrap_signed(128, 8), -128)
        self.assertEqual(wrap_signed(-129, 8), 127)
        self.assertEqual(wrap_signed(3, 3), 3)


# ---------------------------------------------------------------------------
# 构建器契约
# ---------------------------------------------------------------------------

class TestSignedBuilder(unittest.TestCase):
    def test_invalid_widths_rejected(self):
        c = Circuit()
        for bad in (1, 9, 0, -3):
            with self.assertRaises(ValueError):
                c.signed_input("x", bad)
        for bad in (True, 2.0, "3"):
            with self.assertRaises(TypeError):
                c.signed_input("x", bad)

    def test_signed_const_range(self):
        c = Circuit()
        c.signed_const(-128, 8)
        c.signed_const(127, 8)
        c.signed_const(-4, 3)
        for bad in (-5, 4):
            with self.assertRaises(ValueError, msg=f"bad={bad}"):
                c.signed_const(bad, 3)
        for bad in (True, 1.0, "0"):
            with self.assertRaises(TypeError):
                c.signed_const(bad, 3)

    def test_operand_must_be_signed_value_and_same_width(self):
        c = Circuit()
        a3 = c.signed_input("a", 3)
        b4 = c.signed_input("b", 4)
        x = c.input("x")
        k = c.const(1)
        for build in (
            lambda: c.sadd(a3, b4),   # 宽度不同
            lambda: c.ssub(b4, a3),
            lambda: c.slt(a3, b4),
            lambda: c.sle(a3, b4),
            lambda: c.seq(a3, b4),
            lambda: c.sadd(a3, x),    # 旧域输入
            lambda: c.slt(x, a3),
            lambda: c.seq(a3, k),     # 旧域常量
        ):
            with self.assertRaises(CircuitBuildError):
                build()

    def test_compare_flag_is_not_a_signed_value(self):
        c = Circuit()
        a = c.signed_input("a", 3)
        f = c.slt(a, c.signed_const(0, 3))
        with self.assertRaises(CircuitBuildError):
            c.sadd(f, a)
        with self.assertRaises(CircuitBuildError):
            c.ssub(a, f)

    def test_name_space_shared_and_no_partial_change(self):
        c = Circuit()
        c.input("x")
        n0 = len(c)
        with self.assertRaises(CircuitBuildError):
            c.signed_input("x", 3)  # 与旧输入重名
        self.assertEqual(len(c), n0)
        c.signed_input("y", 3)
        with self.assertRaises(CircuitBuildError):
            c.input("y")
        self.assertEqual(len(c), n0 + 1)

    def test_node_limit_covers_signed_nodes(self):
        c = Circuit()
        # signed_input 占 1 个 DAG 节点（尽管见证上展开为 w+1 个槽）。
        for _ in range(MAX_NODES):
            c.signed_const(0, 2)
        with self.assertRaises(CircuitLimitError):
            c.signed_input("late", 2)
        self.assertEqual(len(c), MAX_NODES)

    def test_back_reference_rule_unchanged(self):
        c = Circuit()
        with self.assertRaises(CircuitBuildError):
            c.sadd(0, 1)


# ---------------------------------------------------------------------------
# 电路与独立规格的联合构建（索引一一对应）
# ---------------------------------------------------------------------------

def build_composite(width: int):
    """a,b 上的复合电路：add/sub/lt/le/eq 全部包含。"""

    c = Circuit()
    a = c.signed_input("a", width)
    b = c.signed_input("b", width)
    add = c.sadd(a, b)
    sub = c.ssub(a, b)
    lt = c.slt(a, b)
    le = c.sle(a, b)
    eq = c.seq(a, b)
    spec = [
        {"kind": "signed_input", "name": "a", "width": width},
        {"kind": "signed_input", "name": "b", "width": width},
        {"kind": "sadd", "inputs": (0, 1), "width": width},
        {"kind": "ssub", "inputs": (0, 1), "width": width},
        {"kind": "slt", "inputs": (0, 1), "width": width},
        {"kind": "sle", "inputs": (0, 1), "width": width},
        {"kind": "seq", "inputs": (0, 1), "width": width},
    ]
    assert (a, b, add, sub, lt, le, eq) == (0, 1, 2, 3, 4, 5, 6)
    return c, spec, (a, b, add, sub, lt, le, eq)


def build_chain_circuit(width: int):
    """链式：t = sadd(a,b); u = ssub(t,a); f = seq(u,b); g = slt(t,b)。"""

    c = Circuit()
    a = c.signed_input("a", width)
    b = c.signed_input("b", width)
    t = c.sadd(a, b)
    u = c.ssub(t, a)   # 恒等于 b（回绕下仍成立，因为 t-a ≡ b mod 2^w）
    f = c.seq(u, b)    # 恒为 1
    g = c.slt(t, b)
    spec = [
        {"kind": "signed_input", "name": "a", "width": width},
        {"kind": "signed_input", "name": "b", "width": width},
        {"kind": "sadd", "inputs": (0, 1), "width": width},
        {"kind": "ssub", "inputs": (2, 0), "width": width},
        {"kind": "seq", "inputs": (3, 1), "width": width},
        {"kind": "slt", "inputs": (2, 1), "width": width},
    ]
    return c, spec, (a, b, t, u, f, g)


# ---------------------------------------------------------------------------
# 小位宽全枚举：逐槽对照独立参考 + 独立点积
# ---------------------------------------------------------------------------

class TestSignedFullEnumeration(unittest.TestCase):
    def _check_against_reference(self, cc, spec, feeds):
        z = generate_witness(cc, feeds)
        ref = ref_eval_signed(spec, feeds)
        report = audit(cc, z)
        self.assertTrue(report.ok, msg=[
            (r.index, r.tag, r.lhs, r.rhs)
            for r in report.results if not r.satisfied
        ][:5])

        # 独立点积逐条复算。
        for con in cc.constraints:
            ok, lhs, rhs = reference_check_constraint(con.a, con.b, con.c, z)
            self.assertTrue(ok, msg=(feeds, con.index, con.tag, lhs, rhs))

        for nd_id, detail in enumerate(ref):
            node = cc.nodes[nd_id]
            w = node.width
            if node.kind in ("sadd", "ssub", "signed_input", "signed_const"):
                lay = cc.signed_layouts[nd_id]
                # 字槽 = 二补码无符号字 mod 97。
                self.assertEqual(
                    z[lay.word_slot], unsigned_word(detail["value"], w) % P,
                    msg=(feeds, nd_id),
                )
                # 每个比特槽逐一对照参考。
                for k, bs in enumerate(lay.bit_slots):
                    self.assertEqual(z[bs], detail["bits"][k],
                                     msg=(feeds, nd_id, k))
                if detail["carries"]:
                    self.assertEqual(
                        tuple(z[s] for s in lay.carry_slots),
                        detail["carries"],
                    )
                if detail["borrows"]:
                    self.assertEqual(
                        tuple(z[s] for s in lay.carry_slots),
                        detail["borrows"],
                    )
            else:
                lay = cc.signed_cmp_layouts[nd_id]
                self.assertEqual(z[lay.flag_slot], detail["value"])
                if node.kind in ("slt", "sle"):
                    self.assertEqual(
                        tuple(z[s] for s in lay.diff_bits),
                        detail["diff_bits"],
                    )
                    self.assertEqual(
                        tuple(z[s] for s in lay.borrows),
                        detail["borrows"],
                    )
                else:
                    self.assertEqual(
                        tuple(z[s] for s in lay.eq_prod), detail["xnor"])
                    self.assertEqual(
                        tuple(z[s] for s in lay.eq_chain), detail["chain"])
        return z

    def test_widths_2_3_4_full_enumeration(self):
        for w in (2, 3, 4):
            c, spec, _ = build_composite(w)
            cc = compile_circuit(c)
            low, high = signed_range(w)
            for av in range(low, high + 1):
                for bv in range(low, high + 1):
                    feeds = {"a": av, "b": bv}
                    self._check_against_reference(cc, spec, feeds)

    def test_chain_identity_width_3(self):
        # 解析关系：wrap(wrap(a+b)-a) == b，故 seq(ssub(sadd(a,b),a),b) 恒 1。
        c, spec, ids = build_chain_circuit(3)
        cc = compile_circuit(c)
        _, _, _, _, f, _ = ids
        for av in range(-4, 4):
            for bv in range(-4, 4):
                feeds = {"a": av, "b": bv}
                z = self._check_against_reference(cc, spec, feeds)
                self.assertEqual(z[cc.signed_cmp_layouts[f].flag_slot], 1)

    def test_compare_flags_match_python_semantics_all_widths(self):
        for w in range(2, 9):
            c, spec, _ = build_composite(w)
            cc = compile_circuit(c)
            low, high = signed_range(w)
            # 全枚举在 w<=4 做；w>4 取边界与解析代表点。
            if w <= 4:
                values = range(low, high + 1)
            else:
                values = (low, low + 1, -2, -1, 0, 1, 2, high - 1, high)
            for av in values:
                for bv in values:
                    z = generate_witness(cc, {"a": av, "b": bv})
                    self.assertTrue(audit(cc, z).ok)
                    self.assertEqual(
                        z[cc.signed_cmp_layouts[4].flag_slot], int(av < bv))
                    self.assertEqual(
                        z[cc.signed_cmp_layouts[5].flag_slot], int(av <= bv))
                    self.assertEqual(
                        z[cc.signed_cmp_layouts[6].flag_slot], int(av == bv))


# ---------------------------------------------------------------------------
# 手算边界与回绕
# ---------------------------------------------------------------------------

class TestHandComputedBoundaries(unittest.TestCase):
    def test_wraparound_hand_examples(self):
        c = Circuit()
        a = c.signed_input("a", 4)
        b = c.signed_input("b", 4)
        add = c.sadd(a, b)
        sub = c.ssub(a, b)
        cc = compile_circuit(c)

        # (a, b, wrap(a+b), wrap(a-b))，全部手算。
        cases = [
            (7, 1, -8, 6),
            (-8, -1, 7, -7),
            (-8, 1, -7, 7),
            (7, 7, -2, 0),
            (-8, -8, 0, 0),
            (1, -2, -1, 3),
        ]
        for av, bv, es, ed in cases:
            z = generate_witness(cc, {"a": av, "b": bv})
            self.assertTrue(audit(cc, z).ok)
            self.assertEqual(
                z[cc.signed_layouts[add].word_slot], unsigned_word(es, 4),
                msg=(av, bv),
            )
            self.assertEqual(
                z[cc.signed_layouts[sub].word_slot], unsigned_word(ed, 4),
                msg=(av, bv),
            )
            # 独立手算复核。
            self.assertEqual(hand_wrap(av + bv, 4), es)
            self.assertEqual(hand_wrap(av - bv, 4), ed)

    def test_width_8_extremes(self):
        c = Circuit()
        a = c.signed_input("a", 8)
        b = c.signed_input("b", 8)
        add, sub = c.sadd(a, b), c.ssub(a, b)
        cc = compile_circuit(c)
        # (a, b, wrap(a+b), wrap(a-b))，全部手算。
        cases = [
            (127, 1, -128, 126),
            (-128, -1, 127, -127),
            (127, 127, -2, 0),
            (-128, 127, -1, 1),      # 255 -> -1；-255 -> 1
            (0, -128, -128, -128),   # 128 回绕为 -128
        ]
        for av, bv, es, ed in cases:
            z = generate_witness(cc, {"a": av, "b": bv})
            self.assertTrue(audit(cc, z).ok, msg=(av, bv))
            self.assertEqual(z[cc.signed_layouts[add].word_slot],
                             unsigned_word(es, 8) % P)
            self.assertEqual(z[cc.signed_layouts[sub].word_slot],
                             unsigned_word(ed, 8) % P)

    def test_signed_comparison_boundary_sign_matters(self):
        c = Circuit()
        a = c.signed_input("a", 4)
        b = c.signed_input("b", 4)
        lt, le, eq = c.slt(a, b), c.sle(a, b), c.seq(a, b)
        cc = compile_circuit(c)
        # -1 < 1（有符号）；无符号口径下 15 > 1，必须区分。
        z = generate_witness(cc, {"a": -1, "b": 1})
        self.assertEqual(z[cc.signed_cmp_layouts[lt].flag_slot], 1)
        self.assertEqual(z[cc.signed_cmp_layouts[le].flag_slot], 1)
        self.assertEqual(z[cc.signed_cmp_layouts[eq].flag_slot], 0)
        # -8 最小，7 最大。
        z = generate_witness(cc, {"a": -8, "b": 7})
        self.assertEqual(z[cc.signed_cmp_layouts[lt].flag_slot], 1)
        z = generate_witness(cc, {"a": 7, "b": -8})
        self.assertEqual(z[cc.signed_cmp_layouts[lt].flag_slot], 0)
        self.assertEqual(z[cc.signed_cmp_layouts[le].flag_slot], 0)
        # 相等时 lt=0, le=1, eq=1。
        z = generate_witness(cc, {"a": -3, "b": -3})
        self.assertEqual(z[cc.signed_cmp_layouts[lt].flag_slot], 0)
        self.assertEqual(z[cc.signed_cmp_layouts[le].flag_slot], 1)
        self.assertEqual(z[cc.signed_cmp_layouts[eq].flag_slot], 1)

    def test_constant_operands_hand_values(self):
        c = Circuit()
        x = c.signed_input("x", 4)
        k5 = c.signed_const(5, 4)
        add = c.sadd(k5, x)
        sub = c.ssub(k5, x)
        eq_t = c.seq(k5, c.signed_const(5, 4))
        eq_f = c.seq(k5, c.signed_const(6, 4))
        cc = compile_circuit(c)
        z = generate_witness(cc, {"x": -8})
        self.assertEqual(z[cc.signed_layouts[add].word_slot],
                         unsigned_word(hand_wrap(5 + (-8), 4), 4))  # -3 -> 13
        self.assertEqual(z[cc.signed_layouts[add].word_slot], 13)
        self.assertEqual(z[cc.signed_layouts[sub].word_slot],
                         unsigned_word(hand_wrap(5 - (-8), 4), 4))  # 13 -> 13
        self.assertEqual(z[cc.signed_cmp_layouts[eq_t].flag_slot], 1)
        self.assertEqual(z[cc.signed_cmp_layouts[eq_f].flag_slot], 0)
        self.assertTrue(audit(cc, z).ok)


# ---------------------------------------------------------------------------
# 约束结构：确有逐位布尔性与进位约束，而非只有域运算
# ---------------------------------------------------------------------------

class TestConstraintStructure(unittest.TestCase):
    def setUp(self):
        c, _, _ = build_composite(3)
        self.cc = compile_circuit(c)

    def test_tag_presence(self):
        tags = [con.tag for con in self.cc.constraints]
        for tag in ("sbit_booleanity", "signed_word", "sadd_bit",
                    "ssub_bit", "signed_cmp_bit", "signed_carry0",
                    "signed_borrow0",
                    "scarry_booleanity", "signed_flag",
                    "seq_prod", "seq_chain", "signed_pin"):
            self.assertIn(tag, tags, msg=tag)

    def test_booleanity_constraint_is_quadratic_bb_minus_b(self):
        con = next(con for con in self.cc.constraints
                   if con.tag == "sbit_booleanity")
        # A = b, B = b - 1, C = 0；稀疏项按槽位升序，常数槽 0 在前。
        self.assertEqual(con.a, ((con.a[0][0], 1),))
        self.assertEqual(con.b, ((0, P - 1), (con.a[0][0], 1)))
        self.assertEqual(con.c, ())
        # 独立解析：b*(b-1) 只在 b∈{0,1} 为 0。
        for bv in range(P):
            ok, _, _ = reference_check_constraint(
                con.a, con.b, con.c, _z_with(self.cc, con.a[0][0], bv)
            )
            self.assertEqual(ok, bv in (0, 1))

    def test_full_adder_relation_shape(self):
        # sadd node 2 的逐位关系：1 * s_k = x_k + y_k + c_k - 2 c_{k+1}。
        # A 恒为常数 1，B 只有结果位（系数 1），C 是三操作数与 -2 进位。
        con = next(con for con in self.cc.constraints if con.tag == "sadd_bit")
        self.assertEqual(con.a, ((0, 1),))
        self.assertEqual(len(con.b), 1)
        self.assertEqual(con.b[0][1], 1)             # 结果位系数 +1
        coeffs = dict(con.c)
        self.assertNotIn(con.b[0][0], coeffs)        # 结果位不出现在 C 中
        self.assertEqual(list(coeffs.values()).count(1), 3)  # x_k, y_k, c_k
        self.assertIn(-2 % P, coeffs.values())       # 下一进位系数 -2

    def test_full_subtractor_relation_shape(self):
        # ssub node 3：1 * d_k = x_k - y_k - r_k + 2 r_{k+1}。
        con = next(con for con in self.cc.constraints if con.tag == "ssub_bit")
        self.assertEqual(con.a, ((0, 1),))
        self.assertEqual(len(con.b), 1)
        self.assertEqual(con.b[0][1], 1)             # 差值位系数 +1
        coeffs = dict(con.c)
        self.assertNotIn(con.b[0][0], coeffs)
        self.assertIn(2, coeffs.values())            # 下一借位系数 +2
        self.assertIn(P - 1, coeffs.values())        # -1 系数

    def test_source_mapping_layouts(self):
        cc = self.cc
        # 每个有符号值节点都有布局；位槽可反查到节点与角色。
        for nd_id, lay in cc.signed_layouts.items():
            self.assertEqual(len(lay.bit_slots), cc.nodes[nd_id].width)
            for bs in lay.bit_slots:
                info = cc.source_of(bs)
                self.assertEqual(info.node, nd_id)
                self.assertEqual(info.kind, "signed_bit")
        # signed_input 的字槽就是命名输入槽。
        self.assertEqual(cc.inputs["a"], cc.signed_layouts[0].word_slot)
        self.assertEqual(cc.signed_inputs, {"a": 3, "b": 3})
        # 字槽来源为 input，位槽来源为 intermediate。
        self.assertEqual(cc.source_of(cc.inputs["a"]).role, "input")
        self.assertTrue(all(
            cc.source_of(s).role == "intermediate"
            for s in cc.signed_layouts[0].bit_slots
        ))
        # 比较布局的标志位与逐位辅助槽齐全。
        for nd_id, lay in cc.signed_cmp_layouts.items():
            w = cc.nodes[nd_id].width
            if cc.nodes[nd_id].kind in ("slt", "sle"):
                self.assertEqual(len(lay.diff_bits), w)
                self.assertEqual(len(lay.borrows), w + 1)
            else:
                self.assertEqual(len(lay.eq_prod), w)
                self.assertEqual(len(lay.eq_chain), w)


def _z_with(cc, slot, value):
    z = [0] * cc.n_vars
    z[0] = 1
    z[slot] = value
    return z


# ---------------------------------------------------------------------------
# 健全性：逐槽全 97 值单点篡改必被拒
# ---------------------------------------------------------------------------

class TestSignedTamperSoundness(unittest.TestCase):
    def test_every_slot_every_wrong_value_rejected_width_3(self):
        c, _, _ = build_composite(3)
        cc = compile_circuit(c)
        z = generate_witness(cc, {"a": -2, "b": 3})
        self.assertTrue(audit(cc, z).ok)
        for slot in range(1, cc.n_vars):
            good = z[slot]
            for wrong in range(P):
                if wrong == good:
                    continue
                zz = z.copy()
                zz[slot] = wrong
                report = audit(cc, zz)
                self.assertFalse(
                    report.ok,
                    msg=f"slot {slot} ({cc.source_of(slot)}) tampered to "
                        f"{wrong} unexpectedly accepted",
                )

    def test_input_bit_tamper_is_pinned_to_word(self):
        # 只改某个输入比特而不改字槽：signed_word 约束必失败并定位到输入节点。
        c, _, _ = build_composite(3)
        cc = compile_circuit(c)
        z = generate_witness(cc, {"a": 1, "b": 2})
        bit_slot = cc.signed_layouts[0].bit_slots[0]
        zz = z.copy()
        zz[bit_slot] = 1 - zz[bit_slot]
        report = audit(cc, zz)
        self.assertFalse(report.ok)
        self.assertIn(0, {f.node for f in report.failures})
        self.assertIn("signed_word", [f.tag for f in report.failures])

    def test_carry_tamper_breaks_adjacent_bit_relation(self):
        c, _, _ = build_composite(3)
        cc = compile_circuit(c)
        z = generate_witness(cc, {"a": -4, "b": 3})  # 触发进位
        carry = cc.signed_layouts[2].carry_slots[1]
        zz = z.copy()
        zz[carry] = 1 - zz[carry]
        report = audit(cc, zz)
        self.assertFalse(report.ok)
        self.assertTrue(any(
            f.node == 2 and f.tag in ("sadd_bit", "scarry_booleanity")
            for f in report.failures
        ))

    def test_flag_tamper_rejected(self):
        c, _, ids = build_composite(3)
        _, _, _, _, lt, _, _ = ids
        cc = compile_circuit(c)
        z = generate_witness(cc, {"a": 0, "b": 1})  # lt=1
        flag = cc.signed_cmp_layouts[lt].flag_slot
        zz = z.copy()
        zz[flag] = 0
        self.assertFalse(audit(cc, zz).ok)
        # 非布尔值也必被布尔性约束拒绝。
        zz[flag] = 2
        self.assertFalse(audit(cc, zz).ok)


# ---------------------------------------------------------------------------
# 见证输入错误
# ---------------------------------------------------------------------------

class TestSignedWitnessInputErrors(unittest.TestCase):
    def setUp(self):
        c = Circuit()
        a = c.signed_input("a", 3)
        self.add = c.sadd(a, c.signed_const(1, 3))
        self.cc = compile_circuit(c)

    def test_out_of_range_raises_signed_input_error(self):
        for bad in (4, -5, 100, -100):
            with self.assertRaises(SignedInputError) as ctx:
                generate_witness(self.cc, {"a": bad})
            self.assertEqual(ctx.exception.name, "a")
            self.assertEqual(ctx.exception.width, 3)
            self.assertEqual((ctx.exception.low, ctx.exception.high), (-4, 3))
            self.assertEqual(ctx.exception.value, bad)
            self.assertEqual(ctx.exception.kind, "range")

    def test_type_errors_match_global_contract(self):
        with self.assertRaises(TypeError):
            generate_witness(self.cc, {"a": True})
        with self.assertRaises(TypeError):
            generate_witness(self.cc, {"a": 1.5})
        with self.assertRaises(TypeError):
            generate_witness(self.cc, {"a": "1"})
        with self.assertRaises(TypeError):
            generate_witness(self.cc, {"a": None})
        with self.assertRaises(ValueError):
            generate_witness(self.cc, {"a": float("nan")})
        with self.assertRaises(ValueError):
            generate_witness(self.cc, {"a": float("inf")})

    def test_in_range_negative_accepted(self):
        z = generate_witness(self.cc, {"a": -4})
        self.assertTrue(audit(self.cc, z).ok)

    def test_missing_and_extra(self):
        with self.assertRaises(UnknownInputError):
            generate_witness(self.cc, {})
        with self.assertRaises(UnexpectedInputError):
            generate_witness(self.cc, {"a": 1, "q": 2})

    def test_no_partial_witness_on_failure(self):
        # 多个有符号输入时，后一个非法必须整体失败，不返回任何见证。
        c = Circuit()
        c.signed_input("a", 3)
        c.signed_input("b", 3)
        cc = compile_circuit(c)
        with self.assertRaises(SignedInputError):
            generate_witness(cc, {"a": 0, "b": 99})

    def test_audit_shape_rules_apply_to_aux_slots(self):
        z = generate_witness(self.cc, {"a": 0})
        zz = z.copy()
        lay = self.cc.signed_layouts[self.add]
        zz[lay.bit_slots[0]] = 97
        with self.assertRaises(AuditError):
            audit(self.cc, zz)


class TestWidth7WordMod97Behavior(unittest.TestCase):
    """w≥7 时无符号字节可能超过 p-1；字槽是 Σ2^k b_k (mod 97)。

    这些测试锁定 README「已知限制」中记录的精确边界行为。
    """

    def test_unconsumed_w8_input_allows_congruent_decomposition(self):
        # 无任何消费者的 w=8 输入：字槽 0 同时接受比特 u=0 与 u=97。
        c = Circuit()
        a = c.signed_input("a", 8)
        cc = compile_circuit(c)
        z = generate_witness(cc, {"a": 0})      # u=0，全零比特
        lay = cc.signed_layouts[a]
        self.assertEqual(z[lay.word_slot], 0)
        zz = z.copy()
        for k in range(8):
            zz[lay.bit_slots[k]] = (97 >> k) & 1  # 另一组 0/1 比特，u=97
        # 单点篡改必被抓，但这条多槽一致的替代分解恰好满足 word 约束。
        self.assertTrue(audit(cc, zz).ok)

    def test_consumed_w8_input_pins_bits_via_carry_chain(self):
        # 同样的替代分解一旦进入 sadd 进位链即被拒绝。
        c = Circuit()
        x = c.signed_input("x", 8)
        s = c.sadd(x, c.signed_const(0, 8))
        cc = compile_circuit(c)
        z = generate_witness(cc, {"x": 0})
        lay = cc.signed_layouts[x]
        zz = z.copy()
        for k in range(8):
            zz[lay.bit_slots[k]] = (97 >> k) & 1
        report = audit(cc, zz)
        self.assertFalse(report.ok)
        self.assertIn(s, {f.node for f in report.failures})

    def test_w6_word_is_unique_even_unconsumed(self):
        # w=6 字 0..63 < 97：任何非零 0/1 比特分解都与字槽 0 不同余。
        c = Circuit()
        a = c.signed_input("a", 6)
        cc = compile_circuit(c)
        z = generate_witness(cc, {"a": 0})      # u=0
        lay = cc.signed_layouts[a]
        for mask in range(1, 1 << 6):
            zz = z.copy()
            for k in range(6):
                zz[lay.bit_slots[k]] = (mask >> k) & 1
            self.assertFalse(audit(cc, zz).ok, msg=f"mask={mask}")


# ---------------------------------------------------------------------------
# 与旧能力混用
# ---------------------------------------------------------------------------

class TestLegacyInterop(unittest.TestCase):
    def test_compare_flag_drives_legacy_select(self):
        c = Circuit()
        a = c.signed_input("a", 3)
        b = c.signed_input("b", 3)
        f = c.slt(a, b)
        sel = c.select(f, c.const(10), c.const(0))
        out = c.mul(sel, c.const(2))
        cc = compile_circuit(c)
        z1 = generate_witness(cc, {"a": 1, "b": 2})
        self.assertTrue(audit(cc, z1).ok)
        self.assertEqual(z1[_slot_of(cc, out)], 20)
        z2 = generate_witness(cc, {"a": 2, "b": 1})
        self.assertTrue(audit(cc, z2).ok)
        self.assertEqual(z2[_slot_of(cc, out)], 0)

    def test_assert_equal_on_signed_words_width_3(self):
        # w=3 时无符号字 0..7 < 97，字槽相等 iff 有符号相等。
        from zkcirc import AssertEqualError
        c = Circuit()
        a = c.signed_input("a", 3)
        b = c.signed_input("b", 3)
        t = c.sadd(a, b)
        node = c.assert_equal(t, c.signed_const(-1, 3))  # 要求 a+b 回绕为 -1
        cc = compile_circuit(c)
        # 1+2=3 != -1；3+3 回绕为 -2，都不成立。
        with self.assertRaises(AssertEqualError):
            generate_witness(cc, {"a": 1, "b": 2})
        with self.assertRaises(AssertEqualError):
            generate_witness(cc, {"a": 3, "b": 3})
        # -4+3=-1（无溢出），断言成立。
        z = generate_witness(cc, {"a": -4, "b": 3})
        self.assertTrue(audit(cc, z).ok)
        self.assertEqual(z[_slot_of(cc, node)], unsigned_word(-1, 3))

    def test_legacy_circuit_unchanged_layout(self):
        # 旧电路的编译产物不新增任何有符号布局。
        c = Circuit()
        x = c.input("x")
        c.add(x, c.const(1))
        cc = compile_circuit(c)
        self.assertEqual(dict(cc.signed_inputs), {})
        self.assertEqual(dict(cc.signed_layouts), {})
        self.assertEqual(dict(cc.signed_cmp_layouts), {})


def _slot_of(cc, node_id):
    return next(i.slot for i in cc.sources if i.node == node_id)



if __name__ == "__main__":  # pragma: no cover
    unittest.main()
