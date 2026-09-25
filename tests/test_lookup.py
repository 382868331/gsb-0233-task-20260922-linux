"""lookup(value, table) 的契约与穷举健全性测试。

覆盖：
- 小域全部 97 个输入逐值枚举，接受集合恰好等于表；
- 见证生成填写连乘中间槽，篡改每一类中间槽（head/chain/输出）
  均被 audit 捕获，包括伪造中间值试图骗过非成员检查；
- 构建期拒绝：空表、重复表元素、非规范域值、超长表、非法类型；
- 含 0 的表、全相同输入、两个 lookup 共享同一张表但中间见证独立；
- 原 select 的布尔约束保持不变。

期望值由 tests.reference 的独立朴素解释器给出（不导入被测核心）。
"""

import unittest

from zkcirc import (
    P,
    Circuit,
    compile_circuit,
    generate_witness,
    audit,
    LookupTableError,
    LookupMembershipError,
    NonBooleanSelectError,
)

try:  # pragma: no cover
    from .reference import reference_eval
except ImportError:  # pragma: no cover
    from reference import reference_eval


def _slot_of(cc, node_id):
    return next(i.slot for i in cc.sources if i.node == node_id
                and i.kind != "lookup_aux")


class TestLookupTableValidation(unittest.TestCase):
    def test_empty_duplicate_oversized_and_noncanonical_rejected(self):
        c = Circuit()
        x = c.input("x")
        for bad in ([], [1, 1], [0, 5, 5], [2, 2, 2],
                    list(range(9)), [0] * 3):
            with self.assertRaises(LookupTableError, msg=f"bad={bad}"):
                c.lookup(x, bad)
        # 非规范域值：不做模规约，直接 ValueError。
        for bad in ([97], [-1], [96, 97], [0, -97]):
            with self.assertRaises(ValueError, msg=f"bad={bad}"):
                c.lookup(x, bad)
        # bool / float / NaN / Infinity / 其他类型。
        with self.assertRaises(TypeError):
            c.lookup(x, [True])
        with self.assertRaises(TypeError):
            c.lookup(x, [1.0])
        with self.assertRaises(ValueError):
            c.lookup(x, [float("nan")])
        with self.assertRaises(ValueError):
            c.lookup(x, [float("inf")])
        with self.assertRaises(TypeError):
            c.lookup(x, {1, 2})
        with self.assertRaises(TypeError):
            c.lookup(x, "12")
        # 失败不追加节点、不占用节点预算。
        self.assertEqual(len(c), 1)

    def test_bounds_one_and_eight_accepted(self):
        c = Circuit()
        n1 = c.lookup(c.input("a"), [7])
        n8 = c.lookup(c.input("b"), list(range(0, 16, 2)))
        cc = compile_circuit(c)
        self.assertEqual(len(cc.nodes[n1].table), 1)
        self.assertEqual(len(cc.nodes[n8].table), 8)

    def test_value_ref_validated(self):
        c = Circuit()
        with self.assertRaises(TypeError):
            c.lookup(True, [1])
        with self.assertRaises(Exception):
            c.lookup(99, [1])


class TestLookupAcceptedSet(unittest.TestCase):
    """对多张表枚举全部 97 个域值，核对接受集合恰好为表本身。"""

    TABLES = (
        [0],                    # 含 0 的单元素表
        [0, 1, 2],              # 含 0
        [42],                   # 非零单元素
        [5, 17, 50, 96],        # 一般表
        list(range(0, 16, 2)),  # 长度 8 上限
    )

    def _build(self, table):
        c = Circuit()
        x = c.input("x")
        node = c.lookup(x, table)
        spec = [
            {"kind": "input", "name": "x"},
            {"kind": "lookup", "inputs": (0,), "table": tuple(table)},
        ]
        return c, node, spec

    def test_enumerate_all_field_values(self):
        for table in self.TABLES:
            c, node, spec = self._build(table)
            cc = compile_circuit(c)
            members = set(table)
            for v in range(P):
                feeds = {"x": v}
                if v in members:
                    z = generate_witness(cc, feeds)
                    report = audit(cc, z)
                    self.assertTrue(
                        report.ok,
                        msg=f"table={table} v={v} fails: "
                            f"{[ (r.tag, r.lhs, r.rhs) for r in report.failures ]}",
                    )
                    # 输出值仍是输入 value 本身。
                    self.assertEqual(z[_slot_of(cc, node)], v)
                    # 与独立朴素解释器的逐节点值一致。
                    expected = reference_eval(spec, feeds)
                    self.assertEqual(z[cc.inputs["x"]], expected[0])
                    self.assertEqual(z[_slot_of(cc, node)], expected[1])
                else:
                    with self.assertRaises(LookupMembershipError) as ctx:
                        generate_witness(cc, feeds)
                    self.assertEqual(ctx.exception.node, node)
                    self.assertEqual(ctx.exception.value, v)

    def test_constant_member_and_nonmember_witness(self):
        # value 为常量节点：成员常量可生成，非成员常量必失败。
        c = Circuit()
        good = c.const(3)
        n = c.lookup(good, [1, 2, 3])
        cc = compile_circuit(c)
        z = generate_witness(cc, {})
        self.assertTrue(audit(cc, z).ok)
        self.assertEqual(z[_slot_of(cc, n)], 3)

        c2 = Circuit()
        c2.lookup(c2.const(4), [1, 2, 3])
        with self.assertRaises(LookupMembershipError):
            generate_witness(compile_circuit(c2), {})


class TestLookupIntermediateTamper(unittest.TestCase):
    """逐槽负例：每一类中间槽被改为任意其他域值都必须被审计发现。"""

    TABLES = ([0], [0, 1, 2], [5, 17, 50, 96], list(range(0, 16, 2)))
    VALUES = (0, 1, 2, 5, 50, 96)

    def test_every_slot_every_wrong_value_fails_audit(self):
        for table in self.TABLES:
            members = set(table)
            for v in self.VALUES:
                if v not in members:
                    continue
                c = Circuit()
                x = c.input("x")
                node = c.lookup(x, table)
                cc = compile_circuit(c)
                z = generate_witness(cc, {"x": v})
                slots = sorted(
                    info.slot for info in cc.sources
                    if info.node == node
                )
                for sidx in slots:
                    good = z[sidx]
                    for wrong in range(P):
                        if wrong == good:
                            continue
                        zz = z.copy()
                        zz[sidx] = wrong
                        report = audit(cc, zz)
                        self.assertFalse(
                            report.ok,
                            msg=(f"table={table} v={v} slot={sidx} "
                                 f"forged={wrong} was accepted"),
                        )
                        # 失败必须定位回该 lookup 节点。
                        self.assertIn(
                            node, {f.node for f in report.failures}
                        )

    def test_forged_aux_cannot_fake_membership(self):
        """非成员 value：无论怎样伪造连乘中间槽都不可能通过审计。

        对一个 k=3 的表、非成员 value，把 3 个中间槽各自枚举全部 97
        个域值（其余按合法见证填充），审计必须始终失败——这正是
        「不引入未约束的宿主布尔判断」的 R1CS 保证。
        """

        table = [7, 20, 42]
        c = Circuit()
        x = c.input("x")
        node = c.lookup(x, table)
        cc = compile_circuit(c)
        with self.assertRaises(LookupMembershipError):
            generate_witness(cc, {"x": 8})

        # 手工构造一份形状合法的见证：value=8（非成员），逐个枚举
        # 中间槽。先取一个成员见证作底盘，再改输入槽。
        base = generate_witness(cc, {"x": 7})
        x_slot = cc.inputs["x"]
        aux_slots = sorted(
            info.slot for info in cc.sources
            if info.node == node and info.kind == "lookup_aux"
        )
        out_slot = _slot_of(cc, node)
        self.assertEqual(len(aux_slots), 3)

        import itertools
        # 三个中间槽全枚举 97^3 代价过大；固定两个为合法底盘值，
        # 单槽枚举 97 值即可证明没有任何单个槽值能同时满足所有门。
        for target in aux_slots:
            for forged in range(P):
                zz = base.copy()
                zz[x_slot] = 8
                zz[out_slot] = 8
                zz[target] = forged
                self.assertFalse(
                    audit(cc, zz).ok,
                    msg=f"nonmember accepted with slot {target}={forged}",
                )
        # 再做一次小规模联合枚举（每槽抽样若干值），增加覆盖。
        sample = (0, 1, 7, 20, 42, 50, 96)
        for combo in itertools.product(sample, repeat=3):
            zz = base.copy()
            zz[x_slot] = 8
            zz[out_slot] = 8
            for s, val in zip(aux_slots, combo):
                zz[s] = val
            self.assertFalse(audit(cc, zz).ok)


class TestLookupSharedTable(unittest.TestCase):
    def test_same_table_shared_but_aux_per_lookup(self):
        c = Circuit()
        a = c.input("a")
        b = c.input("b")
        la = c.lookup(a, [1, 2, 3])
        lb = c.lookup(b, [3, 2, 1])  # 顺序不同 => 不同表结构
        lc = c.lookup(b, [1, 2, 3])  # 与 la 完全相同的表 => 共享对象
        self.assertIs(c.get_node(la).table, c.get_node(lc).table)
        self.assertIsNot(c.get_node(la).table, c.get_node(lb).table)
        cc = compile_circuit(c)

        # 两个 lookup 即使共享表，中间槽也完全独立。
        aux_a = sorted(s.slot for s in cc.sources
                       if s.node == la and s.kind == "lookup_aux")
        aux_c = sorted(s.slot for s in cc.sources
                       if s.node == lc and s.kind == "lookup_aux")
        self.assertTrue(set(aux_a).isdisjoint(aux_c))

        # 同表、不同 value（全相同输入的对偶：a=1,b=2）。
        z = generate_witness(cc, {"a": 1, "b": 2})
        self.assertTrue(audit(cc, z).ok)
        self.assertEqual(z[_slot_of(cc, la)], 1)
        self.assertEqual(z[_slot_of(cc, lc)], 2)
        # 连乘中间值因 value 不同而不同（m0 = value - 1）。
        self.assertEqual(z[aux_a[0]], 0)       # 1 - 1
        self.assertEqual(z[aux_c[0]], 1)       # 2 - 1

        # 全相同输入：a=b=3，两个 lookup 都合法。
        z2 = generate_witness(cc, {"a": 3, "b": 3})
        self.assertTrue(audit(cc, z2).ok)

        # 把 la 的中间槽错误地共享（复制 lc 的不同 value 结果）必被抓。
        z3 = generate_witness(cc, {"a": 1, "b": 2})
        caught = False
        for sa, sc in zip(aux_a, aux_c):
            zz = z3.copy()
            zz[sa] = z3[sc]
            if not audit(cc, zz).ok:
                caught = True
        # 至少一个错误共享的中间槽被门约束抓住（m0: 1-1=0 vs 2-1=1）。
        self.assertTrue(caught)


class TestSelectUnchanged(unittest.TestCase):
    def test_select_booleanity_still_present(self):
        c = Circuit()
        b, x = c.input("b"), c.input("x")
        sel = c.select(b, x, c.const(0))
        node = c.lookup(sel, [0, 1])
        cc = compile_circuit(c)
        tags = {con.tag for con in cc.constraints}
        self.assertIn("select_value", tags)
        self.assertIn("select_booleanity", tags)
        self.assertIn("lookup_membership", tags)

        for bv in (0, 1):
            z = generate_witness(cc, {"b": bv, "x": bv})
            self.assertTrue(audit(cc, z).ok)
            self.assertEqual(z[_slot_of(cc, node)], bv)
        with self.assertRaises(NonBooleanSelectError):
            generate_witness(cc, {"b": 2, "x": 0})


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
