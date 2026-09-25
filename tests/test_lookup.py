"""lookup(value, table) 成员约束的专项测试。

覆盖契约：
- 小域 p=97 上逐值枚举（0..96）：见证生成成功当且仅当 value 属于表；
  成功见证的 audit 必须全部通过，且输出槽 == value。
- 含 0 表、全相同输入、两个 lookup 共享同一张表。
- 重复表元素 / 空表 / 非规范域值在构建期拒绝。
- 每类中间槽（lookup 输出槽与连乘链上每个 lookup_aux 槽）逐个、
  逐域值篡改，audit 必须发现；伪造「全 0 中间值」也无法蒙混。
- 共享表时常量结构相同，但两个 lookup 的中间见证槽互不共享。

期望值用朴素模运算独立计算（reference.reference_eval 不导入被测核心）。
"""

import unittest

from zkcirc import (
    P,
    Circuit,
    compile_circuit,
    generate_witness,
    audit,
    LookupMissError,
)
from zkcirc.errors import CircuitBuildError

try:  # pragma: no cover
    from .reference import reference_eval
except ImportError:  # pragma: no cover
    from reference import reference_eval


TABLES = [
    [0],                      # 含 0 的单元素表
    [0, 1],                  # 含 0 表
    [0, 5, 10],
    [7, 42, 96, 0],
    [10, 20, 30, 40, 50],
    [1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [10, 20, 30, 40, 50, 60, 70, 80],  # 最长 8 元素
]


def slot_of_node(cc, node_id):
    return next(
        i.slot for i in cc.sources
        if i.node == node_id and i.kind != "lookup_aux"
    )


def aux_slots(cc, node_id):
    return [i.slot for i in cc.sources
            if i.node == node_id and i.kind == "lookup_aux"]


class TestLookupAcceptSetExhaustive(unittest.TestCase):
    def test_every_field_value_accepted_iff_in_table(self):
        for table in TABLES:
            with self.subTest(table=table):
                c = Circuit()
                x = c.input("x")
                lk = c.lookup(x, table)
                cc = compile_circuit(c)
                spec = [
                    {"kind": "input", "name": "x"},
                    {"kind": "lookup", "inputs": (0,), "table": tuple(table)},
                ]
                out_slot = slot_of_node(cc, lk)
                for v in range(P):
                    if v in table:
                        z = generate_witness(cc, {"x": v})
                        self.assertEqual(z[out_slot], v, msg=f"v={v}")
                        report = audit(cc, z)
                        self.assertTrue(report.ok, msg=[
                            (r.index, r.tag, r.lhs, r.rhs)
                            for r in report.results if not r.satisfied
                        ])
                        expected = reference_eval(spec, {"x": v})
                        self.assertEqual(z[out_slot], expected[1])
                    else:
                        with self.assertRaises(LookupMissError) as ctx:
                            generate_witness(cc, {"x": v})
                        self.assertEqual(ctx.exception.node, lk)
                        self.assertEqual(ctx.exception.value, v)
                        self.assertEqual(ctx.exception.table, tuple(table))

    def test_constant_lookup_member_and_miss(self):
        # value 也可以是常量节点：成员时可生成，非成员时无解。
        c = Circuit()
        lk = c.lookup(c.const(7), [1, 7, 9])
        cc = compile_circuit(c)
        z = generate_witness(cc, {})
        self.assertTrue(audit(cc, z).ok)
        self.assertEqual(z[slot_of_node(cc, lk)], 7)

        c2 = Circuit()
        c2.lookup(c2.const(8), [1, 7, 9])
        cc2 = compile_circuit(c2)
        with self.assertRaises(LookupMissError):
            generate_witness(cc2, {})


class TestLookupWitnessChain(unittest.TestCase):
    def test_generator_fills_product_chain_slots(self):
        table = [10, 20, 30, 40]
        c = Circuit()
        x = c.input("x")
        lk = c.lookup(x, table)
        cc = compile_circuit(c)
        # 4 个表元素 -> 3 个连乘中间槽。
        self.assertEqual(len(aux_slots(cc, lk)), 3)
        for v in table:
            z = generate_witness(cc, {"x": v})
            slots = aux_slots(cc, lk)
            products = []
            acc = 1
            for t in table:
                acc = (acc * (v - t)) % P
                products.append(acc)
            self.assertEqual([z[s] for s in slots], products[1:])
            self.assertEqual(products[-1], 0)
            self.assertTrue(audit(cc, z).ok)

        # 约束标签：1 条输出定义 + 4 条成员门（含末门 =0）。
        tags = [con.tag for con in cc.constraints]
        self.assertEqual(tags.count("lookup_value"), 1)
        self.assertEqual(tags.count("lookup_member"), 4)


class TestSharedTableLookups(unittest.TestCase):
    def _build(self):
        table = [0, 5, 10, 42]
        c = Circuit()
        x = c.input("x")
        y = c.input("y")
        l1 = c.lookup(x, table)  # 共享同一个 Python 表对象/常量结构
        l2 = c.lookup(y, table)
        return c, table, x, y, l1, l2

    def test_aux_slots_are_distinct_per_lookup(self):
        c, table, x, y, l1, l2 = self._build()
        cc = compile_circuit(c)
        a1, a2 = aux_slots(cc, l1), aux_slots(cc, l2)
        self.assertTrue(a1)
        self.assertEqual(len(a1), len(table) - 1)
        self.assertTrue(set(a1).isdisjoint(a2))
        self.assertNotEqual(slot_of_node(cc, l1), slot_of_node(cc, l2))

    def test_all_equal_inputs_and_independent_membership(self):
        c, table, x, y, l1, l2 = self._build()
        cc = compile_circuit(c)
        # 全相同输入（两个输入取同一个成员值 0；表含 0）。
        z = generate_witness(cc, {"x": 0, "y": 0})
        self.assertTrue(audit(cc, z).ok)
        self.assertEqual(z[slot_of_node(cc, l1)], 0)
        self.assertEqual(z[slot_of_node(cc, l2)], 0)
        # 两个 lookup 取**不同**成员时，中间槽各自承载自己的连乘积，
        # 不会错误共享：l1 在 v=5 的链值不应出现在 l2(v=42) 的槽里。
        z2 = generate_witness(cc, {"x": 5, "y": 42})
        self.assertTrue(audit(cc, z2).ok)

        def chain(v):
            acc, vals = 1, []
            for t in table:
                acc = (acc * (v - t)) % P
                vals.append(acc)
            return vals[1:]

        self.assertEqual([z2[s] for s in aux_slots(cc, l1)], chain(5))
        self.assertEqual([z2[s] for s in aux_slots(cc, l2)], chain(42))

        # 一个在表内、一个不在：见证生成确定失败。
        with self.assertRaises(LookupMissError) as ctx:
            generate_witness(cc, {"x": 5, "y": 6})
        self.assertEqual(ctx.exception.node, l2)

    def test_tampering_one_lookup_aux_does_not_implicate_the_other(self):
        c, table, x, y, l1, l2 = self._build()
        cc = compile_circuit(c)
        z = generate_witness(cc, {"x": 5, "y": 42})
        for s in aux_slots(cc, l1):
            zz = z.copy()
            zz[s] = (z[s] + 1) % P
            report = audit(cc, zz)
            self.assertFalse(report.ok)
            self.assertEqual({f.node for f in report.failures}, {l1})


class TestLookupSlotTamper(unittest.TestCase):
    def test_every_wrong_value_in_every_slot_class_fails(self):
        table = [3, 11, 27, 40, 55, 71, 88, 96]  # 8 元素：链最长
        c = Circuit()
        x = c.input("x")
        lk = c.lookup(x, table)
        cc = compile_circuit(c)
        z = generate_witness(cc, {"x": 40})
        target_slots = [slot_of_node(cc, lk)] + aux_slots(cc, lk)
        self.assertEqual(len(target_slots), 8)  # 输出槽 + 7 个连乘槽
        for sidx in target_slots:
            for wrong in range(P):
                if wrong == z[sidx]:
                    continue
                zz = z.copy()
                zz[sidx] = wrong
                report = audit(cc, zz)
                self.assertFalse(
                    report.ok,
                    msg=f"slot {sidx} wrong={wrong} unexpectedly accepted",
                )
                self.assertIn(lk, {f.node for f in report.failures})

    def test_forged_all_zero_aux_cannot_hide_non_membership(self):
        # 攻击者把输入取为表外值，却伪造输出槽为表内成员、所有连乘槽为 0
        # （末门 p_n*1=0 因此被满足）。输出定义 1*v_out=v_in 必然失败。
        table = [1, 2, 3]
        c = Circuit()
        x = c.input("x")
        lk = c.lookup(x, table)
        cc = compile_circuit(c)
        z = generate_witness(cc, {"x": 2})
        z[cc.inputs["x"]] = 4
        z[slot_of_node(cc, lk)] = 2
        for s in aux_slots(cc, lk):
            z[s] = 0
        report = audit(cc, z)
        self.assertFalse(report.ok)
        nodes = {f.node for f in report.failures}
        self.assertIn(lk, nodes)

    def test_non_member_input_is_rejected_under_many_forged_chains(self):
        table = [2, 5, 8]
        c = Circuit()
        x = c.input("x")
        lk = c.lookup(x, table)
        cc = compile_circuit(c)
        good = generate_witness(cc, {"x": 5})
        x_slot = cc.inputs["x"]
        out_slot = slot_of_node(cc, lk)
        aux = aux_slots(cc, lk)
        # 确定性伪造模式（无随机源）：常数填充 + 递推序列 + 合法链复用。
        forged_patterns = [
            [0, 0], [1, 1], [1, 0], [0, 1],
            [42, 73], [96, 2],
            [good[aux[0]], good[aux[1]]],
        ]
        for v in range(P):
            if v in table:
                continue
            for out_guess in (v, table[0], table[1], table[2]):
                for pat in forged_patterns:
                    zz = good.copy()
                    zz[x_slot] = v
                    zz[out_slot] = out_guess
                    for s, a in zip(aux, pat):
                        zz[s] = a
                    report = audit(cc, zz)
                    self.assertFalse(
                        report.ok,
                        msg=f"v={v} out={out_guess} pat={pat} accepted",
                    )
                    self.assertIn(lk, {f.node for f in report.failures})


class TestLookupTableValidation(unittest.TestCase):
    def test_duplicate_empty_oversize_rejected(self):
        c = Circuit()
        c.input("x")
        for bad in ([1, 1], [0, 5, 0], [9, 9, 9]):
            with self.assertRaises(ValueError, msg=f"bad={bad}"):
                c.lookup(0, bad)
        with self.assertRaises(ValueError):
            c.lookup(0, [])
        with self.assertRaises(ValueError):
            c.lookup(0, list(range(9)))
        self.assertEqual(len(c), 1)  # 失败调用未追加节点

    def test_non_canonical_elements_rejected(self):
        c = Circuit()
        c.input("x")
        for bad in (-1, 97, 100):
            with self.assertRaises(ValueError, msg=f"bad={bad}"):
                c.lookup(0, [bad])
        for bad in (True, False, 1.0, float("nan"), "1", None):
            with self.assertRaises((TypeError, ValueError), msg=f"bad={bad!r}"):
                c.lookup(0, [bad])

    def test_table_container_and_value_ref_types(self):
        c = Circuit()
        c.input("x")
        for bad in ("01", {0, 1}, {"a": 1}, 7, None):
            with self.assertRaises(TypeError, msg=f"bad={bad!r}"):
                c.lookup(0, bad)
        with self.assertRaises(TypeError):
            c.lookup(True, [0, 1])
        with self.assertRaises(CircuitBuildError):
            c.lookup(99, [0, 1])  # 引用不存在的节点

    def test_tuple_table_accepted_and_normalized_canonical(self):
        c = Circuit()
        x = c.input("x")
        lk = c.lookup(x, (0, 96))
        self.assertEqual(c.get_node(lk).table, (0, 96))
        cc = compile_circuit(c)
        self.assertTrue(audit(cc, generate_witness(cc, {"x": 96})).ok)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
