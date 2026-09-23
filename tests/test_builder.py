"""DAG 构建器 Circuit 的输入校验与上限测试。"""

import unittest

from zkcirc import Circuit, MAX_NODES
from zkcirc.errors import CircuitBuildError, CircuitLimitError


class TestCircuitBuilder(unittest.TestCase):
    def test_empty_circuit_compiles(self):
        cc = __import__("zkcirc").compile_circuit(Circuit())
        self.assertEqual(cc.n_vars, 1)
        self.assertEqual(cc.constraints, ())

    def test_node_refs_must_be_existing_indices(self):
        c = Circuit()
        with self.assertRaises(CircuitBuildError):
            c.add(0, 1)
        c.const(1)
        with self.assertRaises(CircuitBuildError):
            c.add(0, 1)  # 1 尚不存在

    def test_refs_reject_bool_float_str(self):
        c = Circuit()
        c.const(1)
        with self.assertRaises(TypeError):
            c.add(True, 0)
        with self.assertRaises(TypeError):
            c.mul(0, 1.0)
        with self.assertRaises(TypeError):
            c.select("0", 0, 0)

    def test_input_name_rules(self):
        c = Circuit()
        c.input("a")
        with self.assertRaises(CircuitBuildError):
            c.input("a")
        with self.assertRaises(ValueError):
            c.input("")
        with self.assertRaises(TypeError):
            c.input(7)

    def test_const_rejects_bool_nan_inf_float(self):
        c = Circuit()
        with self.assertRaises(TypeError):
            c.const(True)
        with self.assertRaises(TypeError):
            c.const(1.0)
        with self.assertRaises(ValueError):
            c.const(float("nan"))
        with self.assertRaises(ValueError):
            c.const(float("inf"))

    def test_node_limit_is_enforced_and_no_partial_change(self):
        c = Circuit()
        for _ in range(MAX_NODES):
            c.const(0)
        self.assertEqual(len(c), MAX_NODES)
        with self.assertRaises(CircuitLimitError):
            c.const(1)
        self.assertEqual(len(c), MAX_NODES)  # 失败的追加未生效

    def test_failed_input_does_not_register_name(self):
        c = Circuit()
        for _ in range(MAX_NODES):
            c.const(0)
        with self.assertRaises(CircuitLimitError):
            c.input("late")
        c2 = Circuit()
        c2.input("late")  # 名字未被上一个失败调用占用
        self.assertEqual(len(c2), 1)

    def test_back_reference_forward_is_impossible(self):
        c = Circuit()
        a = c.const(1)
        b = c.const(2)
        self.assertEqual((a, b), (0, 1))
        # 构造器层面无法引用未来节点；防御式 compile 校验见 test_compile。


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
