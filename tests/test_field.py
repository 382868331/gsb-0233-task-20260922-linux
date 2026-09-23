"""域工具 parse_scalar 的契约测试。"""

import math
import unittest

from zkcirc.field import P, parse_scalar, fadd, fmul, fsub, finv


class TestParseScalar(unittest.TestCase):
    def test_int_reduced_mod_p(self):
        self.assertEqual(parse_scalar(0), 0)
        self.assertEqual(parse_scalar(96), 96)
        self.assertEqual(parse_scalar(97), 0)
        self.assertEqual(parse_scalar(100), 3)

    def test_negative_int_has_modular_meaning(self):
        self.assertEqual(parse_scalar(-1), P - 1)
        self.assertEqual(parse_scalar(-97), 0)

    def test_bool_rejected_even_though_int_subtype(self):
        with self.assertRaises(TypeError):
            parse_scalar(True)
        with self.assertRaises(TypeError):
            parse_scalar(False)

    def test_nan_and_infinity_explicitly_rejected(self):
        with self.assertRaisesRegex(ValueError, "NaN"):
            parse_scalar(float("nan"))
        with self.assertRaisesRegex(ValueError, "Infinity"):
            parse_scalar(float("inf"))
        with self.assertRaisesRegex(ValueError, "Infinity"):
            parse_scalar(float("-inf"))

    def test_plain_float_rejected(self):
        with self.assertRaises(TypeError):
            parse_scalar(1.0)
        with self.assertRaises(TypeError):
            parse_scalar(1.5)

    def test_other_types_rejected(self):
        for bad in ("1", [1], None, 1 + 0j):
            with self.assertRaises(TypeError):
                parse_scalar(bad)

    def test_error_message_carries_location_hint(self):
        try:
            parse_scalar(True, what="const value")
        except TypeError as exc:
            self.assertIn("const value", str(exc))
        else:  # pragma: no cover
            self.fail("expected TypeError")


class TestFieldOps(unittest.TestCase):
    def test_basic_ops(self):
        self.assertEqual(fadd(60, 50), 13)
        self.assertEqual(fmul(20, 5), 3)       # 100 mod 97
        self.assertEqual(fsub(0, 1), 96)

    def test_inverse(self):
        for a in range(1, P):
            self.assertEqual(fmul(a, finv(a)), 1)
        with self.assertRaises(ZeroDivisionError):
            finv(0)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
