"""本次条件分支增量的固定输入演示。

运行：python demo_iteration.py

现场构建/编译/生成见证并审计：
1. selector=0：允许 x=0、inv=0，不要求逆元，select 取 fallback；
2. selector=1：x=2 必须配逆元，错误逆元由见证生成与 R1CS 拒绝；
3. 独立审计 selector=2、选中值与非选中值篡改。
"""

from __future__ import annotations

from zkcirc import (
    Circuit,
    compile_circuit,
    generate_witness,
    audit,
    GuardedEqualError,
)


P = 97
LINE = "=" * 72


def build_circuit():
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
    return c, {
        "b": b, "x": x, "inv": inv, "fallback_base": fallback_base,
        "product": product, "one": one, "guard": guard,
        "fallback": fallback, "chosen": chosen,
    }


def independent_check(compiled, witness):
    def dot(terms):
        return sum(coeff * witness[slot] for slot, coeff in terms) % P

    failures = []
    for con in compiled.constraints:
        lhs = dot(con.a) * dot(con.b) % P
        rhs = dot(con.c) % P
        if lhs != rhs:
            failures.append((con, lhs, rhs))
    return failures


def main() -> None:
    c, nodes = build_circuit()
    cc = compile_circuit(c)
    print(LINE)
    print("条件逆元电路：guarded_equal(b, x*inv, 1)；select(b, x, fallback_base+1)")
    print(f"节点 {len(cc.nodes)} 个，见证槽 {cc.n_vars} 个，约束 {len(cc.constraints)} 条")
    for tag in ("guarded_value", "guarded_booleanity", "guarded_equal",
                "select_value", "select_booleanity"):
        con = next(item for item in cc.constraints if item.tag == tag)
        print(f"  - {tag}: {con.origin}")

    print()
    print("[1] selector=0，关闭逆元分支：x=0, inv=0 合法，输出 fallback=6")
    closed = {"b": 0, "x": 0, "inv": 0, "fallback_base": 5}
    z0 = generate_witness(cc, closed)
    print(f"    witness={z0}；独立审计失败数={len(independent_check(cc, z0))}")
    assert audit(cc, z0).ok

    print()
    print("[2] selector=1，开启逆元分支：2 * pow(2,95,97) = 1")
    inv2 = pow(2, P - 2, P)
    open_ok = {"b": 1, "x": 2, "inv": inv2, "fallback_base": 5}
    z1 = generate_witness(cc, open_ok)
    print(f"    inv={inv2}，chosen={z1[next(s.slot for s in cc.sources if s.node == nodes['chosen'])]}")
    assert audit(cc, z1).ok and not independent_check(cc, z1)

    print()
    print("[3] selector=1 但给出错误逆元 inv=0：见证生成实际抛出")
    try:
        generate_witness(cc, {"b": 1, "x": 2, "inv": 0, "fallback_base": 5})
    except GuardedEqualError as exc:
        print(f"    {type(exc).__name__}: {exc}")

    print()
    print("[4] 独立审计篡改：selector=2 不能插值绕过布尔性")
    bad_b = z1.copy()
    bad_b[cc.inputs["b"]] = 2
    failures = independent_check(cc, bad_b)
    print(f"    独立审计失败 {len(failures)} 条；标签="
          f"{sorted({f[0].tag for f in failures})}")
    assert any(f[0].tag in {"guarded_booleanity", "select_booleanity"}
               for f in failures)

    print()
    print("[5] 独立审计篡改：选中分支 product=0 触发逆元等式失败")
    bad_product = z1.copy()
    product_slot = next(s.slot for s in cc.sources if s.node == nodes["product"])
    bad_product[product_slot] = 0
    failures = independent_check(cc, bad_product)
    print(f"    独立审计失败标签={sorted({f[0].tag for f in failures})}")
    assert any(f[0].tag == "guarded_equal" for f in failures)

    print()
    print("[6] 独立审计篡改：非选中 fallback 槽已初始化，但其定义约束定位失败")
    bad_fallback = z1.copy()
    fallback_slot = next(s.slot for s in cc.sources if s.node == nodes["fallback"])
    bad_fallback[fallback_slot] = 7
    failures = independent_check(cc, bad_fallback)
    print(f"    fallback {fallback_slot} 槽 6 -> 7；失败标签="
          f"{sorted({f[0].tag for f in failures})}")
    assert any(f[0].tag == "add" for f in failures)

    print()
    print(LINE)
    print("演示结束：条件写入了 R1CS；关闭分支不强制逆元，开启分支拒绝错误逆元。")
    print(LINE)


if __name__ == "__main__":
    main()
