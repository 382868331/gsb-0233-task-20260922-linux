"""zkcirc 条件分支增量演示：select + guarded_assert（离线、确定性）。

运行:  python demo_iteration.py

内容（全部现场计算，无 sleep、无预录结果，总耗时远低于 90 秒）:
  A. 正常路径：guarded 电路编译为稀疏 R1CS，生成见证并逐约束审计通过，
     打印新增中间变量与约束来源。
  B. 关闭分支不触发「除零逆元」约束：b=0 且 d=0（0 无模逆元）时见证
     照常生成、审计通过，相关槽位仍有明确赋值。
  C. 开启分支正确拒绝：b=1 且 d=0 时任何候选逆元都被 GuardedAssertError
     拒绝；b=2 被 NonBooleanSelectError 拒绝。
  D. 独立审计器篡改检测：篡改 selector、选中值、非选中值，以及
     selector=2 的插值伪造，均被逐约束定位（布尔性约束写在电路里）。
"""

from __future__ import annotations

from zkcirc import (
    Circuit,
    compile_circuit,
    generate_witness,
    audit,
    GuardedAssertError,
    NonBooleanSelectError,
)

LINE = "=" * 72
P = 97


def dot(terms, z):
    return sum(c * z[s] for s, c in terms) % P


def independent_audit(cc, z):
    """独立约束审计器：只用朴素点积逐条复算，不调用 zkcirc.audit。"""

    return [con for con in cc.constraints
            if dot(con.a, z) * dot(con.b, z) % P != dot(con.c, z)]


def slot_of(cc, node):
    return next(info.slot for info in cc.sources if info.node == node)


def build_inverse_circuit():
    """条件求逆电路：仅当 b=1 时强制 d*w == 1（w 是 d 的模逆元）。

        0: input b   分支开关
        1: input d   被求逆的量
        2: input w   候选逆元（见证变量，任何情况下都有明确赋值）
        3: const 1
        4: mul   p = d * w
        5: guarded_assert g = (b, p, 1)
        6: mul   out = g * p
    """

    c = Circuit()
    b = c.input("b")
    d = c.input("d")
    w = c.input("w")
    one = c.const(1)
    p = c.mul(d, w)
    g = c.guarded_assert(b, p, one)
    out = c.mul(g, p)
    return c, {"b": b, "d": d, "w": w, "p": p, "g": g, "out": out}


def main() -> None:
    print(LINE)
    print("A. guarded 电路编译：新中间变量与约束来源")
    print(LINE)
    circuit, nodes = build_inverse_circuit()
    cc = compile_circuit(circuit)
    print(f"域 p={cc.p}，见证槽位数 n_vars={cc.n_vars}，约束数 "
          f"{len(cc.constraints)}")
    print("变量来源（sources）:")
    for info in cc.sources:
        print(f"  slot {info.slot}: role={info.role:<13} node={info.node} "
              f"name={info.name} kind={info.kind}")
    print("guarded_assert 节点 5 的约束（新增约束来源）:")
    for con in cc.constraints:
        if con.node == nodes["g"]:
            print(f"  [{con.index}] tag={con.tag}")
            print(f"       origin: {con.origin}")
            print(f"       a={con.a} b={con.b} c={con.c}")

    print()
    print(LINE)
    print("B. 分支关闭（b=0）：d=0 无逆元也不触发逆元约束，见证完整赋值")
    print(LINE)
    z = generate_witness(cc, {"b": 0, "d": 0, "w": 55})
    report = audit(cc, z)
    print(f"输入 b=0, d=0, w=55 -> 见证 z = {z}")
    print(f"audit ok = {report.ok}（w 槽位={z[slot_of(cc, nodes['w'])]} "
          f"有明确赋值，未留未初始化槽）")

    print()
    print(LINE)
    print("C. 分支开启（b=1）：逆元约束生效，正确接受/拒绝")
    print(LINE)
    z_ok = generate_witness(cc, {"b": 1, "d": 5, "w": 39})
    print(f"d=5, w=39（5*39=195=1 mod 97）-> audit ok = "
          f"{audit(cc, z_ok).ok}")
    for w in (38, 0, 50):
        try:
            generate_witness(cc, {"b": 1, "d": 5, "w": w})
            print(f"d=5, w={w} -> 未被拒绝（不应发生）")
        except GuardedAssertError as exc:
            print(f"d=5, w={w} -> 拒绝: {exc}")
    try:
        generate_witness(cc, {"b": 1, "d": 0, "w": 1})
    except GuardedAssertError as exc:
        print(f"d=0（除零情形，无逆元）-> 拒绝: {exc}")
    try:
        generate_witness(cc, {"b": 2, "d": 5, "w": 39})
    except NonBooleanSelectError as exc:
        print(f"b=2 -> 拒绝: {exc}")

    print()
    print(LINE)
    print("D. 独立审计器篡改检测（selector / 选中值 / 非选中值 / b=2 插值）")
    print(LINE)
    base = generate_witness(cc, {"b": 1, "d": 5, "w": 39})

    def show(label, z):
        failed = independent_audit(cc, z)
        tags = [f"#{con.index}:{con.tag}" for con in failed]
        print(f"{label} -> 独立审计失败约束: {tags if tags else '无（不应发生）'}")

    # 在 b=0、d=0（两支值不等）的合法见证上把 selector 翻成 1：
    # 守卫被非法开启，guarded_equal 立即失败。
    # （b=1 且等式成立时翻成 0 在 R1CS 关系语义下本就不可区分，
    #   见 README「已知限制」。）
    z1 = generate_witness(cc, {"b": 0, "d": 0, "w": 55})
    z1[slot_of(cc, nodes["b"])] = 1
    show("篡改 selector b: 0->1      ", z1)
    z2 = list(base); z2[slot_of(cc, nodes["p"])] = 2
    show("篡改选中值 p=d*w: 1->2     ", z2)
    z3 = list(base); z3[slot_of(cc, nodes["w"])] = 38
    show("篡改非选中见证 w: 39->38   ", z3)
    # selector=2 插值伪造：令 p' 满足 b*(p-1)=p'-1 在 b=2 时成立，
    # 即 p' = 2*p - 1，试图绕过 guarded_equal。
    z4 = list(base)
    z4[slot_of(cc, nodes["b"])] = 2
    z4[slot_of(cc, nodes["p"])] = (2 * base[slot_of(cc, nodes["p"])] - 1) % P
    show("selector=2 插值伪造        ", z4)
    print("结论：b*(b-1)=0 布尔性约束写在电路中，b=2 无法插值绕过条件。")


if __name__ == "__main__":
    main()
