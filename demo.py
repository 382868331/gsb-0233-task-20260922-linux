"""zkcirc 固定输入演示（离线、确定性、无第三方依赖）。

运行:  python demo.py

内容:
  A. 正常路径：构建含共享子表达式与 select 的电路，编译为稀疏 R1CS，
     生成见证，逐约束审计通过，并打印变量来源。
  B. 异常边界：非布尔 select 选择位被拒绝；缺失命名输入被拒绝。
  C. 失败约束定位：篡改一个中间见证槽，audit 逐约束报告失败位置。
  D. 2..8 位有符号整数：4 位 sadd/ssub 回绕、slt/sle/seq 比较，
     逐位布尔性与进位约束的源码映射；边界回绕手算核对；越界输入
     被明确拒绝；篡改进位比特被审计定位。

所有输入均写死在本文件中，结果全部现场计算，不使用 sleep 或预录输出。
"""

from __future__ import annotations

from zkcirc import (
    Circuit,
    compile_circuit,
    generate_witness,
    audit,
    NonBooleanSelectError,
    UnknownInputError,
    SignedInputError,
)

LINE = "=" * 72


def build_circuit() -> tuple[Circuit, dict[int, str]]:
    """示例电路：

        s  = x + y                 # 共享子表达式
        q  = s * s
        v  = select(b, q, 2)       # b∈{0,1}：b=1 取 q，否则取常量 2
        out = v + s
        assert_equal(out, out)     # 输出锚点
    """

    c = Circuit()
    x = c.input("x")
    y = c.input("y")
    b = c.input("b")
    s = c.add(x, y)
    q = c.mul(s, s)
    k = c.const(2)
    v = c.select(b, q, k)
    out = c.add(v, s)
    anchor = c.assert_equal(out, out)
    labels = {x: "x", y: "y", b: "b", s: "s=x+y", q: "q=s*s",
              k: "const 2", v: "v=select(b,q,2)", out: "out=v+s",
              anchor: "assert out"}
    return c, labels


def part_a() -> None:
    print(LINE)
    print("A. 正常路径：编译 -> 见证生成 -> 逐约束审计")
    print(LINE)
    c, labels = build_circuit()
    cc = compile_circuit(c)
    print(f"域 p = {cc.p}；节点数 = {len(cc.nodes)}；"
          f"见证变量数 n_vars = {cc.n_vars}（槽 0 恒为 1）")
    print(f"稀疏约束数 = {len(cc.constraints)}")
    print()

    print("变量来源表：")
    for info in cc.sources:
        if info.role == "constant_one":
            print(f"  槽 {info.slot:>2}: 常数 1（z[0]，首位恒 1）")
        else:
            print(f"  槽 {info.slot:>2}: {info.role:<12} "
                  f"节点 {info.node} ({labels[info.node]})"
                  + (f"  输入名={info.name!r}" if info.name else ""))
    print()

    print("稀疏 R1CS 约束（<a,z>*<b,z>=<c,z>，系数已模 97 规约）：")
    for con in cc.constraints:
        print(f"  #{con.index} [节点 {con.node} {labels[con.node]}] "
              f"{con.tag}")
        print(f"       {con.origin}")
        print(f"       A={con.a}")
        print(f"       B={con.b}")
        print(f"       C={con.c}")
    print()

    feeds = {"x": 4, "y": 6, "b": 1}  # 固定输入：s=10, q=100≡3, out=13
    print(f"固定用户输入（仅按名字提供，无法指定中间槽）：{feeds}")
    z = generate_witness(cc, feeds)
    print(f"生成的见证 z = {z}")
    print(f"  域值核对：s=10, q=100 mod 97 = {100 % 97}, "
          f"v=q=3, out=3+10=13；z 中各槽与之一致")
    report = audit(cc, z)
    print(f"审计结果：ok={report.ok}，"
          f"{sum(r.satisfied for r in report.results)}/"
          f"{len(report.results)} 条约束满足")
    assert report.ok


def part_b() -> None:
    print()
    print(LINE)
    print("B. 异常边界：见证生成拒绝非法请求（现场实际抛出）")
    print(LINE)
    c, _ = build_circuit()
    cc = compile_circuit(c)

    # B1：select 选择位 b=50，不是 0/1。
    try:
        generate_witness(cc, {"x": 4, "y": 6, "b": 50})
    except NonBooleanSelectError as exc:
        print(f"[拒绝 1] 非布尔 select 位 -> {type(exc).__name__}")
        print(f"        节点 {exc.node}：b 的域值 = {exc.b}，"
              f"仅允许 0/1（b*(b-1)=0 不可满足）")
        print(f"        信息：{exc}")

    # B2：缺失命名输入。
    try:
        generate_witness(cc, {"x": 4, "y": 6})  # 缺 b
    except UnknownInputError as exc:
        print(f"[拒绝 2] 未知/缺失输入 -> {type(exc).__name__}：{exc}")
        print("        这是确定的无解（输入缺失）；本库无搜索过程，"
              "因此不存在也不需要「预算耗尽」这一类别。")


def part_c() -> None:
    print()
    print(LINE)
    print("C. 失败约束定位：篡改中间槽后 audit 逐约束报告")
    print(LINE)
    c, labels = build_circuit()
    cc = compile_circuit(c)
    z = generate_witness(cc, {"x": 4, "y": 6, "b": 1})

    # 中间槽：s=x+y 在槽 4（来源表可查；这里直接按节点定位，避免写死数字）。
    s_node = next(i for i, n in enumerate(cc.nodes) if n.kind == "add")
    s_slot = next(info.slot for info in cc.sources if info.node == s_node)
    original = z[s_slot]
    z_bad = z.copy()
    z_bad[s_slot] = (original + 7) % 97  # 把 10 改成 17
    print(f"合法见证   = {z}")
    print(f"篡改：槽 {s_slot}（节点 {s_node} {labels[s_node]}）"
          f"{original} -> {z_bad[s_slot]}")
    print(f"被篡改见证 = {z_bad}")
    print()

    report = audit(cc, z_bad)
    print(f"总体结论 ok={report.ok}；"
          f"失败 {len(report.failures)} 条，明细：")
    for r in report.results:
        mark = "PASS" if r.satisfied else "FAIL"
        print(f"  [{mark}] 约束 #{r.index} 节点 {r.node} "
              f"({labels[r.node]}) tag={r.tag}")
        if not r.satisfied:
            print(f"         <a,z>*<b,z> = {r.lhs}，<c,z> = {r.rhs}，"
                  f"差 (lhs-rhs) mod 97 = {r.difference}")
            print(f"         语义：{r.origin}")
    assert not report.ok
    # 被篡改的 s 槽由 add 节点定义，并被 q=s*s 与 out=v+s 消费，
    # 失败必然定位到这些节点。
    failed_nodes = {r.node for r in report.failures}
    print()
    print(f"失败定位到的节点集合 = {sorted(failed_nodes)}，"
          f"其中 {s_node} 即被篡改的 s=x+y 定义节点。")


# ---------------------------------------------------------------------------
# D. 2..8 位有符号整数（二补码）加减与比较
# ---------------------------------------------------------------------------


def _wrap4(value: int) -> int:
    """4 位二补码回绕（演示用手算口径，独立于 zkcirc）。"""

    return ((value + 8) % 16) - 8


def build_signed_circuit():
    """4 位有符号电路：

        s = sadd(a, b)   # 溢出仅回绕
        d = ssub(a, b)
        lt = slt(a, b)   # 有符号 a < b，输出 0/1
        le = sle(a, b)
        eq = seq(a, b)
    """

    c = Circuit()
    a = c.signed_input("a", 4)
    b = c.signed_input("b", 4)
    s = c.sadd(a, b)
    d = c.ssub(a, b)
    lt = c.slt(a, b)
    le = c.sle(a, b)
    eq = c.seq(a, b)
    return c, (a, b, s, d, lt, le, eq)


def part_d() -> None:
    print()
    print(LINE)
    print("D. 4 位有符号整数：逐位布尔性 + 进位/借位 R1CS（非域运算模拟）")
    print(LINE)
    c, (a, b, s, d, lt, le, eq) = build_signed_circuit()
    cc = compile_circuit(c)
    print(f"节点数 = {len(cc.nodes)}；见证槽数 = {cc.n_vars}；"
          f"稀疏约束数 = {len(cc.constraints)}")
    print("有符号输入登记：", dict(cc.signed_inputs))
    print()

    # 源码映射：sadd 节点 2 的逐位槽布局。
    lay = cc.signed_layouts[s]
    print(f"sadd 节点 {s} 的源码映射（SignedLayout）：")
    print(f"  结果比特槽（小端，末位为符号位）= {lay.bit_slots}")
    print(f"  进位槽 c0..c4（c0 钉为 0，c4 丢弃即回绕）= {lay.carry_slots}")
    print(f"  字槽 word = Σ 2^k·b_k (mod 97) = {lay.word_slot}")
    for t in (lay.bit_slots[0], lay.carry_slots[1], lay.word_slot):
        info = cc.source_of(t)
        print(f"  槽 {t:>3}: role={info.role:<12} kind={info.kind} "
              f"node={info.node}")
    print()

    print("抽样约束（证明是逐位二次约束，而非整条域加法）：")
    for want in ("sadd_bit", "sbit_booleanity", "signed_carry0"):
        con = next(x for x in cc.constraints if x.tag == want)
        print(f"  #{con.index} tag={con.tag}  node={con.node}")
        print(f"     {con.origin}")
        print(f"     A={con.a}\n     B={con.b}\n     C={con.c}")
    print()

    # 正常 + 回绕边界：全部手算核对。
    print("加减（回绕）结果核对（期望值为手算 4 位二补码）：")
    print(f"  {'a':>4} {'b':>4} | {'a+b 回绕':>8} {'字槽':>4} | "
          f"{'a-b 回绕':>8} {'字槽':>4}")
    for av, bv in ((3, 2), (7, 1), (-8, -1), (-8, 1), (-1, -1)):
        z = generate_witness(cc, {"a": av, "b": bv})
        es, ed = _wrap4(av + bv), _wrap4(av - bv)
        gs = z[cc.signed_layouts[s].word_slot]
        gd = z[cc.signed_layouts[d].word_slot]
        assert audit(cc, z).ok
        assert gs == es % 16 and gd == ed % 16
        print(f"  {av:>4} {bv:>4} | {es:>8} {gs:>4} | {ed:>8} {gd:>4}")
    print("  例：7+1 在 4 位下回绕为 -8（字=8）；-8-1 回绕为 7（字=7）。")
    print()

    print("有符号比较（-1 < 1；与无符号口径 15 > 1 必须不同）：")
    z = generate_witness(cc, {"a": -1, "b": 1})
    print(f"  a=-1,b=1 -> slt={z[cc.signed_cmp_layouts[lt].flag_slot]}, "
          f"sle={z[cc.signed_cmp_layouts[le].flag_slot]}, "
          f"seq={z[cc.signed_cmp_layouts[eq].flag_slot]}")
    z = generate_witness(cc, {"a": 7, "b": -8})
    print(f"  a=7,b=-8 -> slt={z[cc.signed_cmp_layouts[lt].flag_slot]}, "
          f"sle={z[cc.signed_cmp_layouts[le].flag_slot]}（7 不小于 -8）")
    z = generate_witness(cc, {"a": -3, "b": -3})
    print(f"  a=-3,b=-3 -> slt={z[cc.signed_cmp_layouts[lt].flag_slot]}, "
          f"sle={z[cc.signed_cmp_layouts[le].flag_slot]}, "
          f"seq={z[cc.signed_cmp_layouts[eq].flag_slot]}")
    print()

    # 实际触发的错误：越界输入。
    print("非法输入拒绝（现场实际抛出，失败不留半状态）：")
    try:
        generate_witness(cc, {"a": 8, "b": 0})  # 4 位最大只到 7
    except SignedInputError as exc:
        print(f"  [拒绝 1] 越界 -> {type(exc).__name__}: {exc}")
        print(f"          合法区间 [{exc.low}, {exc.high}]，width={exc.width}")
    try:
        generate_witness(cc, {"a": True, "b": 0})  # bool 即使是 int 子类也拒绝
    except TypeError as exc:
        print(f"  [拒绝 2] 类型非法 -> TypeError: {exc}")
    print()

    # 篡改进位比特：审计必须定位到 sadd 节点。
    print("篡改见证：把 sadd 的进位 c1 翻转，audit 逐条定位：")
    z = generate_witness(cc, {"a": -8, "b": 1})
    c1 = cc.signed_layouts[s].carry_slots[1]
    zz = z.copy()
    zz[c1] = 1 - zz[c1]
    report = audit(cc, zz)
    hits = [f for f in report.failures if f.node == s]
    print(f"  被篡改槽 = {c1}（sadd 节点 {s} 的进位 c1）；"
          f"审计 ok={report.ok}，命中该节点的失败约束 {len(hits)} 条：")
    for f in hits[:4]:
        print(f"     [FAIL] #{f.index} tag={f.tag}  {f.origin}  "
              f"lhs={f.lhs} rhs={f.rhs}")
    assert not report.ok and hits


def main() -> None:
    part_a()
    part_b()
    part_c()
    part_d()
    print()
    print(LINE)
    print("演示结束：1 个正常结果 + 2 个实际触发的异常拒绝 + 1 组失败约束定位")
    print("+ 1 组有符号加减比较（正常/回绕边界/越界拒绝/篡改见证定位）。")
    print("本程序不生成任何真实链上证明，仅在 p=97 域内做约束审计。")
    print(LINE)


if __name__ == "__main__":
    main()
