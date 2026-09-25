"""zkcirc 固定输入演示（离线、确定性、无第三方依赖）。

运行:  python demo.py

内容:
  A. 正常路径：构建含共享子表达式与 select 的电路，编译为稀疏 R1CS，
     生成见证，逐约束审计通过，并打印变量来源。
  B. 异常边界：非布尔 select 选择位被拒绝；缺失命名输入被拒绝。
 C. 失败约束定位：篡改一个中间见证槽，audit 逐约束报告失败位置。
  D. lookup(value, table) 成员约束：接受/拒绝现场计算 + 伪造中间值被抓。

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
    LookupMissError,
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


def part_d() -> None:
    print()
    print(LINE)
    print("D. lookup(value, table)：有限查找表成员约束（含 0 表）")
    print(LINE)
    table = [0, 5, 10, 42]  # 含 0；4 个互不重复的规范域元素
    c = Circuit()
    x = c.input("x")
    lk = c.lookup(x, table)
    cc = compile_circuit(c)
    print(f"查找表 = {table}；成员多项式连乘拆成的约束：")
    for con in cc.constraints:
        print(f"  #{con.index} tag={con.tag:<14} {con.origin}")
        print(f"       A={con.a}\n       B={con.b}\n       C={con.c}")
    aux = [info.slot for info in cc.sources
           if info.node == lk and info.kind == "lookup_aux"]
    print(f"lookup 独占的连乘中间槽 = {aux}（输出槽另计，不与任何"
          "其他 lookup 共享）")
    print()

    for v in (0, 10, 42):
        z = generate_witness(cc, {"x": v})
        print(f"[接受] x={v}：输出槽={z[next(i.slot for i in cc.sources if i.node == lk and i.kind != 'lookup_aux')]}, "
              f"连乘槽={[z[s] for s in aux]}，audit ok={audit(cc, z).ok}")

    try:
        generate_witness(cc, {"x": 6})  # 6 不在 [0, 5, 10, 42]
    except LookupMissError as exc:
        print(f"[拒绝] x=6 -> {type(exc).__name__}：{exc}")

    # 伪造：x 取表外值 6，却把输出槽改成成员 5、所有连乘槽填 0
    # （末门 p_n*1=0 因此被满足），输出定义 1*v_out=v_in 仍必失败。
    z_bad = generate_witness(cc, {"x": 5})
    out_slot = next(i.slot for i in cc.sources
                    if i.node == lk and i.kind != "lookup_aux")
    z_bad[cc.inputs["x"]] = 6
    z_bad[out_slot] = 5
    for s in aux:
        z_bad[s] = 0
    report = audit(cc, z_bad)
    print(f"[伪造中间值] x 槽=6、输出槽=5、连乘槽全 0 -> audit ok={report.ok}")
    for f in report.failures:
        print(f"         FAIL #{f.index} tag={f.tag} 节点={f.node} "
              f"lhs={f.lhs} rhs={f.rhs} 差={f.difference}")
    assert not report.ok


def main() -> None:
    part_a()
    part_b()
    part_c()
    part_d()
    print()
    print(LINE)
    print("演示结束：正常路径 + 异常拒绝 + 失败定位 + lookup 成员约束演示。")
    print("本程序不生成任何真实链上证明，仅在 p=97 域内做约束审计。")
    print(LINE)


if __name__ == "__main__":
    main()
