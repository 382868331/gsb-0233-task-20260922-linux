# zkcirc — p=97 算术约束电路的见证生成与审计

一个离线、零第三方依赖的教学型可复用库：在素数域 **p = 97** 上把表达式
DAG（`add` / `mul` / `const` / `input` / `select` / `lookup` /
`assert_equal`）
编译为稀疏 **R1CS**（`<A,z>·<B,z> = <C,z> (mod 97)`，`z[0] ≡ 1`），
生成见证，并对任意见证向量做**逐约束审计**、报告每条失败约束的位置与
左右侧值。`lookup(value, table)` 把「value 属于 1..8 个互不重复域元素
的有限查找表」表达为成员多项式连乘拆成的原生 R1CS 乘法门，不引入任何
没有约束的宿主布尔判断。

**本库不生成、也不验证任何真实链上零知识证明**；它只实现题目契约规定
的有限数学子集，不宣称兼容 Groth16/PLONK 等任何行业协议。

## 运行环境

- Python **3.14.7**（仅使用标准库；3.10+ 的语法即可运行，但以 3.14.7 为准）
- Linux 原生；安装 Python 后**无需安装任何其他依赖**
- 完全离线：不需要网络、账号、密钥、数据库、中间件、云 API 或 Docker

## 准确命令

```bash
# 必要测试（独立参考解释器位于 tests/reference.py，不导入被测核心）
python -m unittest discover -s tests -v

# 固定输入演示（现场计算，约 0.05 秒，远小于 8 秒；无 sleep、无预录结果）
python demo.py
```

### lookup 可复现使用路径与失败示例

```bash
./.venv/bin/python - <<'PY'
from zkcirc import Circuit, compile_circuit, generate_witness, audit, LookupMissError

c = Circuit()
x = c.input("x")
c.lookup(x, [0, 5, 10, 42])   # 含 0 的表；输出值 == x，另加成员连乘门
cc = compile_circuit(c)

z = generate_witness(cc, {"x": 5})          # 5 在表内
print(audit(cc, z).ok, z[cc.inputs["x"]])   # True 5

generate_witness(cc, {"x": 6})              # 6 不在表内 -> LookupMissError
PY
```

现场输出（最后一行是实际抛出的拒绝，不是捕获后吞掉）：

```
True 5
zkcirc.errors.LookupMissError: lookup node 1 value 6 is not in table [0, 5, 10, 42] (field p=97): the membership product cannot be zero
```

`python demo.py` 的 D 节还演示了把表外输入伪造成「输出槽=成员值、
连乘槽全 0」时，audit 如何在 `lookup_value` 与第一条成员门上同时定位
失败。完整穷举（全部 97 个域值 × 8 张表、逐中间槽篡改）由
`tests/test_lookup.py` 自动执行。

## 目录结构

```
zkcirc/            本题库（可导入包）
  __init__.py        公开接口导出
  field.py           模 97 域工具、标量入参契约（拒绝 bool/NaN/Infinity）
  circuit.py         DAG 构建、R1CS 编译、见证生成、逐约束审计
  errors.py          可定位的错误类型层次
tests/
  reference.py       独立参考：朴素域解释器 + 独立点积（不 import zkcirc）
  test_field.py      域工具契约
  test_builder.py    DAG 构建校验与 200 节点上限
  test_circuit.py    编译/见证/审计：独立解释器对照、非布尔 select、
                     共享子图、中间值篡改、未知输入、稀疏格式
  test_soundness.py  确定性穷举：全部 97 个域值的单点篡改检测
  test_lookup.py     lookup：逐值接受集合、含 0 表、共享表、
                     逐槽伪造负例、表校验
demo.py            固定输入演示
```

## 公开接口

### 1. 构建 DAG：`Circuit`

```python
from zkcirc import Circuit, compile_circuit, generate_witness, audit

c = Circuit()
x   = c.input("x")            # 命名输入，返回节点下标；名字电路内唯一
y   = c.input("y")
k   = c.const(40)             # 常量节点（int，构造时模 97 规约）
s   = c.add(x, y)             # 加法
m   = c.mul(s, k)             # 乘法；节点 s 被共享时只分配一个见证槽
sel = c.select(b, t, u)       # b∈{0,1} 时输出 b*t+(1-b)*u
a   = c.assert_equal(m, sel)  # 见证生成时强制两侧相等；输出取左侧
lk  = c.lookup(x, [0, 5, 10]) # 输出 == x；并约束 x∈{0,5,10}（表长 1..8）
```

- 节点按下标顺序追加，**只能引用更早的节点**，故 DAG 天然无环；
  插入顺序即拓扑序。
- 同一节点下标传给多个父节点即表示**共享子图**；编译时只占一个见证槽。
- **上限：最多 200 个节点**（`zkcirc.MAX_NODES`）。超出抛
  `CircuitLimitError`，失败的追加不产生任何部分变更。
- **lookup 表契约**：表必须是 `list/tuple`，长度 **1..8**
  （`zkcirc.MAX_LOOKUP_TABLE`），元素必须是**规范域元素**（`0..96` 的
  int；拒绝 bool、负数、`≥97`、float）且**互不重复**。空表、超长、
  重复或非规范元素在构建期抛 `ValueError`/`TypeError`，且不追加节点。
  相同表可以在多个 lookup 间重复使用，但每个 lookup 拥有**自己独立的**
  连乘中间槽，不会错误共享不同 value 的中间见证。

### 2. 编译：`compile_circuit(circuit) -> CompiledCircuit`

`CompiledCircuit` 字段：

| 字段 | 含义 |
|---|---|
| `p` | 97 |
| `n_vars` | 见证向量长度（含 `z[0]` 常数 1） |
| `constraints` | `tuple[Constraint]`，稀疏 R1CS |
| `sources` | `tuple[VariableInfo]`，逐槽位的**变量来源** |
| `inputs` | `{输入名: 槽位}` 只读映射 |
| `nodes` | 原始 DAG 节点元组 |

- `Constraint(index, node, tag, origin, a, b, c)`：`a/b/c` 均为
  `tuple[(var_index, coeff)]`，按变量下标升序、系数已模 97 规约、
  零系数被剔除。`tag` ∈ `add | mul | select_value | select_booleanity |
  lookup_value | lookup_member | assert_value | assert_equal`；`origin` 是
  人读语义说明。
- `VariableInfo(slot, role, node, name, kind)`：`role` 为
  `constant_one`（槽 0）、`input` 或 `intermediate`。
- **常量节点不占见证槽**：在约束中内联为常数槽 0 上的系数。

编译出的约束（`v` 为节点输出槽，`lin(n)` 为操作数线性项）：

| 节点 | 约束 |
|---|---|
| `add` | `1 · v = lin(x) + lin(y)` |
| `mul` | `lin(x) · lin(y) = v` |
| `select` | `b · (lin(x)−lin(y)) = v−lin(y)` **且** `b·(b−1) = 0` |
| `lookup` | `1·v = lin(value)`，外加成员连乘乘法门链（见下节） |
| `assert_equal` | `1 · v = lin(x)` **且** `(lin(x)−lin(y)) · 1 = 0` |

两条 select 约束在域 p=97 上恰好等价于「`b∈{0,1}` 且
`v = b·x + (1−b)·y`」：布尔性方程在域中只有 0、1 两个解。

#### lookup 的成员连乘门

对表 `T = [t_1, …, t_n]`（`1 ≤ n ≤ 8`），成员条件
`∏_{k=1..n} (v − t_k) = 0` 在域（整环）上当且仅当 `v` 等于某个 `t_k`。
编译把连乘拆成 n 条原生乘法门（没有宿主布尔变量）：

| 门 | A | B | C |
|---|---|---|---|
| n=1 的唯一门 | `lin(v) − t_1` | `1` | `0` |
| 第 1 门（n≥2） | `lin(v) − t_1` | `lin(v) − t_2` | `p_2`（中间槽） |
| 中间门 | `p_{k−1}` | `lin(v) − t_k` | `p_k`（中间槽） |
| 末门 | `p_n` | `1` | `0` |

表含 n 个元素时分配 **n−1 个** `lookup_aux` 中间槽（`sources` 中
`kind="lookup_aux"`）。它们与输出槽一样有「输出系数为 1」的定义门，
固定其他槽后取值唯一，逐槽逐域值篡改测试（见 `tests/test_lookup.py`）
证实审计必捕获任何伪造中间值，包括把所有连乘槽伪造为 0。

### 3. 见证生成：`generate_witness(compiled, {"name": int, ...}) -> list[int]`

- 直接按 DAG 在域上求值（不求解矩阵），返回完整 `z`，`z[0] = 1`。
- 调用方**只能按名字提供输入**；中间槽全部由本函数计算，
  **无法被用户输入覆盖**。多余输入名同样被拒绝。
- 失败即整体抛出，**绝不返回部分见证**：

| 情形 | 异常 |
|---|---|
| 缺失输入名 | `UnknownInputError`（确定无解） |
| 未声明的多余输入名 / 非 str 键 | `UnexpectedInputError` / `TypeError` |
| select 位 ∉ {0,1} | `NonBooleanSelectError`（带节点号与实际 b 值） |
| assert_equal 不成立 | `AssertEqualError`（带节点号与左右值） |
| lookup 值不在表内 | `LookupMissError`（带节点号、实际值与表） |
| 值非 int、bool、NaN、Infinity、其他类型 | `TypeError` / `ValueError` |

### 4. 审计：`audit(compiled, witness) -> AuditReport`

- 见证形状非法（长度不符、元素非规范域元素、含 bool/float/NaN/Infinity、
  `z[0]≠1`）抛 `AuditError`。
- 形状合法则**始终返回报告**：`AuditReport.ok` 与
  `results: tuple[ConstraintResult]`；`ConstraintResult` 含
  `index / node / tag / origin / satisfied / lhs / rhs / difference`。
- `report.failures` 给出全部失败约束，可直接定位到 DAG 节点与约束语义。

## 输入与错误语义（总契约）

- 域元素一律是 `0..96` 的 Python **int**；接受任意 int 并模 97 规约，
  **负数有确定的模运算含义**（如 `-1 → 96`）。
- **整数参数拒绝 bool**：`True/False` 即使是 `int` 子类型也抛 `TypeError`。
- **拒绝 float**：`NaN` 与 `±Infinity` 以 `ValueError` 单独点名；
  普通 float 抛 `TypeError`（域算术完全精确，不存在浮点域元素）。
- 所有错误都带定位信息（节点下标 / 约束下标 / 输入名 / 槽位），
  非法输入不会被静默纠正。
- **「预算耗尽」与「无解」严格分开**：本库没有任何搜索过程
  （见证是按 DAG 直接求值得到的），因此不存在预算耗尽这一类别；
  唯一的「无解」是输入缺失或约束不成立，各自以明确的确定异常报告。
- 有状态操作（构建节点、生成见证）失败时不留下未说明的部分变更。

## 误差口径

本库**不产生任何浮点结果**：所有运算都是整数模 97，结果精确、误差为 0，
不存在容差（tolerance），也不存在用宽容差掩盖的边界情况。审计的
`lhs/rhs/difference` 同样是精确整数域值。

## 测试与独立参考

- `tests/reference.py` 是**独立编写**的朴素解释器：只接受朴素 `dict`
  规格，直接做模运算，**不 import zkcirc**，用于给出期望值。
- 被测核心与独立参考的逐节点值，在确定性输入网格上逐一对照；
  `test_soundness.py` 还对每个中间槽枚举全部 97 个域值做单点篡改，
  验证审计必然捕获并定位（每个中间节点恰有一条输出系数为 1 的
  定义约束，故固定其他槽后中间槽唯一）。
- 独立点积复算仅作为**往返一致性的补充**，不作为期望值来源。

## 设计取舍

1. **见证直接求值而非解 R1CS**：DAG 无环且节点输出按拓扑序可唯一计算，
   直接求值最简单、确定且无歧义；R1CS 仅用于审计/约束表达。
2. **常量不占槽**：减少见证宽度；常量在约束矩阵中内联为常数槽系数。
3. **select 不引入辅助见证**：两条约束（选择式 + 布尔性）即完备，
   避免了无法写成线性 C 的二次辅助定义式。
4. **审计与见证生成分离**：`audit` 接受任何向量（包括被篡改的向量），
   因此既能验证合法见证，也能对伪造/损坏见证做逐条法医式定位。
5. **域固定为 p=97**：不做通用曲线/通用域参数化（题目明确固定 p=97）。

## 已知限制

- R1CS 约束的是变量**关系**，不保证每个输入都能从其余见证唯一反推：
  例如纯 `x*x` 电路无法区分 `x` 与 `−x (mod 97)`；`b=0` 的 `select`
  不约束未选分支。这是 R1CS 的标准关系语义，**中间槽**仍被其定义约束
  唯一钉住（已穷举验证），但输入唯一性需由电路设计者通过断言保证。
- **完全没有消费者的输入节点不出现在任何约束中**（标准 R1CS 行为），
  审计无法约束其值；需要约束某个输入时让它参与计算或 `assert_equal`。
- 不做 Witness 之外的证明系统、不做序列化/文件格式、不做电路优化
  （如公共子表达式重写）或消除死节点。
- 不是通用零知识证明框架：无可信设置、无证明/验证密钥、无链上验证器。
- 200 节点是硬接口边界；超出即拒绝，不做分批/分页处理。
