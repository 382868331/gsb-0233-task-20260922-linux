# zkcirc — p=97 算术约束电路的见证生成与审计

一个离线、零第三方依赖的教学型可复用库：在素数域 **p = 97** 上把表达式
DAG（`add` / `mul` / `const` / `input` / `select` / `assert_equal`）
编译为稀疏 **R1CS**（`<A,z>·<B,z> = <C,z> (mod 97)`，`z[0] ≡ 1`），
生成见证，并对任意见证向量做**逐约束审计**、报告每条失败约束的位置与
左右侧值。

本轮迭代在不改动任何旧入口语义的前提下，新增 **2..8 位有符号整数
（二补码）的加减与比较**（`signed_input` / `signed_const` / `sadd` /
`ssub` / `slt` / `sle` / `seq`）：溢出策略**只有回绕**；约束层面
逐位生成比特布尔性（`b(b−1)=0`）与全加器进位 / 全减器借位链，
**不是**用一条域加法模拟；每个比特、进位、借位、字槽都输出来源映射。

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

# 固定输入演示（现场计算，约 0.05 秒，远小于 90 秒；无 sleep、无预录结果）
python demo.py
```

## 目录结构

```
zkcirc/            本题库（可导入包）
  __init__.py        公开接口导出
  field.py           模 97 域工具、标量入参契约（拒绝 bool/NaN/Infinity）；
                     2..8 位有符号整数工具（位宽校验/区间/二补码比特/回绕）
  circuit.py         DAG 构建、R1CS 编译（含逐位布尔性与进位/借位链）、
                     见证生成、逐约束审计
  errors.py          可定位的错误类型层次
tests/
  reference.py       独立参考：朴素域解释器 + 独立点积；有符号朴素解释器
                     （进位/借位/同或/与链，均不 import zkcirc）
  test_field.py      域工具契约
  test_builder.py    DAG 构建校验与 200 节点上限
  test_circuit.py    编译/见证/审计：独立解释器对照、非布尔 select、
                     共享子图、中间值篡改、未知输入、稀疏格式
  test_soundness.py  确定性穷举：全部 97 个域值的单点篡改检测
  test_signed.py     有符号能力：w=2/3/4 全枚举对照独立参考、w=2..8 比较、
                     手算回绕边界、约束结构、逐槽 97 值篡改、非法输入、混用
demo.py            固定输入演示（A 域电路 + D 有符号电路）
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
```

- 节点按下标顺序追加，**只能引用更早的节点**，故 DAG 天然无环；
  插入顺序即拓扑序。
- 同一节点下标传给多个父节点即表示**共享子图**；编译时只占一个见证槽。
- **上限：最多 200 个节点**（`zkcirc.MAX_NODES`）。超出抛
  `CircuitLimitError`，失败的追加不产生任何部分变更。

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
| `signed_inputs` / `signed_layouts` / `signed_cmp_layouts` | 有符号能力的位宽登记与逐槽源码映射（见第 5 节；旧电路中为空） |

- `Constraint(index, node, tag, origin, a, b, c)`：`a/b/c` 均为
  `tuple[(var_index, coeff)]`，按变量下标升序、系数已模 97 规约、
  零系数被剔除。`tag` ∈ `add | mul | select_value | select_booleanity |
  assert_value | assert_equal`；`origin` 是人读语义说明。
- `VariableInfo(slot, role, node, name, kind)`：`role` 为
  `constant_one`（槽 0）、`input` 或 `intermediate`。
- **常量节点不占见证槽**：在约束中内联为常数槽 0 上的系数。

编译出的约束（`v` 为节点输出槽，`lin(n)` 为操作数线性项）：

| 节点 | 约束 |
|---|---|
| `add` | `1 · v = lin(x) + lin(y)` |
| `mul` | `lin(x) · lin(y) = v` |
| `select` | `b · (lin(x)−lin(y)) = v−lin(y)` **且** `b·(b−1) = 0` |
| `assert_equal` | `1 · v = lin(x)` **且** `(lin(x)−lin(y)) · 1 = 0` |

两条 select 约束在域 p=97 上恰好等价于「`b∈{0,1}` 且
`v = b·x + (1−b)·y`」：布尔性方程在域中只有 0、1 两个解。

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
| 有符号输入越出 w 位区间 | `SignedInputError`（带 name/width/low/high/value） |
| 值非 int、bool、NaN、Infinity、其他类型 | `TypeError` / `ValueError` |

### 4. 审计：`audit(compiled, witness) -> AuditReport`

- 见证形状非法（长度不符、元素非规范域元素、含 bool/float/NaN/Infinity、
  `z[0]≠1`）抛 `AuditError`。
- 形状合法则**始终返回报告**：`AuditReport.ok` 与
  `results: tuple[ConstraintResult]`；`ConstraintResult` 含
  `index / node / tag / origin / satisfied / lhs / rhs / difference`。
- `report.failures` 给出全部失败约束，可直接定位到 DAG 节点与约束语义。

### 5. 2..8 位有符号整数（二补码）

```python
c = Circuit()
a  = c.signed_input("a", 4)          # 4 位有符号命名输入，合法值 [-8, 7]
b  = c.signed_input("b", 4)
k  = c.signed_const(-1, 4)           # 4 位有符号常量（必须落在区间内）
s  = c.sadd(a, b)                    # 有符号加，溢出仅按二补码回绕
d  = c.ssub(a, b)                    # 有符号减（回绕）
lt = c.slt(a, b)                     # a <  b，输出被布尔性钉住的 0/1 标志
le = c.sle(a, b)                     # a <= b
eq = c.seq(a, b)                     # a == b
```

- 位宽 `w` 必须是 **2..8 的 int**（拒绝 bool/float）；有符号运算/比较
  的两个操作数必须都是有符号值节点且**位宽相同**，否则构造期即抛
  `CircuitBuildError`，失败的追加不改变电路。
- 有符号输入与普通 `input` **共用名字空间**；见证生成时按名字给一个
  普通 Python int，必须落在 `[-2**(w-1), 2**(w-1)-1]`。**越界不回绕、
  不模 97 规约**——回绕只是 `sadd/ssub` 的溢出策略，越界输入抛
  `SignedInputError`（带 `name/width/low/high/value/kind`）；
  bool/普通 float 抛 `TypeError`，NaN/Infinity 抛 `ValueError`。
- 比较输出是 0/1 标志（不是有符号值），可以直接喂给旧 `select` 或
  旧域运算；有符号值节点的**字槽**（二补码无符号字 mod 97）也可被
  `add/mul/select/assert_equal` 引用——但注意 w≥5 时字可超过 96，
  字槽是「无符号字 mod 97」，跨域相等断言需设计者自行保证口径。

**见证展开（约束不是域运算模拟）。** 一个有符号值节点 `v` 展开为：

| 槽 | 数量 | 约束 |
|---|---|---|
| 结果比特 `b_k`（小端，`b_{w-1}` 为符号位） | w | 每个 `b_k·(b_k−1) = 0`（布尔性） |
| 进位/借位 `c_k` | w+1 | `c_0 = 0`；每个 `c_k·(c_k−1) = 0`；逐位全加/全减关系 |
| 字槽 `word` | 1 | `1·word = Σ 2^k·b_k (mod 97)` |

- `sadd` 第 k 位全加器：`1·s_k = x_k + y_k + c_k − 2·c_{k+1}`，
  配 `s_k、c_{k+1}` 的布尔性，在 0/1 上恰唯一确定标准进位；
  最高进位 `c_w` 不约束（丢弃）即**溢出回绕**。
- `ssub` 第 k 位全减器：`1·d_k = x_k − y_k − r_k + 2·r_{k+1}`，
  同理唯一确定标准借位，最高借位丢弃。
- `signed_input` 的字槽是**命名输入槽**：用户给出的整数由见证生成器
  分解为比特，`word = Σ2^k·b_k` 把输入与逐位分解互相钉住；
  只篡改某个输入比特而不改字槽，`signed_word` 约束必然失败。
- `signed_const` 不占见证槽（与旧 const 一致），各比特以字面 0/1
  内联在常数槽上。

**比较的实现。** 有符号序通过「翻转两数符号位后的无符号序」实现：

- `slt`：对 `u_x=(x xor 2^{w-1})`、`u_y` 做 w 位无符号减法（同一条
  全减器链），标志 `f = r_w`（最高借位）；`sle` 交换两侧并取
  `f = 1 − r_w`。
- `seq`：逐位同或 `e_k = 1 − x_k − y_k + 2·x_k·y_k`
  （R1CS：`2x_k·y_k = e_k − 1 + x_k + y_k`），再用与链
  `q_0 = e_0, q_k = q_{k-1}·e_k`，标志 `f = q_{w-1}`。
- 全部中间比特、借位、同或位、链位都是带布尔性约束的见证槽。

**新增编译产物字段（旧字段全部不变）：**

| 字段 | 含义 |
|---|---|
| `signed_inputs` | `{输入名: 位宽}`，只列有符号输入（普通输入在 `inputs`） |
| `signed_layouts` | `{节点: SignedLayout(node,width,bit_slots,carry_slots,word_slot)}` |
| `signed_cmp_layouts` | `{节点: SignedCmpLayout(...)}`：含 `flag_slot`、`diff_bits/borrows`（slt/sle）或 `eq_prod/eq_chain`（seq） |

所有这些槽同时出现在 `sources` 中（`role` 为 input/intermediate，
`kind` 为 `signed_bit/signed_carry/signed_borrow/signed_word/
signed_flag/signed_diff_bit/signed_eq_prod/signed_eq_chain`），
可由槽反查节点、由节点反查全部槽——即题面要求的**源码映射**。

新增约束 tag：`sbit_booleanity / scarry_booleanity / sadd_bit /
ssub_bit / signed_carry0 / signed_borrow0 / signed_cmp_bit /
signed_word / signed_flag / seq_prod / seq_chain / signed_pin`。

新增公开工具（`zkcirc` 包导出）：`check_width / signed_range /
signed_to_bits / bits_to_signed / wrap_signed` 与常量
`MIN_SIGNED_WIDTH=2`、`MAX_SIGNED_WIDTH=8`。

## 输入与错误语义（总契约）

- 域元素一律是 `0..96` 的 Python **int**；接受任意 int 并模 97 规约，
  **负数有确定的模运算含义**（如 `-1 → 96`）。
- **整数参数拒绝 bool**：`True/False` 即使是 `int` 子类型也抛 `TypeError`。
- **拒绝 float**：`NaN` 与 `±Infinity` 以 `ValueError` 单独点名；
  普通 float 抛 `TypeError`（域算术完全精确，不存在浮点域元素）。
- 所有错误都带定位信息（节点下标 / 约束下标 / 输入名 / 槽位），
  非法输入不会被静默纠正。
- **有符号整数输入不做模 97 规约、不回绕**：必须是 w 位区间内的
  普通 int，越界抛 `SignedInputError`；回绕仅发生在 `sadd/ssub`
  的运算结果上。
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
- 有符号部分：`reference.py` 另有一套独立的二补码朴素解释器
  （`ref_eval_signed`），逐位计算标准进位/借位、符号位翻转比较、
  逐位同或与与链；`test_signed.py` 对 w=2/3/4 的**全部输入组合**
  逐槽（比特/进位/借位/字/标志）对照参考，并对复合电路的**每个
  见证槽枚举全部 97 个域值**做单点篡改，审计必须拒绝；w=5..8
  取边界与代表点核对。回绕与比较另用手算例子（7+1=−8、−8−1=7、
  −1<1 与无符号 15>1 的区别）独立复核。
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
6. **有符号整数逐位约束而非域运算模拟**：即使 p=97 能直接容纳 8 位
   字，`sadd/ssub` 仍显式展开 w 个结果比特 + w+1 个进位/借位，用
   全加/全减器方程 + 逐位布尔性约束，使「比特为 0/1、进位为标准
   进位」成为可审计的关系；比较复用同一条全减器链（符号位翻转），
   相等用逐位同或 + 与链，避免任何不可信的整体字比较。
7. **溢出只有回绕**：最高进位/借位不约束（丢弃），结果由低 w 位
   二补码解释；本迭代不提供饱和/报错/条件溢出标志。

## 已知限制

- R1CS 约束的是变量**关系**，不保证每个输入都能从其余见证唯一反推：
  例如纯 `x*x` 电路无法区分 `x` 与 `−x (mod 97)`；`b=0` 的 `select`
  不约束未选分支。这是 R1CS 的标准关系语义，**中间槽**仍被其定义约束
  唯一钉住（已穷举验证），但输入唯一性需由电路设计者通过断言保证。
- **完全没有消费者的输入节点不出现在任何约束中**（标准 R1CS 行为），
  审计无法约束其值；需要约束某个输入时让它参与计算或 `assert_equal`。
  有符号输入只要被任一有符号运算消费，其全部比特与字槽即被约束。
- 有符号能力**只含二补码加减与 `< / <= / ==` 比较**：不含乘法、
  除法/取模、截断/扩展位宽转换、`!= / > / >=`（可由现有标志取反
  构造）、溢出标志或饱和语义；比较结果只有 0/1，不能直接再做
  `sadd`（需先由电路设计者显式转换）。
- 有符号字槽以「无符号字 mod 97」入域：p=97 装不下整个 8 位字节
  （0..255），字槽只是把比特打包供旧域运算使用的**冗余槽**，真实
  表示永远是那 w 个被布尔性钉住的比特。w≤6（字 ≤63）时字槽与字节
  一一对应；**w≥7 时不同字节可能模 97 同余**（如 w=8 的 −128、−31、
  66 对应无符号 0、97、194，字槽都为 0）。后果有两点：
  (1) 对字槽直接做旧域 `assert_equal`/`mul` 不能唯一反推有符号值；
  (2) 一个**完全没有任何消费者**的 w≥7 `signed_input`，其
  `word = Σ2^k b_k (mod 97)` 约束允许另一组合法 0/1 比特（等价于
  另一个同余有符号值）——这与「无消费者的输入不被约束」是同一类
  标准 R1CS 行为。一旦该输入被 `sadd/ssub/比较` 消费，进位/借位/
  同或链按比特把它唯一钉死，伪造的替代分解必被审计拒绝（已穷举验证）。
- 有符号节点展开会线性增加见证宽度（每个 sadd/ssub 约 2w+2 槽、
  3w+3 条约束；8 位二元运算约 18 槽）；200 个 DAG 节点仍是硬上限，
  但大位宽电路的见证规模可能较大（本迭代不做公共子表达式合并）。
- 不做 Witness 之外的证明系统、不做序列化/文件格式、不做电路优化
  （如公共子表达式重写）或消除死节点。
- 不是通用零知识证明框架：无可信设置、无证明/验证密钥、无链上验证器。
- 200 节点是硬接口边界；超出即拒绝，不做分批/分页处理。
