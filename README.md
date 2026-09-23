# zkcircuit — 算术约束电路的见证生成与审计（GF(97)）

离线零知识工具链的可复用模块：把表达式 DAG 编译为稀疏 R1CS
（`<A,z> * <B,z> = <C,z>`，z 首位恒为 1），从用户输入生成完整见证，
并逐约束审计任意见证、定位失败约束。**不生成真实链上证明**。

## 环境

- Python **3.14.7**（Linux 原生），**仅标准库**，安装 Python 后无任何其他依赖。
- 核心、测试、演示全部离线：无网络、账号、密钥、数据库、Docker。

## 接口

```python
from zkcircuit import Circuit, generate_witness, audit, evaluate

c = Circuit()                 # 表达式 DAG 构建器，最多 200 个节点
x = c.input("x")              # 具名外部输入（名字唯一）
y = c.input("y")
s = c.mul(x, y)               # add / mul / const / select(b,x,y) / assert_equal
t = c.add(s, x)
picked = c.select(y, t, c.const(3))
c.assert_equal(picked, c.add(c.mul(y, t), c.mul(c.add(c.const(1), c.mul(c.const(96), y)), c.const(3))))

cc = c.compile()              # -> CompiledCircuit（稀疏约束 + 变量来源）
z = generate_witness(cc, {"x": 5, "y": 1})   # 见证向量 z，z[0] == 1
report = audit(cc, z)         # 逐约束审计
ref = evaluate(c, {"x": 5, "y": 1})          # 独立参考解释器（不经过编译器）
```

### 公开数据结构

- `CompiledCircuit`：`prime`、`wire_count`、`constraints`（`Constraint(index,
  A, B, C, label, node_index)`，A/B/C 为 `{线号: 系数}` 稀疏字典，零系数不存储）、
  `origins`（每根线的来源：`constant`/`input`/`const`/`add`/`mul`/`select`，
  含节点号与子节点）、`input_wires`、`node_wires`、`wire_of(node)`。
- `AuditReport`：`ok`、`checked`、`failures`（`ConstraintFailure(index, label,
  node_index, lhs, rhs)`）、`summary()`。
- `EvalResult`：`values`（节点号 → 域值）、`of(node)`。

### 线（wire）布局

`z[0]` 恒为 1；随后按声明顺序每个 `input` 一根线；再按节点序每个产生值的
节点（`const`/`add`/`mul`/`select`）一根线。`assert_equal` 不占线，只产生约束。
**共享节点（同一 Node 对象被多处引用）只分配一根线/一个见证槽**；
结构相同但分别构建的节点不会被合并。

### 约束编码

| 节点 | 约束 |
|---|---|
| `const v` | `z_w * 1 = v` |
| `add(a,b)=c` | `(z_a + z_b) * 1 = z_c` |
| `mul(a,b)=c` | `z_a * z_b = z_c` |
| `select(b,x,y)=s` | `z_b*(z_x - z_y) = z_s - z_y`，**外加** `z_b*(z_b-1) = 0` |
| `assert_equal(x,y)` | `(z_x - z_y) * 1 = 0` |

同一根线被两个子节点共享时系数会累加（如 `add(x,x)` → 系数 2）。

## 输入上限与错误语义

- DAG 节点数上限 **200**（含 assert 节点），超出抛 `NodeLimitError`；
  构建失败不会留下部分变更。
- 数值契约：域元素必须为标准型整数 `[0, 97)`；**拒绝 NaN/Infinity、
  非整浮点、bool、越界整数**（不静默取模），抛 `ValidationError` 并
  在消息中给出位置（如 `generate_witness(inputs['x'])`）。
- 见证生成是全有或全无：先整体校验输入映射再求值。
  - 缺少输入 → `MissingInputError`
  - 未知输入名 → `UnknownInputError`
  - 试图覆盖中间/辅助槽 → `IntermediateOverrideError`
  - `select` 选择子非 0/1 → `ValidationError`（见证生成器拒绝；
    手工构造的含非布尔 b 的见证会在 audit 中被 `select_bool#N` 约束定位）
- `audit` 对格式错误的见证抛 `ValidationError`；对格式良好但不满足约束的
  见证**不抛异常**，返回 `ok=False` 的报告并逐条列出失败约束。
- 所有异常都继承 `CircuitError`。

## 误差口径

本库**不产生任何浮点结果**：全部算术为 GF(97) 上的精确整数模运算，
误差恒为 0，不存在容差问题。浮点数仅允许以“有限且整值”的形式作为
输入出现（如 `3.0` → `3`），其余一律拒绝。

## 设计取舍

- **共享按对象身份**：同一 `Node` 对象即共享子图，编译器不做结构哈希/
  公共子表达式消除——语义透明、可预测。
- **见证由 DAG 直接求值生成**：生成器与 R1CS 约束是两条独立路径，
  audit 才是两者的交叉验证点；参考解释器 `evaluate` 是第三条独立实现，
  测试用它作对照（不调用编译器/见证生成器取期望值）。
- **assert_equal 不产生见证值**，只产生一条约束；解释器中对应语义为
  不满足时抛 `AssertionViolationError`。
- **select 非布尔即拒绝**：见证生成器直接报错而非生成一个必然审计失败
  的见证；audit 仍能对任何手工构造的见证定位 `select_bool` 违例。

## 已知限制

- 域固定为 GF(97)，不可配置；值必须在 `[0, 97)`，不做隐式取模。
- 仅实现本题契约的六种节点与 R1CS 编译，**不宣称兼容** circom、
  bellman、arkworks 等任何行业标准格式；不生成、不验证真实证明。
- 无优化（不做约束消除/常量折叠）；`const` 也占一根线并产生一条约束。
- 节点数上限 200 是硬接口边界；解释器同样按此规模设计，未做大规模
  性能调优。

## 命令

```bash
python -m unittest discover -s tests -v   # 运行全部测试
python demo.py                            # 固定输入演示（<1 秒）
```

`demo.py` 真实计算并打印：一个正常结果（见证生成 + 解释器对照 +
审计通过），以及一个实际触发的边界（篡改中间线后审计失败并定位到
具体约束；另演示 `MissingInputError` 异常边界）。
