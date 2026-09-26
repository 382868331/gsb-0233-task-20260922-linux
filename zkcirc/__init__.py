"""zkcirc: 域 p=97 上算术约束电路（R1CS）的见证生成与审计。

仅依赖 Python 标准库。本模块实现题目契约规定的有限数学子集，
不生成真实链上证明，也不宣称兼容任何行业级零知识证明协议。
"""

from .field import P, parse_scalar
from .circuit import (
    MAX_NODES,
    Circuit,
    Node,
    Constraint,
    VariableInfo,
    CompiledCircuit,
    compile_circuit,
    generate_witness,
    audit,
    ConstraintResult,
    AuditReport,
)
from .errors import (
    ZkCircError,
    CircuitBuildError,
    CircuitLimitError,
    CompileError,
    WitnessError,
    NonBooleanSelectError,
    AssertEqualError,
    GuardedAssertError,
    UnknownInputError,
    UnexpectedInputError,
    AuditError,
)

__all__ = [
    "P",
    "MAX_NODES",
    "parse_scalar",
    "Circuit",
    "Node",
    "Constraint",
    "VariableInfo",
    "CompiledCircuit",
    "compile_circuit",
    "generate_witness",
    "audit",
    "ConstraintResult",
    "AuditReport",
    "ZkCircError",
    "CircuitBuildError",
    "CircuitLimitError",
    "CompileError",
    "WitnessError",
    "NonBooleanSelectError",
    "AssertEqualError",
    "GuardedAssertError",
    "UnknownInputError",
    "UnexpectedInputError",
    "AuditError",
]
