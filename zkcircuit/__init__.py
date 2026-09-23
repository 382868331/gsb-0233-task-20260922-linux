"""zkcircuit -- witness generation and auditing for arithmetic constraint
circuits (R1CS) over GF(97).

Public API
----------
Building a DAG:
    Circuit, Node, MAX_NODES

Compiling to sparse R1CS:
    CompiledCircuit, Constraint  (via ``Circuit.compile()``)

Witness generation and auditing:
    generate_witness, audit, AuditReport, ConstraintFailure

Independent reference interpreter:
    evaluate, EvalResult, NonBooleanSelectError, AssertionViolationError

Errors (all derive from CircuitError):
    ValidationError, NodeLimitError, DuplicateInputNameError,
    MissingInputError, UnknownInputError, IntermediateOverrideError

Field:
    PRIME (= 97), validate_field_value
"""

from .dag import MAX_NODES, Circuit, Node
from .errors import (
    CircuitError,
    DuplicateInputNameError,
    IntermediateOverrideError,
    MissingInputError,
    NodeLimitError,
    UnknownInputError,
    ValidationError,
    WitnessInputError,
)
from .field import PRIME, validate_field_value
from .interp import (
    AssertionViolationError,
    EvalResult,
    NonBooleanSelectError,
    evaluate,
)
from .r1cs import CompiledCircuit, Constraint
from .witness import (
    AuditReport,
    ConstraintFailure,
    audit,
    generate_witness,
)

__all__ = [
    "MAX_NODES",
    "PRIME",
    "AssertionViolationError",
    "AuditReport",
    "Circuit",
    "CircuitError",
    "CompiledCircuit",
    "Constraint",
    "ConstraintFailure",
    "DuplicateInputNameError",
    "EvalResult",
    "IntermediateOverrideError",
    "MissingInputError",
    "Node",
    "NodeLimitError",
    "NonBooleanSelectError",
    "UnknownInputError",
    "ValidationError",
    "WitnessInputError",
    "audit",
    "evaluate",
    "generate_witness",
    "validate_field_value",
]

__version__ = "1.0.0"
