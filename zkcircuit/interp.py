"""Independent reference interpreter for the expression DAG.

This module evaluates a :class:`~zkcircuit.dag.Circuit` DAG directly over
GF(97) -- it does NOT call the R1CS compiler or the witness generator.
Tests use it as the independent oracle that witness generation is
checked against (round-trip agreement is only a supplementary signal).

Semantics per node:
    const(v)        -> v
    input(name)     -> supplied value
    add(x, y)       -> (x + y) mod 97
    mul(x, y)       -> (x * y) mod 97
    select(b, x, y) -> x if b == 1, y if b == 0; any other b raises
                       NonBooleanSelectError (the interpreter enforces the
                       same booleanity contract the R1CS layer encodes as
                       b*(b-1) = 0)
    assert_equal(x, y) -> returns True if x == y, else raises
                          AssertionViolationError

Evaluation is memoised per node identity, so shared sub-DAGs are
evaluated once -- mirroring the single-witness-wire rule.
"""

from dataclasses import dataclass
from typing import Dict

from .dag import Circuit, Node
from .errors import (
    CircuitError,
    MissingInputError,
    UnknownInputError,
    ValidationError,
)
from .field import PRIME, validate_field_value


class NonBooleanSelectError(CircuitError):
    """A select node's selector evaluated to a value other than 0 or 1."""


class AssertionViolationError(CircuitError):
    """An assert_equal node's two sides evaluated to different values."""

    def __init__(self, node_index, lhs, rhs):
        self.node_index = node_index
        self.lhs = lhs
        self.rhs = rhs
        super().__init__(
            f"assert_equal at node#{node_index} violated: "
            f"{lhs} != {rhs} (mod {PRIME})"
        )


@dataclass(frozen=True)
class EvalResult:
    """Interpreter output: one value per value-producing node."""

    values: Dict[int, int]  # node index -> field value

    def of(self, node: Node) -> int:
        """Value of ``node`` (assert_equal nodes have none)."""
        return self.values[node.index]


def evaluate(circuit: Circuit, inputs: Dict[str, int]) -> EvalResult:
    """Evaluate every node of ``circuit`` over GF(97).

    Input mapping validation matches the witness generator exactly:
    unknown names raise :class:`UnknownInputError`, missing names raise
    :class:`MissingInputError`, non-canonical values raise
    :class:`ValidationError`.  The mapping is validated in full before
    any evaluation happens.
    """
    if not isinstance(circuit, Circuit):
        raise TypeError("evaluate(): first argument must be a Circuit")
    if not isinstance(inputs, dict):
        raise ValidationError(
            f"evaluate(): inputs must be a dict, got {type(inputs).__name__}"
        )

    declared = set(circuit.input_names)
    for key, value in inputs.items():
        if not isinstance(key, str):
            raise ValidationError(
                f"evaluate(): input name keys must be str, "
                f"got {type(key).__name__}"
            )
        if key not in declared:
            raise UnknownInputError(
                f"unknown input {key!r}: circuit declares "
                f"{list(circuit.input_names)}"
            )
        validate_field_value(value, where=f"evaluate(inputs[{key!r}])")
    missing = [n for n in circuit.input_names if n not in inputs]
    if missing:
        raise MissingInputError(f"missing values for input(s) {missing}")

    values: Dict[int, int] = {}
    for node in circuit.nodes:  # construction order is topological
        if node.op == "const":
            values[node.index] = node.value % PRIME
        elif node.op == "input":
            values[node.index] = inputs[node.name]
        elif node.op == "add":
            x, y = (values[c.index] for c in node.children)
            values[node.index] = (x + y) % PRIME
        elif node.op == "mul":
            x, y = (values[c.index] for c in node.children)
            values[node.index] = (x * y) % PRIME
        elif node.op == "select":
            b, x, y = (values[c.index] for c in node.children)
            if b not in (0, 1):
                raise NonBooleanSelectError(
                    f"select at node#{node.index}: selector b={b} is not "
                    f"boolean over GF({PRIME})"
                )
            values[node.index] = x if b == 1 else y
        elif node.op == "assert_equal":
            x, y = (values[c.index] for c in node.children)
            if x != y:
                raise AssertionViolationError(node.index, x, y)
        else:  # pragma: no cover - the builder only emits known ops
            raise CircuitError(f"unknown op {node.op!r}")
    return EvalResult(values=values)
