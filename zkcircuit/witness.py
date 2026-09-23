"""Witness generation and per-constraint auditing.

* :func:`generate_witness` fills every wire of a compiled circuit from
  user-supplied input values.  It is all-or-nothing: any invalid input
  raises before the witness is returned, and no partial state leaks to
  the caller.  Intermediate/auxiliary wires are computed by the
  generator and can never be set or overridden by the caller.
* :func:`audit` evaluates every sparse R1CS constraint against an
  arbitrary witness and reports each failing constraint individually,
  including the located left/right dot products.
"""

from dataclasses import dataclass
from typing import Dict, List, Optional

from .errors import (
    IntermediateOverrideError,
    MissingInputError,
    UnknownInputError,
    ValidationError,
)
from .field import PRIME, addmod, mulmod, validate_field_value
from .r1cs import CompiledCircuit


@dataclass(frozen=True)
class ConstraintFailure:
    """One R1CS constraint that did not hold for an audited witness.

    Attributes:
        index: position of the constraint in the compiled constraint list.
        label: semantic label, e.g. ``select_bool#5`` or ``assert_equal#9``.
        node_index: DAG node that emitted the constraint, when applicable.
        lhs: value of ``<A,z> * <B,z>`` modulo p.
        rhs: value of ``<C,z>`` modulo p.
    """

    index: int
    label: str
    node_index: Optional[int]
    lhs: int
    rhs: int

    def __str__(self):
        return (
            f"constraint #{self.index} ({self.label}) failed: "
            f"<A,z>*<B,z> = {self.lhs} != {self.rhs} = <C,z>"
        )


@dataclass
class AuditReport:
    """Result of :func:`audit` over every constraint.

    ``ok`` is True exactly when ``failures`` is empty.  ``checked`` is
    the number of constraints evaluated.
    """

    ok: bool
    checked: int
    failures: List[ConstraintFailure]

    def summary(self) -> str:
        if self.ok:
            return f"audit passed: all {self.checked} constraints hold"
        first = self.failures[0]
        return (
            f"audit FAILED: {len(self.failures)}/{self.checked} "
            f"constraints violated; first: {first}"
        )


def generate_witness(compiled: CompiledCircuit, inputs: Dict[str, int]):
    """Compute the full witness vector ``z`` for ``inputs``.

    ``z[0]`` is always 1; input wires take the supplied canonical
    values; every other wire is derived topologically by direct field
    evaluation of the DAG.

    Error semantics (raised before anything is returned; the caller's
    ``inputs`` mapping is never mutated):
      * :class:`~zkcircuit.errors.MissingInputError` -- a declared input
        has no value;
      * :class:`~zkcircuit.errors.UnknownInputError` -- a supplied key is
        not a declared input name;
      * :class:`~zkcircuit.errors.IntermediateOverrideError` -- a
        supplied key matches an internal slot label used in
        ``compiled.origins`` (defensive; intermediate wires have no
        user-facing name);
      * :class:`~zkcircuit.errors.ValidationError` -- any value is not a
        canonical field element (NaN/Infinity/bool/out-of-range/...).
    """
    if not isinstance(compiled, CompiledCircuit):
        raise TypeError(
            "generate_witness(): first argument must be a CompiledCircuit"
        )
    if not isinstance(inputs, dict):
        raise ValidationError(
            f"generate_witness(): inputs must be a dict, "
            f"got {type(inputs).__name__}"
        )

    # Validate the whole mapping first: never partially apply anything.
    internal_names = {
        f"#{o['node']}"
        for o in compiled.origins
        if o["kind"] in ("const", "add", "mul", "select")
    }
    seen = set()
    for key in inputs:
        if not isinstance(key, str):
            raise ValidationError(
                f"generate_witness(): input name keys must be str, "
                f"got {type(key).__name__}"
            )
        if key in seen:
            # dicts cannot have duplicate keys; guard anyway
            continue
        seen.add(key)
        if key not in compiled.input_wires:
            if key in internal_names:
                raise IntermediateOverrideError(
                    f"input {key!r} names an internal/intermediate slot; "
                    f"user inputs cannot override intermediate wires"
                )
            raise UnknownInputError(
                f"unknown input {key!r}: this circuit declares inputs "
                f"{list(compiled.input_wires)}"
            )
        validate_field_value(
            inputs[key], where=f"generate_witness(inputs[{key!r}])"
        )

    missing = [
        name for name in compiled.input_wires if name not in inputs
    ]
    if missing:
        raise MissingInputError(
            f"missing values for input(s) {missing}; "
            f"all declared inputs must be supplied"
        )

    z = [0] * compiled.wire_count
    z[0] = 1

    for name, wire in compiled.input_wires.items():
        z[wire] = inputs[name]

    # Derive intermediate wires straight from the DAG in node-index
    # order (parents are always built after children, hence topologic).
    for n in compiled._nodes:
        if n.op == "input" or n.op == "assert_equal":
            continue
        w = compiled.node_wires[n.index]
        if n.op == "const":
            z[w] = n.value % PRIME
        elif n.op == "add":
            z[w] = addmod(
                z[compiled.node_wires[n.children[0].index]],
                z[compiled.node_wires[n.children[1].index]],
            )
        elif n.op == "mul":
            z[w] = mulmod(
                z[compiled.node_wires[n.children[0].index]],
                z[compiled.node_wires[n.children[1].index]],
            )
        elif n.op == "select":
            b, x, y = (
                z[compiled.node_wires[c.index]] for c in n.children
            )
            if b not in (0, 1):
                raise ValidationError(
                    f"select at node#{n.index}: selector b={b} is not "
                    f"boolean (required b*(b-1)=0 over GF({PRIME})); "
                    f"no canonical select value exists"
                )
            z[w] = x if b == 1 else y
        # no other ops exist; compilation would have failed otherwise
    return z


def dot(sparse: Dict[int, int], z) -> int:
    """Sparse dot product ``sum(coef * z[wire]) mod p``."""
    total = 0
    for wire, coef in sparse.items():
        total = (total + coef * z[wire]) % PRIME
    return total


def _validate_witness(compiled: CompiledCircuit, z):
    if not isinstance(z, (list, tuple)):
        raise ValidationError(
            f"audit(): witness must be a list/tuple, "
            f"got {type(z).__name__}"
        )
    if len(z) != compiled.wire_count:
        raise ValidationError(
            f"audit(): witness length {len(z)} does not match wire count "
            f"{compiled.wire_count}"
        )
    for i, v in enumerate(z):
        if isinstance(v, bool):
            raise ValidationError(f"audit(): z[{i}] is bool; use int 0/1")
        if not isinstance(v, int):
            raise ValidationError(
                f"audit(): z[{i}] must be an int, got {type(v).__name__}"
            )
        if not 0 <= v < PRIME:
            raise ValidationError(
                f"audit(): z[{i}]={v} is outside [0, {PRIME})"
            )
    if z[0] != 1:
        raise ValidationError("audit(): z[0] must be the constant 1")


def audit(compiled: CompiledCircuit, z) -> AuditReport:
    """Check every R1CS constraint against witness ``z``.

    Returns an :class:`AuditReport` listing every failing constraint.
    Malformed witness vectors raise :class:`ValidationError`; a
    well-formed but unsatisfying witness produces a report with
    ``ok=False`` (it does not raise).
    """
    if not isinstance(compiled, CompiledCircuit):
        raise TypeError("audit(): first argument must be a CompiledCircuit")
    _validate_witness(compiled, z)

    failures: List[ConstraintFailure] = []
    for con in compiled.constraints:
        a = dot(con.A, z)
        b = dot(con.B, z)
        lhs = (a * b) % PRIME
        rhs = dot(con.C, z)
        if lhs != rhs:
            failures.append(
                ConstraintFailure(
                    index=con.index,
                    label=con.label,
                    node_index=con.node_index,
                    lhs=lhs,
                    rhs=rhs,
                )
            )
    return AuditReport(
        ok=not failures,
        checked=len(compiled.constraints),
        failures=failures,
    )
