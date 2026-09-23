"""Expression DAG definition and circuit builder over GF(97).

Node types (``op``):

==========  ============================================
``const``   field constant, data in ``value``
``input``   named external input, name in ``name``
``add``     binary field addition, children (x, y)
``mul``     binary field multiplication, children (x, y)
``select``  ternary mux, children (b, x, y); b constrained
            to be boolean, value is x if b=1 else y
``assert_equal`` binary assertion, children (x, y); emits
            the constraint x - y = 0 and produces no value
==========  ============================================

A node is identified by object identity: referencing the *same* Node
object from several parents denotes a shared sub-DAG and allocates a
single witness wire. Two separately built but structurally identical
nodes are distinct and are never merged automatically.
"""

from dataclasses import dataclass, field
from typing import Optional, Tuple

from .errors import (
    CircuitError,
    DuplicateInputNameError,
    NodeLimitError,
    ValidationError,
)
from .field import validate_field_value

#: Hard upper bound on the number of nodes (assertions included) in a DAG.
MAX_NODES = 200

_NODE_SPECS = {
    "const": (0, False, False),
    "input": (0, False, True),
    "add": (2, False, False),
    "mul": (2, False, False),
    "select": (3, False, False),
    "assert_equal": (2, False, False),
}


@dataclass(frozen=True)
class Node:
    """One node of the expression DAG.

    Instances are created through :class:`Circuit` factory methods; the
    fields are immutable.  ``index`` is assigned by the circuit and used
    in error locations and constraint labels.
    """

    op: str
    children: Tuple["Node", ...] = ()
    value: Optional[int] = None
    name: Optional[str] = None
    index: Optional[int] = field(default=None, compare=False)

    def __repr__(self):
        if self.op == "const":
            return f"<node#{self.index} const {self.value}>"
        if self.op == "input":
            return f"<node#{self.index} input {self.name!r}>"
        return f"<node#{self.index} {self.op}>"


class Circuit:
    """A builder for an expression DAG over GF(97).

    Nodes must be constructed children-first: every child passed to a
    factory must already belong to this circuit, which makes cyclic DAGs
    impossible.  A failed factory call never mutates the circuit.
    """

    def __init__(self):
        self._nodes = []
        self._node_ids = set()
        self._input_names = {}

    # -- introspection ----------------------------------------------------

    @property
    def nodes(self):
        """All constructed nodes in construction (index) order."""
        return list(self._nodes)

    @property
    def input_names(self):
        """Tuple of declared input names in declaration order."""
        return tuple(self._input_names)

    def __len__(self):
        return len(self._nodes)

    # -- node factories ---------------------------------------------------

    def const(self, value) -> Node:
        """Create a constant node holding canonical field ``value``."""
        v = validate_field_value(value, where="const(value)")
        return self._make("const", (), value=v)

    def input(self, name) -> Node:
        """Create a named external input node.

        ``name`` must be a non-empty string and unique within the
        circuit.
        """
        if isinstance(name, bool) or not isinstance(name, str):
            raise ValidationError(
                f"input(name): name must be a str, "
                f"got {type(name).__name__}"
            )
        if not name:
            raise ValidationError("input(name): name must be non-empty")
        if name in self._input_names:
            raise DuplicateInputNameError(
                f"input({name!r}): an input with this name already exists "
                f"(node#{self._input_names[name].index})"
            )
        node = self._make("input", (), name=name)
        self._input_names[name] = node
        return node

    def add(self, x: Node, y: Node) -> Node:
        """Field addition node x + y."""
        return self._make("add", (x, y))

    def mul(self, x: Node, y: Node) -> Node:
        """Field multiplication node x * y."""
        return self._make("mul", (x, y))

    def select(self, b: Node, x: Node, y: Node) -> Node:
        """Multiplexer node: x when b == 1, y when b == 0.

        Compilation additionally enforces b*(b-1) = 0.
        """
        return self._make("select", (b, x, y))

    def assert_equal(self, x: Node, y: Node) -> Node:
        """Assertion node x == y; produces no witness value."""
        return self._make("assert_equal", (x, y))

    # -- internals --------------------------------------------------------

    def _make(self, op, children, *, value=None, name=None):
        spec = _NODE_SPECS.get(op)
        if spec is None:  # pragma: no cover - internal use only
            raise CircuitError(f"unknown op {op!r}")
        arity, _c, _n = spec
        if len(children) != arity:
            raise ValidationError(
                f"{op}: expected {arity} children, got {len(children)}"
            )
        for pos, ch in enumerate(children):
            if not isinstance(ch, Node):
                raise ValidationError(
                    f"{op}: child {pos} must be a Node, "
                    f"got {type(ch).__name__}"
                )
            if id(ch) not in self._node_ids:
                raise ValidationError(
                    f"{op}: child {pos} {ch!r} does not belong to this "
                    f"circuit (build children before their parents)"
                )
        if len(self._nodes) >= MAX_NODES:
            raise NodeLimitError(
                f"circuit already contains the maximum of {MAX_NODES} "
                f"nodes; cannot add {op}"
            )
        node = Node(
            op=op,
            children=tuple(children),
            value=value,
            name=name,
            index=len(self._nodes),
        )
        self._nodes.append(node)
        self._node_ids.add(id(node))
        return node

    # -- compilation ------------------------------------------------------

    def compile(self):
        """Compile the DAG into a sparse R1CS instance.

        Returns a :class:`~zkcircuit.r1cs.CompiledCircuit`.  Compilation is
        deterministic and does not mutate the builder.
        """
        from .r1cs import compile_circuit

        return compile_circuit(self)
