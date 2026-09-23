"""Sparse R1CS data structures and DAG-to-R1CS compilation.

An R1CS instance over GF(97) is a list of constraints

    <A, z> * <B, z> = <C, z>   (mod 97)

where each of A, B, C is a *sparse* vector given as ``{wire_index:
coefficient}`` (zero coefficients are never stored) and ``z`` is the
witness vector whose wire 0 is always the field constant 1.

Wire layout
-----------
* 0            -- the constant 1
* 1..I         -- one wire per declared ``input`` node, in declaration
                  order (== node construction order)
* after inputs -- one wire per value-producing non-input node
                  (``const``/``add``/``mul``/``select``) in topological
                  (node index) order
* ``assert_equal`` nodes own no wire; they only emit a constraint

A shared node (the same ``Node`` object referenced by multiple parents)
appears once in the DAG and therefore owns exactly one wire.

Constraint encodings (a, b, c, s are wire indices)
--------------------------------------------------
* add, c = a + b::

      (z_a + z_b) * 1 = z_c
* mul, c = a * b::

      z_a * z_b = z_c
* select s = select(b, x, y), written s - y = b * (x - y)::

      z_b * (z_x - z_y) = (z_s - z_y)
      z_b * (z_b - 1)   = 0          # extra booleanity constraint
* assert_equal(x, y)::

      (z_x - z_y) * 1 = 0
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from .dag import Circuit, Node
from .field import PRIME


@dataclass(frozen=True)
class Constraint:
    """One sparse R1CS constraint ``<A,z>*<B,z> = <C,z>``."""

    index: int
    A: Dict[int, int]
    B: Dict[int, int]
    C: Dict[int, int]
    label: str
    node_index: Optional[int]

    def __repr__(self):
        return f"<Constraint #{self.index} {self.label}>"


@dataclass
class CompiledCircuit:
    """The result of compiling a :class:`~zkcircuit.dag.Circuit`.

    Attributes:
        prime: field modulus (97).
        wire_count: length of every valid witness vector; wire 0 is the
            constant 1.
        constraints: sparse R1CS constraints in emission order.
        origins: ``origins[i]`` describes where wire ``i`` comes from.
            Kinds: ``constant``, ``input``, ``const``, ``add``, ``mul``,
            ``select``.
        input_wires: mapping input name -> wire index.
        node_wires: mapping node index -> wire index (assert_equal nodes
            and nothing else are absent).
    """

    prime: int
    wire_count: int
    constraints: List[Constraint]
    origins: List[dict]
    input_wires: Dict[str, int]
    node_wires: Dict[int, int]
    # back-reference for node labels; not part of the value-level API
    _nodes: List[Node] = field(default_factory=list, repr=False)

    def wire_of(self, node: Node) -> int:
        """Return the witness wire index owned by ``node``.

        ``assert_equal`` nodes own no wire.
        """
        if not isinstance(node, Node):
            raise TypeError("wire_of(): argument must be a Node")
        if node.index is None or node.index not in self.node_wires:
            raise ValueError(
                f"node {node!r} owns no witness wire "
                f"(assert_equal nodes and foreign nodes do not)"
            )
        return self.node_wires[node.index]

    def input_names(self) -> Tuple[str, ...]:
        return tuple(self.input_wires)


def _lin(*terms) -> Dict[int, int]:
    """Build a sparse linear combination from (wire, coef) terms.

    Unlike a dict literal, this aggregates terms on the *same* wire
    (needed when a node's children share a wire, e.g. add(x, x)), then
    drops coefficients that reduce to zero.
    """
    combined: Dict[int, int] = {}
    for wire, coef in terms:
        combined[wire] = (combined.get(wire, 0) + coef) % PRIME
    return {wire: coef for wire, coef in combined.items() if coef}


def compile_circuit(circuit: Circuit) -> CompiledCircuit:
    """Compile a DAG into a sparse :class:`CompiledCircuit` over GF(97).

    Deterministic; the builder is not mutated.
    """
    if not isinstance(circuit, Circuit):
        raise TypeError("compile_circuit(): argument must be a Circuit")

    nodes = circuit.nodes

    # -- assign wires -----------------------------------------------------
    origins: List[dict] = [{"kind": "constant", "node": None, "value": 1}]
    input_wires: Dict[str, int] = {}
    node_wires: Dict[int, int] = {}

    for n in nodes:
        if n.op == "input":
            wire = len(origins)
            input_wires[n.name] = wire
            node_wires[n.index] = wire
            origins.append({"kind": "input", "node": n.index, "name": n.name})

    for n in nodes:
        if n.op == "input" or n.op == "assert_equal":
            continue
        wire = len(origins)
        node_wires[n.index] = wire
        if n.op == "const":
            origin = {
                "kind": "const",
                "node": n.index,
                "value": n.value,
            }
        else:
            origin = {
                "kind": n.op,
                "node": n.index,
                "children": [c.index for c in n.children],
            }
        origins.append(origin)

    # -- emit constraints --------------------------------------------------
    constraints: List[Constraint] = []

    def emit(A, B, C, label, node_index):
        constraints.append(
            Constraint(
                index=len(constraints),
                A=A,
                B=B,
                C=C,
                label=label,
                node_index=node_index,
            )
        )

    for n in nodes:
        w = node_wires.get(n.index)
        if n.op == "const":
            # constant wire: z_w * 1 = value
            emit(
                _lin((w, 1)),
                {0: 1},
                _lin((0, n.value)),
                f"const#{n.index}",
                n.index,
            )
        elif n.op == "input":
            # free variable; no constraint
            continue
        elif n.op == "add":
            a = node_wires[n.children[0].index]
            b = node_wires[n.children[1].index]
            emit(
                _lin((a, 1), (b, 1)),
                {0: 1},
                _lin((w, 1)),
                f"add#{n.index}",
                n.index,
            )
        elif n.op == "mul":
            a = node_wires[n.children[0].index]
            b = node_wires[n.children[1].index]
            emit(
                _lin((a, 1)),
                _lin((b, 1)),
                _lin((w, 1)),
                f"mul#{n.index}",
                n.index,
            )
        elif n.op == "select":
            bb, xx, yy = (node_wires[c.index] for c in n.children)
            # z_b * (z_x - z_y) = (z_s - z_y)
            emit(
                _lin((bb, 1)),
                _lin((xx, 1), (yy, -1)),
                _lin((w, 1), (yy, -1)),
                f"select#{n.index}",
                n.index,
            )
            # extra booleanity: z_b * (z_b - 1) = 0
            emit(
                _lin((bb, 1)),
                _lin((bb, 1), (0, -1)),
                {},
                f"select_bool#{n.index}",
                n.index,
            )
        elif n.op == "assert_equal":
            xx = node_wires[n.children[0].index]
            yy = node_wires[n.children[1].index]
            emit(
                _lin((xx, 1), (yy, -1)),
                {0: 1},
                {},
                f"assert_equal#{n.index}",
                n.index,
            )

    return CompiledCircuit(
        prime=PRIME,
        wire_count=len(origins),
        constraints=constraints,
        origins=origins,
        input_wires=dict(input_wires),
        node_wires=dict(node_wires),
        _nodes=list(nodes),
    )
