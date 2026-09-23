#!/usr/bin/env python3
"""Fixed-input demonstration for the zkcircuit library.

Runs entirely offline with the Python 3.14 standard library. It builds
one small deterministic circuit over GF(97), generates a witness,
cross-checks it against the independent DAG interpreter, and audits it.
Then it demonstrates an actually triggered rejection boundary: a
tampered witness (an intermediate wire modified by one) fails the audit
and the offending R1CS constraint is located and printed.

Run:  python demo.py
"""

import time

from zkcircuit import (
    PRIME,
    Circuit,
    MissingInputError,
    audit,
    evaluate,
    generate_witness,
)


def build_circuit():
    """Deterministic circuit.

        a, b          : inputs
        prod          = a * b            (shared intermediate)
        sum_ab        = prod + a
        choice        = select(b, sum_ab, const 3)
        check         : choice == b*sum_ab + (1-b)*3   (independently
                          recomputed mux -- holds for boolean b)
    """
    c = Circuit()
    three = c.const(3)
    one = c.const(1)
    a = c.input("a")
    b = c.input("b")
    prod = c.mul(a, b)                       # shared wire
    sum_ab = c.add(prod, a)
    choice = c.select(b, sum_ab, three)
    one_minus_b = c.add(one, c.mul(c.const(PRIME - 1), b))
    recomputed = c.add(c.mul(b, sum_ab), c.mul(one_minus_b, three))
    assertion = c.assert_equal(choice, recomputed)
    return c, dict(a=a, b=b, prod=prod, sum_ab=sum_ab, choice=choice,
                   assertion=assertion)


def main():
    t0 = time.perf_counter()
    print(f"zkcircuit demo over GF({PRIME})")
    print("=" * 60)

    circuit, refs = build_circuit()
    compiled = circuit.compile()
    print(f"circuit: {len(circuit.nodes)} DAG nodes, "
          f"{compiled.wire_count} wires "
          f"(wire 0 = constant 1), "
          f"{len(compiled.constraints)} sparse R1CS constraints")

    inputs = {"a": 12, "b": 1}
    print(f"fixed inputs: a={inputs['a']}, b={inputs['b']}")

    # --- 1. normal result: witness + independent reference + audit ------
    witness = generate_witness(compiled, inputs)
    reference = evaluate(circuit, inputs)

    prod_w = compiled.wire_of(refs["prod"])
    choice_w = compiled.wire_of(refs["choice"])
    print(f"prod   = a*b          = {witness[prod_w]} "
          f"(interpreter: {reference.of(refs['prod'])})")
    print(f"choice = select(...)  = {witness[choice_w]} "
          f"(interpreter: {reference.of(refs['choice'])})")
    print(f"z[0]    = {witness[0]} (always the constant 1)")

    report = audit(compiled, witness)
    print(f"audit on honest witness: {report.summary()}")

    # --- 2. rejected boundary: tamper with an intermediate wire ----------
    print("-" * 60)
    tampered = list(witness)
    old = tampered[prod_w]
    tampered[prod_w] = (old + 1) % PRIME
    print(f"tamper: intermediate wire {prod_w} (a*b) changed "
          f"{old} -> {tampered[prod_w]}")
    bad_report = audit(compiled, tampered)
    print(f"audit on tampered witness: {bad_report.summary()}")
    origin = compiled.origins[prod_w]
    print(f"tampered wire {prod_w} originates from "
          f"{origin['kind']} node#{origin['node']}")
    for failure in bad_report.failures:
        print(f"  located -> constraint #{failure.index} "
              f"'{failure.label}' at node#{failure.node_index}; "
              f"<A,z>*<B,z>={failure.lhs}, <C,z>={failure.rhs}")

    # --- 3. a genuinely raised exception boundary ------------------------
    print("-" * 60)
    try:
        generate_witness(compiled, {"a": 12})  # 'b' missing
    except MissingInputError as exc:
        print(f"exception boundary (as expected): {type(exc).__name__}: {exc}")

    elapsed = time.perf_counter() - t0
    print("=" * 60)
    print(f"done in {elapsed:.3f}s")


if __name__ == "__main__":
    main()
