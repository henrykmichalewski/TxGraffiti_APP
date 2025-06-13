#!/usr/bin/env python3
"""
conjecture_generator.py
=======================

A tiny standalone script that **from Python** emits TxGraffiti-style Lean conjectures.
It interleaves natural-language comments with Lean `conjecture` stubs, matching the
style of *Graffiti Conjectures 100*.

Usage
-----
    python conjecture_generator.py                # prints 100 conjectures to stdout
    python conjecture_generator.py 50 > foo.lean  # prints first 50 into foo.lean

Customisation
-------------
* Edit the `INVARIANTS` list to include the graph-invariant names you care about
  (they must already exist—or be stubbed—in your Lean environment).
* Tweak `K_RANGE` and `C_RANGE` for the coefficient search space.
* Adjust `BOUND_LIMIT` or pass a CLI argument to control how many conjectures are
  emitted.

The output is pure Lean source: you can pipe it into a `.lean` file or paste the
string into the canvas.
"""

import itertools
import sys
import textwrap

# ---- PARAMETERS ---------------------------------------------------------

INVARIANTS = [
    "independence_number",
    "chromatic_number",
    "matching_number",
    "clique_number",
    "vertex_cover_number",
    "min_edge_cover",
    "diameter",
    "radius",
    "triameter",
    "randic_index",
    "harmonic_index",
    "sum_connectivity_index",
    "residue",
    "annihilation_number",
    "sub_total_domination_number",
    "slater",
    "wiener_index",
]

K_RANGE = [1, 2, 3, 4]   # multiplicative coefficients k
C_RANGE = [1, 2, 3, 4]   # additive shifts c

BOUND_LIMIT = 100        # default number of conjectures produced

# ---- HELPER -------------------------------------------------------------

def pretty_comment(idx: int, lhs: str, k: int, rhs: str, c: int) -> str:
    lhs_name = lhs.replace("_", " ")
    rhs_name = rhs.replace("_", " ")
    return textwrap.fill(
        f"Conjecture {idx}: For every finite simple graph G, "
        f"{lhs_name}(G) ≤ {k} * {rhs_name}(G) + {c}.",
        width=78,
    )

def lean_ident(lhs: str, k: int, rhs: str, c: int) -> str:
    return f"{lhs}_le_{k}_{rhs}{'' if c==0 else f'_plus_{c}'}"

def conjecture_block(idx: int, lhs: str, k: int, rhs: str, c: int) -> str:
    comment = pretty_comment(idx, lhs, k, rhs, c)
    ident   = lean_ident(lhs, k, rhs, c)
    rhs_term = f"{k} * {rhs} G + {c}" if k != 1 else f"{rhs} G + {c}"
    return textwrap.dedent(f"""
        /- {comment} -/
        conjecture {ident} (G : SimpleGraph V) [Fintype V] :
          {lhs} G ≤ {rhs_term} := by
          sorry
    """)

# ---- MAIN ---------------------------------------------------------------

def main() -> None:
    try:
        limit = int(sys.argv[1])
    except (IndexError, ValueError):
        limit = BOUND_LIMIT

    header = textwrap.dedent("""
        import Mathlib.Data.Nat.Basic
        import Mathlib.Combinatorics.SimpleGraph.Basic

        namespace AutoGraffiti

        variable {V : Type*}
    """)

    conjectures = []
    idx = 1
    for lhs, rhs in itertools.product(INVARIANTS, repeat=2):
        if lhs == rhs:
            continue  # skip trivial self-bounds
        for k, c in itertools.product(K_RANGE, C_RANGE):
            conjectures.append(conjecture_block(idx, lhs, k, rhs, c))
            idx += 1
            if len(conjectures) >= limit:
                break
        if len(conjectures) >= limit:
            break
    lean_source = header + "\n".join(conjectures) + "\nend AutoGraffiti\n"
    print(lean_source)

if __name__ == "__main__":
    main()
