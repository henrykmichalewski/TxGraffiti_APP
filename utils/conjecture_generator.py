#!/usr/bin/env python3
"""
conjecture_generator.py
-----------------------
Emit TxGraffiti-style Lean conjectures, interleaving English prose with Lean
`conjecture` stubs.

Examples
--------
# strongest ≤100 conjectures over all invariants, 1≤k≤4, 0≤c≤4
python3 utils/conjecture_generator.py --limit 100 > conjectures.lean

# only independence_number on the left, any rhs, 1≤k≤2, 0≤c≤3
python3 utils/conjecture_generator.py --lhs independence_number \
        --rhs '*' --k 1:2 --c 0:3 > few.lean
"""

from __future__ import annotations
import argparse, itertools, json, textwrap, sys
import networkx as nx

# -------------------------------------------------------------------------
#  configurable defaults
# -------------------------------------------------------------------------

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

# map short string → callable(G)         (tiny subset just for filtering step)
# add more as you wire up real invariant code later
INV_FUN: dict[str, callable[[nx.Graph], int | float]] = {
    "independence_number": lambda G: nx.algorithms.approximation.maximum_independent_set(G).__len__(),
    "chromatic_number":    lambda G: nx.algorithms.coloring.greedy_color(G).__len__(),
    "matching_number":     lambda G: nx.max_weight_matching(G, maxcardinality=True).__len__(),
    "diameter":            lambda G: nx.diameter(G) if nx.is_connected(G) else max(nx.diameter(c) for c in nx.connected_components(G)),
    "radius":              lambda G: nx.radius(G) if nx.is_connected(G) else min(nx.radius(G.subgraph(c)) for c in nx.connected_components(G)),
}

SMALL_GRAPHS = [
    nx.complete_graph(4),
    nx.cycle_graph(5),
    nx.path_graph(6),
]

HEADER = textwrap.dedent("""\
    import Mathlib.Data.Nat.Basic
    import Mathlib.Combinatorics.SimpleGraph.Basic

    namespace AutoGraffiti
    variable {V : Type*}
""")

# -------------------------------------------------------------------------
#  pretty-printers
# -------------------------------------------------------------------------

def english(lhs: str, k: int, rhs: str, c: int, idx: int) -> str:
    lhs_h, rhs_h = lhs.replace("_", " "), rhs.replace("_", " ")
    return f"Conjecture {idx}: For every finite simple graph G, " \
           f"{lhs_h}(G) ≤ {k} * {rhs_h}(G) + {c}."

def ident(lhs: str, k: int, rhs: str, c: int) -> str:
    return f"{lhs}_le_{k}_{rhs}" + ("" if c == 0 else f"_plus_{c}")

def lean_block(lhs: str, k: int, rhs: str, c: int, idx: int) -> str:
    comment = english(lhs, k, rhs, c, idx)
    rhs_term = f"{k} * {rhs} G" if k != 1 else f"{rhs} G"
    rhs_term += "" if c == 0 else f" + {c}"
    return textwrap.dedent(f"""\
        /- {comment} -/
        conjecture {ident(lhs,k,rhs,c)} (G : SimpleGraph V) [Fintype V] :
          {lhs} G ≤ {rhs_term} := by
          sorry
    """)

# -------------------------------------------------------------------------
#  dominance + counter-example filters
# -------------------------------------------------------------------------

def dominates(a: tuple[int,int], b: tuple[int,int]) -> bool:
    """(k,c) dominates (k',c')  ⇔  k ≤ k' and c ≤ c' and not equal."""
    k, c   = a
    k2, c2 = b
    return (k, c) != (k2, c2) and k <= k2 and c <= c2

def passes_small_graphs(lhs: str, k: int, rhs: str, c: int) -> bool:
    if lhs not in INV_FUN or rhs not in INV_FUN:
        return True        # can’t test, keep it
    lhs_f, rhs_f = INV_FUN[lhs], INV_FUN[rhs]
    for G in SMALL_GRAPHS:
        if lhs_f(G) > k * rhs_f(G) + c:
            return False   # counter-example found
    return True

# -------------------------------------------------------------------------
#  main
# -------------------------------------------------------------------------

def parse_range(r: str) -> range:
    lo, hi = map(int, r.split(":"))
    return range(lo, hi + 1)

def main() -> None:
    p = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    p.add_argument("--lhs", default="*", help="lhs invariant or * for all")
    p.add_argument("--rhs", default="*", help="rhs invariant or * for all")
    p.add_argument("--k",   default="1:4", help="inclusive range a:b for k")
    p.add_argument("--c",   default="0:4", help="inclusive range a:b for c")
    p.add_argument("--limit", "-n", type=int, default=100, help="max conjectures to emit")
    args = p.parse_args()

    lhs_list = INVARIANTS if args.lhs == "*" else [args.lhs]
    rhs_list = INVARIANTS if args.rhs == "*" else [args.rhs]
    k_range  = parse_range(args.k)
    c_range  = parse_range(args.c)

    # build the full search space
    raw: dict[tuple[str,str], list[tuple[int,int]]] = {}
    for lhs, rhs in itertools.product(lhs_list, rhs_list):
        if lhs == rhs:
            continue
        pairs = list(itertools.product(k_range, c_range))
        # dominance filter
        minimal = []
        for k, c in sorted(pairs):
            if not any(dominates((k2,c2), (k,c)) for k2,c2 in minimal):
                minimal.append((k,c))
        raw[(lhs, rhs)] = minimal

    # flatten, counter-example filter, cap at limit
    out_blocks = []
    idx = 1
    for (lhs, rhs), pairs in raw.items():
        for k, c in pairs:
            if passes_small_graphs(lhs, k, rhs, c):
                out_blocks.append(lean_block(lhs, k, rhs, c, idx))
                idx += 1
            if len(out_blocks) >= args.limit:
                break
        if len(out_blocks) >= args.limit:
            break

    sys.stdout.write(HEADER + "\n".join(out_blocks) + "\nend AutoGraffiti\n")

if __name__ == "__main__":
    main()

