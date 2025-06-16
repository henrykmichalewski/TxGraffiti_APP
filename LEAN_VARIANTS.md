# Lean Variants of Key Conjectures

This document pairs a selection of conjectures with the Lean snippet one can use when formalising them. The WOWII open problems are shown in a standard format produced by `utils/conjecture_generator.py`.  The Fajtlowicz conjectures are illustrated with simple stubs.

## WOWII Open Problems

/- Conjecture 1: For every finite simple graph G, independence number(G) ≤ 1 * vertex cover number(G) + 1. -/
conjecture independence_number_le_1_vertex_cover_number_plus_1 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, chromatic number(G) ≤ 1 * vertex cover number(G) + 1. -/
conjecture chromatic_number_le_1_vertex_cover_number_plus_1 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, matching number(G) ≤ 1 * vertex cover number(G) + 1. -/
conjecture matching_number_le_1_vertex_cover_number_plus_1 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, clique number(G) ≤ 1 * chromatic number(G) + 1. -/
conjecture clique_number_le_1_chromatic_number_plus_1 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, vertex cover number(G) ≤ 2 * matching number(G) + 0. -/
conjecture vertex_cover_number_le_2_matching_number (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, min edge cover(G) ≤ 1 * vertex cover number(G) + 1. -/
conjecture min_edge_cover_le_1_vertex_cover_number_plus_1 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, diameter(G) ≤ 2 * triameter(G) + 0. -/
conjecture diameter_le_2_triameter (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, randic index(G) ≤ 1 * independence number(G) + 1. -/
conjecture randic_index_le_1_independence_number_plus_1 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, harmonic index(G) ≤ 1 * independence number(G) + 2. -/
conjecture harmonic_index_le_1_independence_number_plus_2 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, sum connectivity index(G) ≤ 1 * independence number(G) + 3. -/
conjecture sum_connectivity_index_le_1_independence_number_plus_3 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, residue(G) ≤ 1 * independence number(G) + 0. -/
conjecture residue_le_1_independence_number (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, annihilation number(G) ≤ 2 * independence number(G) + 0. -/
conjecture annihilation_number_le_2_independence_number (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, sub total domination number(G) ≤ 1 * independence number(G) + 2. -/
conjecture sub_total_domination_number_le_1_independence_number_plus_2 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, slater(G) ≤ 1 * independence number(G) + 1. -/
conjecture slater_le_1_independence_number_plus_1 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, wiener index(G) ≤ 2 * independence number(G) + 3. -/
conjecture wiener_index_le_2_independence_number_plus_3 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, independence number(G) ≤ 1 * annihilation number(G) + 1. -/
conjecture independence_number_le_1_annihilation_number_plus_1 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, chromatic number(G) ≤ 1 * clique number(G) + 1. -/
conjecture chromatic_number_le_1_clique_number_plus_1 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, matching number(G) ≤ 1 * min edge cover(G) + 1. -/
conjecture matching_number_le_1_min_edge_cover_plus_1 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, triameter(G) ≤ 3 * radius(G) + 0. -/
conjecture triameter_le_3_radius (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, randic index(G) ≤ 1 * wiener index(G) + 1. -/
conjecture randic_index_le_1_wiener_index_plus_1 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, harmonic index(G) ≤ 1 * wiener index(G) + 2. -/
conjecture harmonic_index_le_1_wiener_index_plus_2 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, sum connectivity index(G) ≤ 1 * wiener index(G) + 2. -/
conjecture sum_connectivity_index_le_1_wiener_index_plus_2 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, residue(G) ≤ 1 * wiener index(G) + 0. -/
conjecture residue_le_1_wiener_index (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, annihilation number(G) ≤ 1 * wiener index(G) + 3. -/
conjecture annihilation_number_le_1_wiener_index_plus_3 (G : SimpleGraph V) [Fintype V] :

/- Conjecture 1: For every finite simple graph G, independence number(G) ≤ 1 * wiener index(G) + 2. -/
conjecture independence_number_le_1_wiener_index_plus_2 (G : SimpleGraph V) [Fintype V] :


## Sample Fajtlowicz Conjectures

Below are a handful of conjectures quoted from the README with simple Lean-style stubs illustrating how one might encode them.  These do not currently have formal definitions in the project.

```lean
/- Conjecture 21: If G is a simple connected graph, then b(G) ≥ CEIL(2dist_avg(B,V)) -/
conjecture fc21 (G : SimpleGraph V) [Fintype V] : Prop := by
  admit

/- Conjecture 22: If G is a simple connected graph, then CEIL(2dist(B,V)))≥ CEIL(2dist_avg(V)) -/
conjecture fc22 (G : SimpleGraph V) [Fintype V] : Prop := by
  admit

/- Conjecture 23: If G is a simple connected graph, then b(G) ≥ FLOOR[α(G) + dist_avg(M)/2] -/
conjecture fc23 (G : SimpleGraph V) [Fintype V] : Prop := by
  admit

/- Conjecture 74: If G is a simple connected graph, then tree(G) ≥ CEIL(2dist_avg(B,V)) -/
conjecture fc74 (G : SimpleGraph V) [Fintype V] : Prop := by
  admit

/- Conjecture 105: If G is a simple connected graph, then α(G) ≤ tree(G)*SQRT[domination(G)] - 1 -/
conjecture fc105 (G : SimpleGraph V) [Fintype V] : Prop := by
  admit

/- Conjecture 214: Let M = {v: λ(v) = λ_max(G)}. If G is a simple connected graph with n > 1 such that 3*g_2 (G¯) ≤ |M|, then G has a Hamiltonian path. -/
conjecture fc214 (G : SimpleGraph V) [Fintype V] : Prop := by
  admit

/- Conjecture 429: Let G be a connected graph on n > 3 vertices and M the vertices of maximum degree and D_avg(P) average of distance from each periphery vertex of graph. Then i(G) ≤  D_avg(P)*(α(G[N(M)]) + 1) -/
conjecture fc429 (G : SimpleGraph V) [Fintype V] : Prop := by
  admit
```
