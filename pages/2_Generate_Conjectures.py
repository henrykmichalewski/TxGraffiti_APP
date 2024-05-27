import streamlit as st
import pandas as pd
from fractions import Fraction
from functions import (
    make_all_upper_linear_conjectures,
    make_all_lower_linear_conjectures,
    dalmatian,
    filter_conjectures,
    invariants,
    booleans,
    make_graph_dataframe_from_edgelists
)

DATA_FILE = "training-data/data.csv"

TEX_MAP = {
    "<=": r"\leq",
    ">=": r"\geq",
    "domination_number": r"\gamma(G)",
    "independence_number": r"\alpha(G)",
    "chromatic_number": r"\chi(G)",
    "clique_number": r"\omega(G)",
    "vertex_cover_number": r"\beta(G)",
    "zero_forcing_number": r"Z(G)",
    "total_zero_forcing_number": r"Z_t(G)",
    "connected_zero_forcing_number": r"Z_c(G)",
    "power_domination_number": r"\gamma_P(G)",
    "total_domination_number": r"\gamma_t(G)",
    "connected_domination_number": r"\gamma_c(G)",
    "independent_domination_number": r"i(G)",
    "matching_number": r"\mu(G)",
    "min_maximal_matching_number": r"\gamma_e(G)",
    "min_degree": r"\delta(G)",
    "max_degree": r"\Delta(G)",
    "diameter": r"\text{diam}(G)",
    "radius": r"\text{rad}(G)",
    "order": r"n(G)",
    "size": r"m(G)",
    "residue": r"R(G)",
    "annihilation_number": r"a(G)",
    "sub_total_domination_number": r"\text{sub}_t(G)",
    "slater": r"sl(G)",
    "k_slater_index": r"sl(G, k)",
    "k_residual_index": r"R(G, k)",
    "triameter": r"\text{tri}(G)",
    "randic_index": r"\text{randic}(G)",
    "harmonic_index": r"\text{harmonic}(G)",
    "sum_connectivity_index": r"\text{sum}_c(G)",
    "(order - domination_number)": r"(n(G) - \gamma(G))",
    "(order - total_domination_number)": r"(n(G) - \gamma_t(G))",
    "(order - connected_domination_number)": r"(n(G) - \gamma_c(G))",
    "(order - independence_number)": r"(n(G) - \alpha(G))",
    "(order - power_domination_number)": r"(n(G) - \gamma_P(G))",
    "(order - zero_forcing_number)": r"(n(G) - Z(G))",
    "(order - diameter)": r"(n(G) - \text{diam}(G))",
    "(order - radius)": r"(n(G) - \text{rad}(G))",
    "(order - triameter)": r"(n(G) - \text{tri}(G))",
    "(size - radius)": r"(m(G) - \text{rad}(G))",
    "(order - independent_domination_number)": r"(n(G) - i(G))",
    "(order - chromatic_number)" : r"(n(G) - \chi(G))",
    "(order - matching_number)" : r"(n(G) - \mu(G))",
    "(order - min_maximal_matching_number)" : r"(n(G) - \gamma_e(G))",
    "(order - min_degree)" : r"(n(G) - \delta(G))",
    "(order - max_degree)" : r"(n(G) - \Delta(G))",
    "(order - clique_number)" : r"(n(G) - \omega(G))",
    "(order - residue)" : r"(n(G) - R(G))",
    "(order - annihilation_number)" : r"(n(G) - a(G))",
    "(order - sub_total_domination_number)" : r"(n(G) - \text{sub}_t(G))",
    "(order - slater)" : r"(n(G) - sl(G))",
    "(order - k_slater_index)" : r"(n(G) - sl(G, k))",
    "(order - k_residual_index)" : r"(n(G) - R(G, k))",
    "min_edge_cover" : r"\beta'(G)",
    "[(annihilation_number + residue)/ max_degree]" : r"\frac{a(G) + R(G)}{\Delta(G)}",
    "[order/ max_degree]" : r"\frac{n(G)}{\Delta(G)}",
    "[order/ (max_degree + 1)]" : r"\frac{n(G)}{\Delta(G) + 1}",
    "[order/ (max_degree - 1)]" : r"\frac{n(G)}{\Delta(G) - 1}",
    "[order/ (max_degree + 2)]": r"\frac{n(G)}{\Delta(G) + 2}",
    "(residue + annihilation_number)" : "(R(G) + a(G))",
    "a connected graph" : r"$\text{If } G \text{ is a connected graph, then}$",
    "a connected and bipartite graph": r"$\text{If } G \text{ is a connected and bipartite graph, then}$",
    "an eulerian graph": r"$\text{If } G \text{ is an eulerian graph, then}$",
    "a connected and eulerian graph": r"$\text{If } G \text{ is a connected and eulerian graph, then}$",
    "a connected and planar graph": r"$\text{If } G \text{ is a connected and planar graph, then}$",
    "a connected and regular graph": r"$\text{If } G \text{ is a connected and } r \text{-regular graph with } r >0 \text{, then}$",
    "a connected and cubic graph": r"$\text{If } G \text{is a connected and cubic graph, then}$",
    "a connected graph which is not K_n": r"$\text{If } G \text{ is a connected graph with } G \neq K_n \text{, then}$",
    "a connected and triangle-free graph": r"$\text{If } G \text{ is a connected and triangle-free graph, then}$",
    "a connected and at-free graph": r"$\text{If } G \text{ is a connected and at-free graph, then}$",
    "a tree graph": r"$\text{If } G \text{ is a non-trivial tree, then}$",
    "a connected and chordal graph": r"$\text{If } G \text{ is a connected and chordal graph, then}$",
    "a connected and claw-free graph": r"$\text{If } G \text{ is a connected and claw-free graph, then}$",
    "a connected graph with maximum degree at most 3": r"$\text{If } G \text{ is a connected graph with } \Delta(G) \leq 3 \text{, then}$",
    "a connected graph which is not K_n and has maximum degree at most 3": r"$\text{If } G \text{ is a connected graph with } G \neq K_n \text{ and } \Delta(G) \leq 3 \text{, then}$",
    "a connected, claw-free, and cubic graph": r"$\text{If } G \text{ is a connected, claw-free, and cubic graph, then}$",
    "a connected, planar, and cubic graph": r"$\text{If } G \text{ is a connected, planar, and cubic graph, then}$",
    "a connected and cubic graph which is not K_4": r"$\text{If } G \neq K_4 \text{ is a connected and cubic graph, then}$",
    "a connected and well-covered graph": r"$\text{If } G \text{ is a connected and well-covered graph, then}$",
    "a connected graph with diameter at most 3": r"$\text{If } G \text{ is a connected graph with } \text{diam}(G) \leq 3 \text{, then}$",
    "a connected and planar graph with diameter at most 3": r"$\text{If } G \text{ is a connected and planar graph with } \text{diam}(G) \leq 3 \text{, then}$",
    "a connected graph with a total domination number equal to the domination number": r"$\text{If } G \text{ is a connected graph with } \gamma_t(G) = \gamma(G) \text{, then}$",
    "a connected_graph with min_degree at least 2": r"$\text{If } G \text{ is a connected graph with } \delta(G) \geq 2 \text{, then}$",
    "a connected_graph with min_degree at least 3": r"$\text{If } G \text{ is a connected graph with } \delta(G) \geq 3 \text{, then}$",
    "a connected_graph with min_degree at least 4": r"$\text{If } G \text{ is a connected graph with } \delta(G) \geq 4 \text{, then}$",
    "a connected and bipartite graph with min_degree at least 2": r"$\text{If } G \text{ is a connected and bipartite graph with } \delta(G) \geq 2 \text{, then}$",
    "a connected and bipartite graph with min_degree at least 3": r"$\text{If } G \text{ is a connected and bipartite graph with } \delta(G) \geq 3 \text{, then}$",
    "a connected and bipartite graph with min_degree at least 4": r"$\text{If } G \text{ is a connected and bipartite graph with } \delta(G) \geq 4 \text{, then}$",
    "a connected and planar graph with min_degree at least 2": r"$\text{If } G \text{ is a connected and planar graph with } \delta(G) \geq 2 \text{, then}$",
    "a connected and planar graph with min_degree at least 3": r"$\text{If } G \text{ is a connected and planar graph with } \delta(G) \geq 3 \text{, then}$",
    "a connected and planar graph with min_degree at least 4": r"$\text{If } G \text{ is a connected and planar graph with } \delta(G) \geq 4 \text{, then}$",
    "a connected graph which is not K_n with min_degree at least 2": r"$\text{If } G \neq K_n \text{ is a connected graph with } \delta(G) \geq 2 \text{, then}$",
    "a connected graph which is not K_n with min_degree at least 3": r"$\text{If } G \neq K_n \text{ is a connected graph with } \delta(G) \geq 3 \text{, then}$",
    "a connected graph which is not K_n with min_degree at least 4": r"$\text{If } G \neq K_n \text{ is a connected graph with } \delta(G) \geq 4 \text{, then}$",
    "a connected and triangle-free graph with min_degree at least 2": r"$\text{If } G \text{ is a connected and triangle-free graph with } \delta(G) \geq 2 \text{, then}$",
    "a connected and triangle-free graph with min_degree at least 3": r"$\text{If } G \text{ is a connected and triangle-free graph with } \delta(G) \geq 3 \text{, then}$",
    "a connected and triangle-free graph with min_degree at least 4": r"$\text{If } G \text{ is a connected and triangle-free graph with } \delta(G) \geq 4 \text{, then}$",
    "a connected and at-free graph with min_degree at least 2": r"$\text{If } G \text{ is a connected and at-free graph with } \delta(G) \geq 2 \text{, then}$",
    "a connected and at-free graph with min_degree at least 3": r"$\text{If } G \text{ is a connected and at-free graph with } \delta(G) \geq 3 \text{, then}$",
    "a connected and at-free graph with min_degree at least 4": r"$\text{If } G \text{ is a connected and at-free graph with } \delta(G) \geq 4 \text{, then}$",
    "a connected and claw-free graph with min_degree at least 2": r"$\text{If } G \text{ is a connected and claw-free graph with } \delta(G) \geq 2 \text{, then}$",
    "a connected and claw-free graph with min_degree at least 3": r"$\text{If } G \text{ is a connected and claw-free graph with } \delta(G) \geq 3 \text{, then}$",
    "a connected and claw-free graph with min_degree at least 4": r"$\text{If } G \text{ is a connected and claw-free graph with } \delta(G) \geq 4 \text{, then}$",
    "a connected graph with min_degree at least 2 and maximum degree at most 3": r"$\text{If } G \text{ is a connected graph with } \delta(G) \geq 2 \text{ and } \Delta(G) \leq 3 \text{, then}$",
    "a connected and chordal graph with min_degree at least 2": r"$\text{If } G \text{ is a connected and chordal graph with } \delta(G) \geq 2 \text{, then}$",
    "a connected and chordal graph with min_degree at least 3": r"$\text{If } G \text{ is a connected and chordal graph with } \delta(G) \geq 3 \text{, then}$",
    "a connected and bull-free graph": r"$\text{If } G \text{ is a connected and bull-free graph, then}$",
    "a connected and diamond-free graph": r"$\text{If } G \text{ is a connected and diamond-free graph, then}$",
    "a connected, cubic, and diamond-free graph": r"$\text{If } G \text{ is a connected, cubic, and diamond-free graph, then}$",

}

DEF_MAP = {
    "domination_number": r"""A *dominating set* of $G$ is a set $D \subseteq V(G)$ of vertices such that every vertex in $G$ is either in $D$
    or adjacent to a vertex in $D$. The *domination number* of a graph $G$, denoted by $\gamma(G)$, is the minimum cardinality of a
    dominating set of $G$.""",
    "independence_number": r"""An *independent set* of a graph $G$ is a set $I \subseteq V(G)$ of vertices such that no two vertices in $I$ are adjacent.
    The *independence number* of a graph $G$, denoted by $\alpha(G)$, is the maximum cardinality of an independent set of $G$.""",
    "chromatic_number": r"""The chromatic number of a graph $G$, denoted by $\chi(G)$, is the minimum number of colors needed
    to color the vertices of $G$ such that no two adjacent vertices have the same color. A coloring of $G$ is an assignment of
    colors to the vertices of $G$ such that no two adjacent vertices have the same color.""",
    "clique_number": r"""A *clique* in $G$ is a set of vertices that induces a complete subgraph of $G$. The *clique number* of a graph $G$, denoted by $\omega(G)$, is the maximum cardinality of a clique in $G$.""",
    "vertex_cover_number": r"""A *vertex cover* of $G$ is a set $C \subseteq V(G)$ of vertices such that every edge in $G$ is incident to at least one
    vertex in $C$. The *vertex cover number* of a graph $G$, denoted by $\beta(G)$, is the minimum cardinality of a
    vertex cover of $G$.""",
    "zero_forcing_number": r"""A *zero forcing set* of $G$ is a set $S \subseteq V(G)$ of vertices such that if the vertices in $S$ are initially colored blue and
    all other vertices are initially colored white, then the coloring process will eventually turn all vertices blue. The *zero forcing number* of a graph $G$, denoted by $Z(G)$, is the minimum size of a zero forcing
    set of $G$.""",
    "total_zero_forcing_number": r"""A *total zero forcing set* of $G$ is a set $S \subseteq V(G)$ of vertices with no isolates, such that if the vertices in $S$ are initially
    colored blue and all other vertices are initially colored white, then the coloring process will eventually turn all vertices blue
    and white. The *total (zero) forcing number* of a graph $G$, denoted by $Z_t(G)$, is the minimum size of a total
    zero forcing set of $G$.""",
    "connected_zero_forcing_number": r"""A *connected zero forcing set* of $G$ is a set $S \subseteq V(G)$ of vertices such that if the vertices in $S$ are initially colored blue and all other vertices are initially colored white, then the coloring process will eventually turn all vertices blue and white. The *connected zero forcing number* of a graph $G$, denoted by $Z_c(G)$, is the minimum size of a connected zero forcing set of $G$.""",
    "total_domination_number" : r"""A *total dominating set* of $G$ is a set $D \subseteq V(G)$ of vertices such that every vertex in $G$ is adjacent
    to a vertex in $D$. The *total domination number* of a graph $G$, denoted by $\gamma_t(G)$, is the minimum cardinality of a total
    dominating set of $G$. """,
    "min_edge_cover": r"""A *minimum edge cover* of $G$ is a set $E \subseteq E(G)$ of edges such that every vertex in $G$ is incident to an edge in $E$. The *minimum edge cover number* of a graph $G$, denoted by $\beta'(G)$, is the minimum cardinality of a minimum edge cover of $G$.""",
    "randic_index": r"""The Randić index of a graph $G$ is a degree sequence graph invariant denoted by $\text{randic}(G)$.""",
    "connected_domination_number" : r"""A *connected dominating set* of $G$ is a dominating set $D \subseteq V(G)$ of vertices such that the subgraph induced by $D$ is connected.
    The *connected domination number* of a graph $G$, denoted by $\gamma_c(G)$, is the minimum cardinality of a connected dominating set of $G$.""",
    "independent_domination_number" : r"""The independent domination number of a graph $G$, denoted by $i(G)$, is the minimum cardinality of an independent
    dominating set of $G$. An independent dominating set of $G$ is a set $D \subseteq V(G)$ of vertices such that $D$ is independent and every vertex in $G$ is adjacent to a vertex in $D$.""",
    "power_domination_number" : r"""The power domination number of a graph $G$, denoted by $\gamma_P(G)$, is the minimum cardinality of a power dominating set of $G$.""",
    "matching_number" : r"""A *matching* in $G$ is a set of edges that do not share any common vertices. The *matching number* of a graph $G$, denoted by $\mu(G)$, is the maximum cardinality of a matching in $G$.""",
    "min_maximal_matching_number" : r"""The minimum maximal matching number of a graph $G$, denoted by $\gamma_e(G)$, is the minimum cardinality of a maximal matching in $G$.""",
    "min_degree" : r"""The minimum degree of a graph $G$, denoted by $\delta(G)$, is the minimum degree of a vertex in $G$.""",
    "max_degree" : r"""The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.""",
    "diameter" : r"""The diameter of a graph $G$, denoted by $\text{diam}(G)$, is the maximum distance between any two vertices in $G$.""",
    "radius" : r"""The radius of a graph $G$, denoted by $\text{rad}(G)$, is the minimum distance between any two vertices in $G$.""",
    "triameter": r"""The triameter of a graph $G$is denoted by $\text{tri}(G)$.""",
    "order" : r"""The order of a graph $G$, denoted by $n(G)$, is the number of vertices in $G$.""",
    "size" : r"""The size of a graph $G$, denoted by $m(G)$, is the number of edges in $G$.""",
    "residue" : r"""The residue of a graph $G$, denoted by $R(G)$, is the number of zeros at the termination of the Havel-Hakimi proccess on
    the degree sequence of $G$.""",
    "harmonic_index": r"""The harmonic index of a graph $G$ is a degree sequence graph invariant denoted by $\text{harmonic}(G)$.""",
    "annihilation_number" : r"""The annihilation number of a graph $G$, denoted by $a(G)$, is a degree sequence invariant introduced by R. Pepper.""",
    "sub_total_domination_number" : r"""The sub-total domination number of a graph $G$ is denoted by $\text{sub}_t(G)$.""",
    "slater" : r"""The Slater number of a graph $G$ is a degree sequence graph invariant denoted by $sl(G)$.""",
    "k_slater_index": r"""The $k$-Slater index of a graph $G$, denoted by $sl(G, k)$, is the smallest integer $k \geq 1$ so that $\text{sub}_k(G) \geq \gamma(G)$,
     where $\text{sub}_k(G)$ is the sub-$k$-domination number of $G$.""",
    "k_residual_index" : r"""The $k$-residual index of a graph $G$, denoted by $R(G, k)$, is the smallest integer $k \geq 1$ so that $\text{R}_k(G) \geq \alpha(G)$,
    where $\text{R}_k(G)$ is the $k$-residue of $G$ and $\alpha(G)$ is the independence number of $G$.""",
    "(order - domination_number)":  r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The domination number of a graph $G$, denoted by $\gamma(G)$, is the minimum cardinality of a dominating set of $G$.
    A dominating set of $G$ is a set $D \subseteq V(G)$ of vertices such that every vertex in $G$ is either in $D$ or adjacent to a vertex in $D$.""",
    "(order - total_domination_number)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The total domination number of a graph $G$,
    denoted by $\gamma_t(G)$, is the minimum cardinality of a total dominating set of $G$. A total dominating set of $G$ is a set $D \subseteq V(G)$ of vertices such that every vertex in $G$ is adjacent to a vertex in $D$.""",
    "(order - connected_domination_number)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The connected domination number of a graph $G$,
    denoted by $\gamma_c(G)$, is the minimum cardinality of a connected dominating set of $G$. A connected dominating set of $G$ is a dominating set $D \subseteq V(G)$ of vertices such that the subgraph induced by $D$ is connected.""",
    "(order - power_domination_number)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The power domination number of a graph $G$, denoted by $\gamma_P(G)$,
    is the minimum cardinality of a power dominating set of $G.""",
    "(order - zero_forcing_number)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The zero forcing number of a graph $G$, denoted by $Z(G)$, is the minimum size of a zero forcing set of $G$.
    A zero forcing set of $G$ is a set $S \subseteq V(G)$ of vertices such that if the vertices in $S$ are initially colored blue and all other vertices are initially colored white, then the coloring process will eventually turn all vertices blue.""",
    "(order - diameter)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The diameter of a graph $G$, denoted by $\text{diam}(G)$, is the maximum distance between any two vertices in $G$.""",
    "(order - radius)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The radius of a graph $G$, denoted by $\text{rad}(G)$, is the minimum distance between any two vertices in $G$.""",
    "(order - triameter)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The triameter of a graph $G$is denoted by $\text{tri}(G)$.""",
    "(order - independent_domination_number)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The independent domination number of a graph $G$, denoted by $i(G)$, is the minimum cardinality of an independent dominating set of $G$.
    An independent dominating set of $G$ is a set $D \subseteq V(G)$ of vertices such that $D$ is independent and every vertex in $G$ is adjacent to a vertex in $D$.""",
    "(order - chromatic_number)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The chromatic number of a graph $G$, denoted by $\chi(G)$, is the minimum number of colors needed to color the
    vertices of $G$ such that no two adjacent vertices have the same color.""",
    "(order - matching_number)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The matching number of a graph $G$, denoted by $\mu(G)$, is the maximum cardinality of a matching in $G$.
    A matching in $G$ is a set of edges that do not share any common vertices.""",
    "(order - min_maximal_matching_number)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The minimum maximal matching number of a graph $G$, denoted by $\gamma_e(G)$, is the minimum cardinality of a maximal matching in $G$.""",
    "(order - min_degree)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The minimum degree of a graph $G$, denoted by $\delta(G)$, is the minimum degree of a vertex in $G.""",
    "(order - max_degree)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G.""",
    "(order - clique_number)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The clique number of a graph $G$, denoted by $\omega(G)$, is the maximum cardinality of a clique in $G.
    A clique in $G$ is a set of vertices that induces a complete subgraph of $G.""",
    "(order - residue)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The residue of a graph $G$, denoted by $R(G)$, is the number of zeros at the termination of the Havel-Hakimi proccess on the degree sequence of $G.""",
    "(order - annihilation_number)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The annihilation number of a graph $G$, denoted by $a(G)$, is a degree sequence invariant introduced by R. Pepper.""",
    "(order - sub_total_domination_number)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The sub-total domination number of a graph $G$ is denoted by $\text{sub}_t(G)$.""",
    "(order - slater)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The Slater number of a graph $G$ is a degree sequence graph invariant denoted by $sl(G)$.""",
    "(order - k_slater_index)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The $k$-Slater index of a graph $G$, denoted by $sl(G, k)$, is the smallest integer $k \geq 1$ so that $\text{sub}_k(G) \geq \gamma(G)$.""",
    "(order - k_residual_index)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The $k$-residual index of a graph $G$, denoted by $R(G, k)$, is the smallest integer $k \geq 1$ so that $\text{R}_k(G) \geq \alpha(G)$.""",
    "[(annihilation_number + residue)/ max_degree]": r"""The annihilation number of a graph $G$, denoted by $a(G)$, is a degree sequence invariant introduced by R. Pepper. The residue of a graph $G$, denoted by $R(G)$, is the number of zeros at the termination of the Havel-Hakimi proccess on the degree sequence of $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.""",
    "[order/ max_degree]": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G.""",
    "[order/ (max_degree + 1)]": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G.""",
    "[order/ (max_degree - 1)]": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G.""",
    "[order/ (max_degree + 2)]": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G.""",
    "(residue + annihilation_number)": r"""The residue of a graph $G$, denoted by $R(G)$, is the number of zeros at the termination of the Havel-Hakimi proccess on the degree sequence of $G$. The annihilation number of a graph $G$, denoted by $a(G)$, is a degree sequence invariant introduced by R. Pepper.""",
    "a connected graph": r"""A connected graph is a graph in which there is a path between every pair of vertices.""",
    "a connected and bipartite graph": r"""A connected and bipartite graph is a graph in which the vertices can be partitioned into two sets such that
    no two vertices in the same set are adjacent.""",
    "an eulerian graph": r"""An *Eulerian trail* (or *Eulerian path*) is a trail in a finite graph that visits every edge exactly once (allowing for revisiting vertices).
    Similarly, an *Eulerian circuit* or *Eulerian cycle* is an Eulerian trail that starts and ends on the same vertex. The term *Eulerian graph* has two common meanings in graph theory.
    One meaning is a graph with an Eulerian circuit, and the other is a graph with every vertex of even degree. These definitions coincide for connected graphs.""",
    "a connected and planar graph": r"""A *planar graph* is a graph that can be embedded in the plane without any edges crossing.""",
    "a connected and regular graph": r"""A connected and $r$-regular graph with $r>0$ is a non-trivial graph in which every vertex has degree $r$.""",
    "a connected and cubic graph": r"""A connected and cubic graph is a graph in which every vertex has degree 3.""",
    "a connected graph which is not K_n": r"""A connected graph which is not $K_n$ is a graph with $n$ vertices that is not a complete graph.""",
    "a connected and triangle-free graph": r"""A connected and triangle-free graph is a graph in which no three vertices form a triangle.""",
    "a connected and at-free graph": r"""A connected graph is a graph in which there is a path between every pair of vertices. Three vertices of a graph form an *asteroidal triple*
    if every two of them are connected by a path avoiding the neighborhood of the third. A graph is *at-free* if it does not contain any asteroidal triple.""",
    "a tree graph": r"""A tree is a connected graph with no cycles.""",
    "a connected and chordal graph": r"""A *chordal graph* is one in which all cycles of four or more vertices have a *chord*, which is an edge that is not part of the cycle but connects two
    vertices of the cycle. Equivalently, every induced cycle in the graph should have exactly three vertices.""",
    "a connected and claw-free graph": r"""A *claw* is another name for the complete bipartite graph $K_{1,3}$ (that is, a star graph comprising three edges, three leaves, and a central vertex).
    A *claw-free graph* is a graph in which no induced subgraph is a claw; i.e., any subset of four vertices has other than only three edges connecting them in this pattern. Equivalently,
    a claw-free graph is a graph in which the neighborhood of any vertex is the complement of a triangle-free graph.""",
    "a connected graph with maximum degree at most 3": r"""A connected graph with maximum degree at most 3 is a graph in which every vertex has degree at most 3.""",
    "a connected graph which is not K_n and has maximum degree at most 3": r"""A connected graph with maximum degree at most 3 is a graph in which every vertex has degree at most 3.""",
    "a connected, claw-free, and cubic graph": r"""A *cubic graph* is a graph where every vertex has degree 3. A *claw* is another name for the complete bipartite graph $K_{1,3}$ (that is, a star graph comprising three edges, three leaves, and a central vertex).
    A *claw-free graph* is a graph in which no induced subgraph is a claw; i.e., any subset of four vertices has other than only three edges connecting them in this pattern. Equivalently,
    a claw-free graph is a graph in which the neighborhood of any vertex is the complement of a triangle-free graph.""",
    "a connected, planar, and cubic graph": r"""A connected, planar, and cubic graph is a graph in which every vertex has degree 3 and can be embedded in the plane without any edges crossing.""",
    "a connected and cubic graph which is not K_4": r"""A connected and cubic graph which is not $K_4$ is a graph in which every vertex has degree 3 and is not a complete graph on 4 vertices.""",
    "a connected and well-covered graph": r"""A connected and well-covered graph is a graph in which every maximal independent set is also maximum.""",
    "a connected graph with diameter at most 3": r"""A connected graph with diameter at most 3 is a graph in which the maximum distance between any two vertices is at most 3.""",
    "a connected and planar graph with diameter at most 3": r"""A connected and planar graph with diameter at most 3 is a graph that can be embedded in the plane without any edges crossing and the maximum distance between any two vertices is at most 3.""",
    "a connected graph with a total domination number equal to the domination number": r"""A connected graph with a total domination number equal to the domination number is a graph in which the minimum cardinality of a total dominating set is equal to the minimum cardinality of a dominating set.""",
    "a connected_graph with min_degree at least 2": r"""A connected graph with minimum degree at least 2 is a graph in which every vertex has degree at least 2.""",
    "a connected_graph with min_degree at least 3": r"""A connected graph with minimum degree at least 3 is a graph in which every vertex has degree at least 3.""",
    "a connected_graph with min_degree at least 4": r"""A connected graph with minimum degree at least 4 is a graph in which every vertex has degree at least 4.""",
    "a connected and bipartite graph with min_degree at least 2": r"""A connected and bipartite graph with minimum degree at least 2 is a graph in which the vertices can be partitioned into two sets such that no two vertices in the same set are adjacent and every vertex has degree at least 2.""",
    "a connected and bipartite graph with min_degree at least 3": r"""A connected and bipartite graph with minimum degree at least 3 is a graph in which the vertices can be partitioned into two sets such that no two vertices in the same set are adjacent and every vertex has degree at least 3.""",
    "a connected and bipartite graph with min_degree at least 4": r"""A connected and bipartite graph with minimum degree at least 4 is a graph in which the vertices can be partitioned into two sets such that no two vertices in the same set are adjacent and every vertex has degree at least 4.""",
    "a connected and planar graph with min_degree at least 2": r"""A connected and planar graph with minimum degree at least 2 is a graph that can be embedded in the plane without any edges crossing and every vertex has degree at least 2.""",
    "a connected and planar graph with min_degree at least 3": r"""A connected and planar graph with minimum degree at least 3 is a graph that can be embedded in the plane without any edges crossing and every vertex has degree at least 3.""",
    "a connected and planar graph with min_degree at least 4": r"""A connected and planar graph with minimum degree at least 4 is a graph that can be embedded in the plane without any edges crossing and every vertex has degree at least 4.""",
    "a connected graph which is not K_n with min_degree at least 2": r"""A connected graph which is not $K_n$ with minimum degree at least 2 is a graph with $n$ vertices that is not a complete graph and every vertex has degree at least 2.""",
    "a connected graph which is not K_n with min_degree at least 3": r"""A connected graph which is not $K_n$ with minimum degree at least 3 is a graph with $n$ vertices that is not a complete graph and every vertex has degree at least 3.""",
    "a connected graph which is not K_n with min_degree at least 4": r"""A connected graph which is not $K_n$ with minimum degree at least 4 is a graph with $n$ vertices that is not a complete graph and every vertex has degree at least 4.""",
    "a connected and triangle-free graph with min_degree at least 2": r"""A connected and triangle-free graph with minimum degree at least 2 is a graph in which no three vertices form a triangle and every vertex has degree at least 2.""",
    "a connected and triangle-free graph with min_degree at least 3": r"""A connected and triangle-free graph with minimum degree at least 3 is a graph in which no three vertices form a triangle and every vertex has degree at least 3.""",
    "a connected and triangle-free graph with min_degree at least 4": r"""A connected and triangle-free graph with minimum degree at least 4 is a graph in which no three vertices form a triangle and every vertex has degree at least 4.""",
    "a connected and at-free graph with min_degree at least 2": r"""A connected and at-free graph with minimum degree at least 2 is a graph in which every vertex has degree at least 2 and does not contain any asteroidal triple.""",
    "a connected and at-free graph with min_degree at least 3": r"""A connected and at-free graph with minimum degree at least 3 is a graph in which every vertex has degree at least 3 and does not contain any asteroidal triple.""",
    "a connected and at-free graph with min_degree at least 4": r"""A connected and at-free graph with minimum degree at least 4 is a graph in which every vertex has degree at least 4 and does not contain any asteroidal triple.""",
    "a connected and chordal graph with min_degree at least 2": r"""A connected and chordal graph with minimum degree at least 2 is a graph in which every vertex has degree at least 2 and every induced cycle has exactly three vertices.""",
    "a connected and chordal graph with min_degree at least 3": r"""A connected and chordal graph with minimum degree at least 3 is a graph in which every vertex has degree at least 3 and every induced cycle has exactly three vertices.""",
    "a connected and chordal graph with min_degree at least 4": r"""A connected and chordal graph with minimum degree at least 4 is a graph in which every vertex has degree at least 4 and every induced cycle has exactly three vertices.""",
    "a connected and claw-free graph with min_degree at least 2": r"""A connected and claw-free graph with minimum degree at least 2 is a graph in which every vertex has degree at least 2 and does not contain any claw.""",
    "a connected and claw-free graph with min_degree at least 3": r"""A connected and claw-free graph with minimum degree at least 3 is a graph in which every vertex has degree at least 3 and does not contain any claw.""",
    "a connected and claw-free graph with min_degree at least 4": r"""A connected and claw-free graph with minimum degree at least 4 is a graph in which every vertex has degree at least 4 and does not contain any claw.""",
    "a connected graph with min_degree at least 2 and maximum degree at most 3": r"""A connected graph with minimum degree at least 2 and maximum degree at most 3 is a graph in which every vertex has degree at least 2 and at most 3.""",
    "a connected and chordal graph with min_degree at least 2": r"""A connected and chordal graph with minimum degree at least 2 is a graph in which every vertex has degree at least 2 and every induced cycle has exactly three vertices.""",
    "a connected and chordal graph with min_degree at least 3": r"""A connected and chordal graph with minimum degree at least 3 is a graph in which every vertex has degree at least 3 and every induced cycle has exactly three vertices.""",
    "a connected and chordal graph with min_degree at least 4": r"""A connected and chordal graph with minimum degree at least 4 is a graph in which every vertex has degree at least 4 and every induced cycle has exactly three vertices.""",
    "a connected and bull-free graph": r"""A *bull* is the complete graph $K_4$ minus one edge. A *bull-free graph* is a graph in which no induced subgraph is a bull.""",
    "a connected and diamond-free graph": r"""A *diamond* is a graph formed by removing one edge from the complete graph $K_4$. A *diamond-free graph* is a graph in which no induced subgraph is a diamond.""",
    "a connected, cubic, and diamond-free graph": r"""A *cubic graph* is a graph where every vertex has degree 3. A *diamond* is a graph formed by removing one edge from the complete graph $K_4$. A *diamond-free graph* is a graph in which no induced subgraph is a diamond.""",

}

TRIVIAL_BOUNDS = [
    "domination_number <= order",
    "order <= size - 1",
    "domination_number <= total_domination_number",
    "domination_number <= independent_domination_number",
    "domination_number <= connected_domination_number",
    "domination_number <= independence_number",
    "domination_number >= power_domination_number",
    "power_domination_number <= zero_forcing_number",
    "power_domination_number <= domination_number",
    "power_domination_number <= total_domination_number",
    "power_domination_number <= connected_domination_number",
    "power_domination_number <= total_zero_forcing_number",
    "independent_domination_number <= independence_number",
    "total_domination_number <= connected_domination_number",
    "zero_forcing_number >= min_degree",
    "zero_forcing_number <= total_zero_forcing_number",
    "total_zero_forcing_number >= zero_forcing_number",
    "power_domination_number >= total_zero_forcing_number",
    "zero_forcing_number >= power_domination_number",
    "zero_forcing_number <= (order - connected_domination_number)",
    "total_zero_forcing_number >= min_degree",
    "matching_number >= min_maximal_matching_number",
    "min_maximal_matching_number <= matching_number",
    "matching_number <= 1/2 order",
    "connected_domination_number >= domination_number",
    "total_domination_number >= domination_number",
    "total_domination_number >= sub_total_domination_number",
    "domination_number >= 1/2 total_domination_number",
    "domination_number <= 1/2 order",
    "domination_number <= (order - max_degree)",
    "domination_number >= slater",
    "total_domination_number <= 2 domination_number",
    "total_domination_number <= 2 independent_domination_number",
    "power_domination_number <= independent_domination_number",
    "total_zero_forcing_number <= order + -1",
    "zero_forcing_number <= order + -1",
    "total_domination_number <= order + -1",
    "domination_number <= order + -1",
    "independent_domination_number <= order + -1",
    "connected_domination_number <= order + -1",
    "power_domination_number <= order + -1",
    "min_degree <= max_degree",
    "min_degree <= zero_forcing_number",
    "annihilation_number >= matching_number",
    "annihilation_number >= independence_number",
    "annihilation_number >= residue",
    "sub_total_domination_number <= total_domination_number",
    "sub_total_domination_number >= slater",
    "slater <= domination_number",
    "chromatic_number >= clique_number",
    "independent_domination_number >= domination_number",
    "independent_domination_number <= (order - max_degree)",
    "independent_domination_number >= slater",
    "independent_domination_number >= power_domination_number",
    "independent_domination_number >= 1/2 total_domination_number",
    "independent_domination_number <= 1/2 order",
    "independent_domination_number >= [order/ (max_degree + 1)]",
    "independent_domination_number <= 1/2 power_domination_number + 11/2",
    "independent_domination_number <= 2/3 zero_forcing_number + 13/3",
    "independent_domination_number <= 1/5 diameter + 27/5",
    "domination_number >= [order/ (max_degree + 1)]",
    "connected_domination_number >= power_domination_number",
    "independence_number <= annihilation_number",
    "independence_number >= residue",
    "independence_number <= order + -1",
    "independence_number <= size",
    "independence_number <= (order - matching_number)",
    "independence_number >= independent_domination_number",
    "independence_number >= domination_number",
    "diameter >= radius",
    "zero_forcing_number >= 1/2 total_zero_forcing_number",
    "annihilation_number <= 1/2 order",
    "connected_zero_forcing_number >= zero_forcing_number",
    "connected_zero_forcing_number <= zero_forcing_number",
    "connected_zero_forcing_number >= min_degree",
    "connected_zero_forcing_number <= order + -1",
    "connected_zero_forcing_number >= chromatic_number + -1",
    "connected_zero_forcing_number >= clique_number + -1",
    "connected_zero_forcing_number >= total_zero_forcing_number"

]

def fraction_to_str(fraction):
    return f"{fraction.numerator}/{fraction.denominator}"

def str_to_fraction(string):
    numerator, denominator = map(int, string.split('/'))
    return Fraction(numerator, denominator)

def conjecture_to_dict(conjecture):
    return {
        "hypothesis": conjecture.hypothesis.statement,
        "conclusion": {
            "lhs": conjecture.conclusion.lhs,
            "inequality": conjecture.conclusion.inequality,
            "slope": fraction_to_str(conjecture.conclusion.slope) if isinstance(conjecture.conclusion.slope, Fraction) else conjecture.conclusion.slope,
            "rhs": conjecture.conclusion.rhs,
            "intercept": fraction_to_str(conjecture.conclusion.intercept) if isinstance(conjecture.conclusion.intercept, Fraction) else conjecture.conclusion.intercept
        },
        "symbol": conjecture.symbol,
        "touch": conjecture.touch
    }

def conjecture_to_latex(conjecture):
    conj_dict = conjecture_to_dict(conjecture)
    slope_numerator = conjecture.conclusion.slope.numerator
    slope_denominator = conjecture.conclusion.slope.denominator
    if slope_numerator == slope_denominator:
        slope = ""
    else:
        slope = r"\frac{" + f"{slope_numerator}" + "}{" + f"{slope_denominator}" + "}" if slope_denominator != 1 else str(slope_numerator)

    intercept_numerator = abs(conjecture.conclusion.intercept.numerator)
    intercept_denominator = abs(conjecture.conclusion.intercept.denominator)
    operation = "+" if conjecture.conclusion.intercept.numerator >= 0 else "-"
    if intercept_numerator == 0:
        tex_string = TEX_MAP[conj_dict["conclusion"]["lhs"]] + " " + TEX_MAP[conj_dict["conclusion"]["inequality"]] + " " + slope + "" + TEX_MAP[conj_dict["conclusion"]["rhs"]] + ","
    elif intercept_numerator == 1 and intercept_denominator == 1:
        tex_string = TEX_MAP[conj_dict["conclusion"]["lhs"]] + " " + TEX_MAP[conj_dict["conclusion"]["inequality"]] + " " + slope + "" + TEX_MAP[conj_dict["conclusion"]["rhs"]] + f" {operation} " + "1"+ ","
    else:
        intercept = r"\frac{" + f"{intercept_numerator}" + "}{" + f"{intercept_denominator}" + "}" if intercept_denominator != 1 else str(intercept_numerator)
        tex_string = TEX_MAP[conj_dict["conclusion"]["lhs"]] + " " + TEX_MAP[conj_dict["conclusion"]["inequality"]] + " " + slope + "" + TEX_MAP[conj_dict["conclusion"]["rhs"]] + f" {operation} " + intercept + ","
    return tex_string

def generate_conjectures():
    # st.title("Generate Conjectures")
    st.set_page_config(page_title="Conjecture Generator") #, page_icon="📈")
    st.markdown("# Conjecturing with TxGraffiti")
    # st.sidebar.header("Plotting Demo")
    st.write(
        """Please select the invariant to conjecture on, whether you would like to conjecture on
        a specific family of graphs, and whether you would like to apply the Dalmatian heuristic
        for filtering the conjectures. After selecting these fields, you can generate the conjectures
        by clicking the button. The conjectures will be computed and then displayed below.
        """
    )

    df = pd.read_csv(DATA_FILE)

    numerical_columns = [col for col in df.columns if col in invariants]
    boolean_columns = [col for col in df.columns if col in booleans]

    # data = st.button("Update Graph Database")
    # if data:
    #     make_graph_dataframe_from_edgelists()

    # with st.sidebar:

    invariant_column = st.selectbox('Select a graph invariant to conjecture on:', numerical_columns)
    single_property = st.selectbox('Would you like to only consider a specific family of graphs? NOTE: Choosing None will take a few minutes for TxGraffiti to generate conjectures.', ['None'] + boolean_columns)
    dalmatian_answer = st.radio('Apply the Dalmatian heuristic for conjecture filtering?', ['y', 'n'])
    generate_conjectures = st.button('Generate Conjectures')

    if generate_conjectures:
        if single_property != 'None':
            boolean_columns = [single_property]

        upper_conjectures = make_all_upper_linear_conjectures(df, invariant_column, numerical_columns, boolean_columns)
        lower_conjectures = make_all_lower_linear_conjectures(df, invariant_column, numerical_columns, boolean_columns)

        conjectures = upper_conjectures + lower_conjectures
        conjectures = [
            conj for conj in conjectures if str(conj.conclusion) not in TRIVIAL_BOUNDS
        ]

        conjectures = [
            conj for conj in conjectures if conj.touch > 2
        ]

        if dalmatian_answer == 'y':
            conjectures = dalmatian(df, conjectures)

        conjectures = filter_conjectures(df, conjectures)

        st.subheader("Generated Conjectures")
        for i, conjecture in enumerate(conjectures):
            with st.expander(f"# Conjecture {i + 1}"):
                print(conjecture.conclusion)
                hypothesis = TEX_MAP[conjecture.hypothesis.statement]
                st.write(f"{hypothesis}")
                st.latex(conjecture_to_latex(conjecture))
                st.write(r" $\text{with equality on }$" +  f"{conjecture.touch}" +  r"$\text{ graphs in the known collection of graphs.}$.")

                lhs = conjecture.conclusion.lhs
                rhs = conjecture.conclusion.rhs
                st.write(f"**Definitions:** {DEF_MAP[conjecture.hypothesis.statement]} {DEF_MAP[lhs]} {DEF_MAP[rhs]}")


        st.session_state.conjectures = [conjecture_to_dict(conj) for conj in conjectures]
        st.session_state.filtered_indices = list(range(len(conjectures)))


generate_conjectures()
