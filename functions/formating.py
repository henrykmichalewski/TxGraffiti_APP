import streamlit as st
from fractions import Fraction
import time

__all__ =[
    'long_computation',
    'fraction_to_str',
    'str_to_fraction',
    'conjecture_to_dict',
    'conjecture_to_latex',
    'conjecture_to_lean',
    'multi_radio',
    'rows_multi_radio',
    'def_map',
    'tex_map',
]

TEX_MAP = {
    "<=": r"\leq",
    ">=": r"\geq",
    "=": r"=",
    "domination_number": r"\gamma(G)",
    "independence_number": r"\alpha(G)",
    "chromatic_number": r"\chi(G)",
    "square_chromatic_number": r"\chi(G^2)",
    "cubed_chromatic_number": r"\chi(G^3)",
    "two_rainbow_domination_number": r"\gamma_{r2}(G)",
    "three_rainbow_domination_number": r"\gamma_{r3}(G)",
    "clique_number": r"\omega(G)",
    "vertex_cover_number": r"\beta(G)",
    "zero_forcing_number": r"Z(G)",
    "total_zero_forcing_number": r"Z_t(G)",
    "residue_residue_power_sum": r"\sum_{i=1}^{R(G)} R(G^i)",
    "connected_zero_forcing_number": r"Z_c(G)",
    "outer_connected_domination_number": r"\tilde{\gamma}_{c}(G)",
    "power_domination_number": r"\gamma_P(G)",
    "total_domination_number": r"\gamma_t(G)",
    "semitotal_domination_number": r"\gamma_{2t}(G)",
    "connected_domination_number": r"\gamma_c(G)",
    "independent_domination_number": r"i(G)",
    "roman_domination_number": r"\gamma_{R}(G)",
    "double_roman_domination_number": r"\gamma_{dR}(G)",
    "restrained_domination_number": r"\gamma_{r}(G)",
    "matching_number": r"\mu(G)",
    "min_maximal_matching_number": r"i(L(G))",
    "edge_domination_number": r"\gamma_e(G)",
    "min_degree": r"\delta(G)",
    "max_degree": r"\Delta(G)",
    "diameter": r"\text{diam}(G)",
    "radius": r"\text{rad}(G)",
    "order": r"n(G)",
    "size": r"m(G)",
    "LG_residue": r"R(L(G))",
    "LG_annihilation": r"a(L(G))",
    "LG_graph_energy": r"[\mathcal{E}(L(G))]",
    "LG_slater": r"sl(L(G))",
    "power_2_residue_sum": r"\sum_{i=1}^{\Delta(G)} R(G^i)",
    "power_max_degree_annihilation_sum": r"\sum_{i=1}^{\Delta(G)} a(G^i)",
    "power_max_degree_residue_sum": r"\sum_{i=1}^{\Delta(G)} R(G^i)",
    "power_min_degree_residue_sum": r"\sum_{i=1}^{\delta(G)} R(G^i)",
    "power_min_degree_annihilation_sum": r"\sum_{i=1}^{\delta(G)} a(G^i)",
    "positive_semidefinite_zero_forcing_number": r"Z_+(G)",
    "graph_energy": r"[\mathcal{E}(G)]",
    "residue": r"R(G)",
    "annihilation_number": r"a(G)",
    "sub_total_domination_number": r"\text{sub}_t(G)",
    "slater": r"sl(G)",
    "power_2_residue_sum": r"(R(G) + R(G^2))",
    "power_3_residue_sum": r"(R(G) + R(G^2) + R(G^3))",
    "power_2_annihilation_sum": r"(a(G) + a(G^2))",
    "power_3_annihilation_sum": r"(a(G) + a(G^2) + a(G^3))",
    "k_slater_index": r"\min\{k \in \mathbb{N} \: : \: sl_k(G) \geq \gamma(G)\}",
    "wiener_index": r"\sum_{\{u,v\} \subseteq V(G)} d(u, v)",
    "k_residual_index": r"R(G, k)",
    "triameter": r"\text{tri}(G)",
    "randic_index": r"\sum_{uv \in E(G)} \frac{1}{\sqrt{d(u) \cdot d(v)}}",
    "second_largest_eigenvalue" : r"[\lambda_2(G)]",
    "square_positive_energy" : r"[s^{+}(G)]",
    "square_negative_energy" : r"[s^{-}(G)]",
    "harmonic_index": r"\sum_{\{u,v\} \in E(G)} \frac{2}{d(u) + d(v)}",
    "strong_harmonic_index": r"\sum_{\{u,v\} \in E(G)} \min \Big\{\frac{1}{d(u)}, \frac{1}{d(v)} \Big \}",
    "sum_connectivity_index": r"\sum_{\{u,v\} \in E(G)} \frac{1}{\sqrt{d(u) + d(v)}}",
    "square_clique_number": r"\omega(G^2)",
    "square_residue": r"R(G^2)",
    "cube_residue": r"R(G^3)",
    "square_annihilation": r"a(G^2)",
    "cube_annihilation": r"a(G^3)",
    "square_zero_forcing_number": r"Z(G^2)",
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
    "(order - min_maximal_matching_number)" : r"(n(G) - i(L(G))",
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
    "a connected graph that is a line graph": r"$\text{If } G \text{ is a connected graph that is also a line graph, then}$",
    "a connected and bull-free graph": r"$\text{If } G \text{ is a connected and bull-free graph, then}$",
    "a connected and diamond-free graph": r"$\text{If } G \text{ is a connected and diamond-free graph, then}$",
    "a connected, cubic, and diamond-free graph": r"$\text{If } G \text{ is a connected, cubic, and diamond-free graph, then}$",
    "a block graph": r"$\text{If } G \text{ is a block graph, then}$",
    "reciprocal_first_zagreb_index": r"\sum_{v \in V(G)} \frac{1}{d(v)^2}",
    "reciprocal_second_zagreb_index": r"\sum_{uv \in E(G)} \frac{1}{d(u) \cdot d(v)}",
    "reciprocal_estrada_index": r"\sum_{i=1}^{n} \frac{1}{e^{\lambda_i}}",
    "reciprocal_harary_index": r"\sum_{u \neq v} \frac{1}{d_G(u,v)^2}",
    "reciprocal_second_zagreb_variation": r"\sum_{uv \in E(G)} \frac{1}{d(u) + d(v)}",
    "reciprocal_randic_index": r"\sum_{uv \in E(G)} \frac{1}{\sqrt{d(u) \cdot d(v)}}",
    "reciprocal_augmented_zagreb_index": r"\sum_{uv \in E(G)} \left( \frac{d(u) + d(v) - 2}{d(u) \cdot d(v)} \right)^3",
    "reciprocal_sum_connectivity_index": r"\sum_{uv \in E(G)} \frac{1}{\sqrt{d(u) + d(v)}}",
    "reciprocal_hyper_zagreb_index": r"\sum_{v \in V(G)} \frac{1}{d(v)(d(v) - 1)}",
    "reciprocal_geometric_arithmetic_index": r"\sum_{uv \in E(G)} \frac{2\sqrt{d(u) \cdot d(v)}}{d(u) + d(v)}",
    # New 2-degree indices
    "first_zagreb_index_2_degree": r"\sum_{v \in V(G)} d_2(v)^2",
    "second_zagreb_index_2_degree": r"\sum_{uv \in E(G)} d_2(u) \cdot d_2(v)",
    "reciprocal_first_zagreb_index_2_degree": r"\sum_{v \in V(G)} \frac{1}{d_2(v)^2}",
    "reciprocal_second_zagreb_index_2_degree": r"\sum_{uv \in E(G)} \frac{1}{d_2(u) \cdot d_2(v)}",
    "average_degree_2_degree": r"\frac{1}{n} \sum_{v \in V(G)} d_2(v)",
    "reciprocal_randic_index_2_degree": r"\sum_{uv \in E(G)} \frac{1}{\sqrt{d_2(u) \cdot d_2(v)}}",
    "reciprocal_sum_connectivity_index_2_degree": r"\sum_{uv \in E(G)} \frac{1}{\sqrt{d_2(u) + d_2(v)}}",
    "hyper_zagreb_index_2_degree": r"\sum_{v \in V(G)} d_2(v)(d_2(v) - 1)",
    "reciprocal_geometric_arithmetic_index_2_degree": r"\sum_{uv \in E(G)} \frac{2 \sqrt{d_2(u) \cdot d_2(v)}}{d_2(u) + d_2(v)}",
    "augmented_average_edge_degree": r"\frac{2|E(G)|}{\bar{d}_e(G) + 2}",
    "inverse_edge_degree_plus_two_sum": r"\sum_{e \in E(G)} \frac{1}{d(e) + 2}",
    "inverse_edge_degree_plus_one_sum": r"\sum_{e \in E(G)} \frac{1}{d(e) + 1}",
    "inverse_degree_plus_one_sum": r"\sum_{v \in V(G)} \frac{1}{d(v) + 1}",
    "inverse_degree_plus_two_sum": r"\sum_{v \in V(G)} \frac{1}{d(v) + 2}",
}


DEF_MAP = {
    "order" : r"""The order of a graph $G$, denoted by $n(G)$, is the number of vertices in $G$.""",

    "size" : r"""The size of a graph $G$, denoted by $m(G)$, is the number of edges in $G$.""",

    "min_degree" : r"""The minimum degree of a graph $G$, denoted by $\delta(G)$, is the minimum
    degree of a vertex in $G$.""",

    "max_degree" : r"""The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum
    degree of a vertex in $G$.""",

    "diameter" : r"""The diameter of a graph $G$, denoted by $\text{diam}(G)$, is the maximum
    distance between any two vertices in $G$.""",

    "triameter": r""" The triameter of a graph $G$ is defined as
    $\text{tri}(G) = \max\{ d(u,v) + d(v,w) + d(u,w) \: : \: u,v,w \in V(G) \}$.""",

    "radius" : r"""The radius of a graph $G$, denoted by $\text{rad}(G)$, is the minimum distance
    between any two vertices in $G$.""",

    "domination_number": r"""A *dominating set* of $G$ is a set $D \subseteq V(G)$ of
    vertices such that every vertex in $G$ is either in $D$ or adjacent to a vertex in
    $D$. The *domination number* of a graph $G$, denoted by $\gamma(G)$, is the minimum
    cardinality of a dominating set of $G$.""",

    "total_domination_number" : r"""A *total dominating set* of $G$ is a set $D \subseteq V(G)$
    of vertices such that every vertex in $G$ is adjacent to a vertex in $D$. The *total domination number*
    of a graph $G$, denoted by $\gamma_t(G)$, is the minimum cardinality of a total dominating set of $G$. """,

    "connected_domination_number" : r"""A *connected dominating set* of $G$ is a dominating
    set $D \subseteq V(G)$ of vertices such that the subgraph induced by $D$ is connected.
    The *connected domination number* of a graph $G$, denoted by $\gamma_c(G)$, is the minimum
    cardinality of a connected dominating set of $G$.""",

    "independence_number": r"""An *independent set* of a graph $G$ is a set $I \subseteq V(G)$
    of vertices such that no two vertices in $I$ are adjacent. The *independence number* of $G$,
    denoted by $\alpha(G)$, is the maximum cardinality of an independent set of $G$.""",

    "chromatic_number": r"""The chromatic number of a graph $G$, denoted by $\chi(G)$, is
    the minimum number of colors needed to color the vertices of $G$ such that no two
    adjacent vertices have the same color.""",

    "square_chromatic_number": r"""The *square* of an undirected graph G is another graph denoted $G^2$
    that has the same set of vertices, but in which two vertices are adjacent when their distance in $G$
    is at most 2. The chromatic number of the square of a graph $G$, denoted
    by $\chi(G^2)$, is the minimum number of colors needed to color the vertices of $G^2$ such
    that no two adjacent vertices have the same color.""",

    "clique_number": r"""A *clique* in $G$ is a set of vertices that induces a complete
    subgraph of $G$. The *clique number* of a graph $G$, denoted by $\omega(G)$, is the maximum cardinality of a clique in $G$.""",

    "vertex_cover_number": r"""A *vertex cover* of $G$ is a set $C \subseteq V(G)$ of vertices such that every edge in $G$ is incident to at least one
    vertex in $C$. The *vertex cover number* of a graph $G$, denoted by $\beta(G)$, is the minimum cardinality of a
    vertex cover of $G$.""",

    "zero_forcing_number": r"""Given a blue and white coloring of the vertices of $G$, the *zero forcing color change rule*
    allows any blue colored vertex with exactly one white colored neighbor to force its one white colored neighbor to become
    colored blue. A set $B \subseteq V(G)$ of initially blue colored vertices is called a *zero forcing set* of $G$ if by iteratively
    applying the zero forcing color change rule all of the vertices in $G$ become colored blue. The *zero forcing number* of
    a graph $G$, denoted by $Z(G)$, is the minimum cardinality of a zero forcing set of $G$.""",

    "total_zero_forcing_number": r"""Given a blue and white coloring of the vertices of $G$, the *zero forcing color change rule*
    allows any blue colored vertex with exactly one white colored neighbor to force its one white colored neighbor to become
    colored blue. A set $B \subseteq V(G)$ of initially blue colored vertices is called a *zero forcing set* of $G$ if by iteratively
    applying the zero forcing color change rule all of the vertices in $G$ become colored blue. The *total zero forcing number* of
    a graph $G$, denoted by $Z_t(G)$, is the minimum cardinality of a zero forcing set of $G$ which induces a isolate-free subgraph.""",

    "connected_zero_forcing_number": r"""Given a blue and white coloring of the vertices of $G$, the *zero forcing color change rule*
    allows any blue colored vertex with exactly one white colored neighbor to force its one white colored neighbor to become
    colored blue. A set $B \subseteq V(G)$ of initially blue colored vertices is called a *zero forcing set* of $G$ if by iteratively
    applying the zero forcing color change rule all of the vertices in $G$ become colored blue. The *connected zero forcing number* of
    a graph $G$, denoted by $Z_t(G)$, is the minimum cardinality of a zero forcing set of $G$ which induces a connected subgraph.""",

    "power_domination_number" : r"""Given a blue and white coloring of the vertices of $G$, the *zero forcing color change rule*
    allows any blue colored vertex with exactly one white colored neighbor to force its one white colored neighbor to become
    colored blue. A set $B \subseteq V(G)$ of initially blue colored vertices is called a *zero forcing set* of $G$ if by iteratively
    applying the zero forcing color change rule all of the vertices in $G$ become colored blue. A *power dominating set* of $G$ is
    a dominating set of a zero forcing set of $G$. The power domination number of a graph $G$, denoted by $\gamma_P(G)$, is the
    minimum cardinality of a power dominating set of $G$.""",

    "independent_domination_number" : r"""An independent dominating set of $G$ is a set $D \subseteq V(G)$ of vertices such that $D$
    is independent and every vertex in $G$ is adjacent to a vertex in $D$. The *independent domination number* of a graph $G$,
    denoted by $i(G)$, is the minimum cardinality of an independent dominating set of $G$. """,

    "matching_number" : r"""A *matching* in $G$ is a set of edges that do not share any common vertices. The *matching number*
    of a graph $G$, denoted by $\mu(G)$, is the maximum cardinality of a matching in $G$.""",

    "edge_domination_number": r"""An *edge dominating set* of $G$ is a set $D \subseteq E(G)$ of edges such that every
    edge in $G$ is incident to an edge in $D$. The *edge domination number* of a graph $G$, denoted by $\gamma_e(G)$,
    is the minimum cardinality of an edge dominating set of $G$.""",

    "annihilation_number" : r"""If $d_1, \dots, d_n$ is the degree sequence of a graph $G$ with $m$ edges, where $d_1 \leq \cdots \leq d_n$,
    then the *annihilation number* of $G$ is the largest integer $k$ such that $\sum_{i=1}^{k} d_i \leq m$, or equivalently, the largest integer
    $k$ such that $\sum_{i=1}^{k} d_i \leq \sum_{i=k+1}^{n} d_i$.""",

    "slater" : r"""The *Slater number* of a graph $G$, written $sl(G)$, is defined as the smallest integer $j$ such that
    $d_1 + \dots + d_j \geq n(G)$, where $d_1, \dots, d_n$ is the degree sequence of $G$ with $d_i \geq d_{i+1}$ for all $i \in [n(G) - 1]$.""",

    "sub_total_domination_number" : r"""The sub-total domination number of a graph $G$ is denoted by $\text{sub}_t(G)$,
    smallest integer $j$ such that
    $j + (d_1 + \dots + d_j) \geq n(G)$, where $d_1, \dots, d_n$ is the degree sequence of $G$ with $d_i \geq d_{i+1}$ for all $i \in [n(G) - 1]$.""",

    "wiener_index" : r"""The *Wiener index* of a graph $G$, denoted by $W(G)$, is the sum of the shortest path distances between all pairs of vertices in $G$.
    Formally, if $d(u, v)$ denotes the distance between vertices $u$ and $v$ in $G$, then $W(G) = \sum_{\{u,v\} \subseteq V(G)} d(u, v).$""",


    "two_rainbow_domination_number": r"""Given a graph $G$ and a set of $[k] = \{1, \dots, k\}$ colors, assume that we assign
    an arbitrary subset of these colors to each vertex of $G$. If we require that each vertex to which an empty set is assigned
    has in its (open) neighborhood all $k$ colors, then this assignment is called a *$k$-rainbow dominating function* of the graph $G$.
    The corresponding invariant $\gamma_{rk}(G)$, which is the minimum sum of numbers of assigned colors over all vertices of $G$,
    is called the *$k$-rainbow domination number* of G. The *2-rainbow domination number* of $G$, denoted
    $\gamma_{r2}(G)$, is the minimum cardinality of a 2-rainbow dominating set of $G$.""",

    "roman_domination_number": r"""A *Roman dominating function* of $G$ is a function $f \: : \: V(G) \rightarrow \{0, 1, 2\}$
    such that every vertex $v$ for which $f(v) = 0$ has a neighbor $u$ with $f(u) = 2$. The weight of a Roman dominating function
    $f$ is $w(f) = \sum_{v \in V(G)} f(v)$. The *Roman domination number* of a graph $G$, denoted by $\gamma_R(G)$, is the minimum
    weight of all possible Roman dominating functions in $G$.""",

    "three_rainbow_domination_number": r"""Given a graph $G$ and a set of $[k] = \{1, \dots, k\}$ colors, assume that we assign
    an arbitrary subset of these colors to each vertex of $G$. If we require that each vertex to which an empty set is assigned
    has in its (open) neighborhood all $k$ colors, then this assignment is called a *$k$-rainbow dominating function* of the graph $G$.
    The corresponding invariant $\gamma_{rk}(G)$, which is the minimum sum of numbers of assigned colors over all vertices of $G$,
    is called the *$k$-rainbow domination number* of G. The *3-rainbow domination number* of $G$, denoted
    $\gamma_{r3}(G)$, is the minimum cardinality of a 3-rainbow dominating set in $G$.""",

    "double_roman_domination_number": r"""A function $f \: : \: V(G) \rightarrow \{0, 1, 2, 3\}$ is a double Roman dominating
    function on a graph $G$ if the following conditions are met. Let $V_i$ denote the set of vertices assigned $i$ by function
    $f$. (i) If $f(v) = 0 $, then vertex $v$ must have at least two neighbors in $V_2$ or one neighbor in $V_3$. (ii) If $f(v) = 1$,
    then vertex $v$ must have at least one neighbor in $V_2 \cup V_3$. The *double Roman domination number* of $G$, written
    $\gamma_{dR}(G)$, equals the minimum weight of a double Roman dominating function on $G$. """,

    "restrained_domination_number": r"""A *restrained dominating set* of $G$, is a dominating set $D \subseteq V(G)$,
    such that each vertex in $V(G) \setminus D$ is adjacent to another vertex in $V(G) \setminus D$.
    The *restrained domination number* of a graph $G$, denoted by $\gamma_{r}(G)$, is the minimum
    cardinality of a restrained dominating set of $G$.""",

    "residue_residue_power_sum": r"""The *$k$-power* of an undirected graph $G$ is another graph denoted $G^k$
    that has the same set of vertices, but in which two vertices are adjacent when their distance in $G$
    is at most $k$. The *residue* of a graph is the number of zero obtained after termination
    of the Havel-Hakimi process on $G$, and is denoted $R(G)$.""",

    "power_max_degree_residue_sum": r"""The *$k$-power* of an undirected graph $G$ is another graph denoted $G^k$
    that has the same set of vertices, but in which two vertices are adjacent when their distance in $G$
    is at most $k$. The *maximum degree* of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.
    The *residue* of a graph is the number of zero obtained after termination of the Havel-Hakimi process on $G$, and is denoted $R(G)$.""",

    "power_max_degree_annihilation_sum": r"""The *$k$-power* of an undirected graph $G$ is another graph denoted $G^k$
    that has the same set of vertices, but in which two vertices are adjacent when their distance in $G$
    is at most $k$. The *maximum degree* of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.
    If $d_1, \dots, d_n$ is the degree sequence of a graph $G$ with $m$ edges, where $d_1 \leq \cdots \leq d_n$,
    then the *annihilation number* of $G$ is the largest integer $k$ such that $\sum_{i=1}^{k} d_i \leq m$, or equivalently, the largest integer
    $k$ such that $\sum_{i=1}^{k} d_i \leq \sum_{i=k+1}^{n} d_i$.""",

    "power_min_degree_residue_sum": r"""The sum of the residues of $G$ through $G^{\delta}$.""",

    "power_min_degree_annihilation_sum": r"""The *$k$-power* of an undirected graph $G$ is another graph denoted $G^k$
    that has the same set of vertices, but in which two vertices are adjacent when their distance in $G$
    is at most $k$. The *minimum degree* of a graph $G$, denoted by $\delta(G)$, is the maximum degree of a vertex in $G$.
    If $d_1, \dots, d_n$ is the degree sequence of a graph $G$ with $m$ edges, where $d_1 \leq \cdots \leq d_n$,
    then the *annihilation number* of $G$ is the largest integer $k$ such that $\sum_{i=1}^{k} d_i \leq m$, or equivalently, the largest integer
    $k$ such that $\sum_{i=1}^{k} d_i \leq \sum_{i=k+1}^{n} d_i$.""",

    "cubed_chromatic_number": r"""The *cube* of an undirected graph G is another graph denoted $G^3$
    that has the same set of vertices, but in which two vertices are adjacent when their distance in $G$
    is at most 3. The chromatic number of the cube of a graph $G$, denoted by
    $\chi(G^3)$, is the minimum number of colors needed to color the vertices of the cube $G^3$ of $G$ such
    that no two adjacent vertices have the same color.""",

    "cube_residue": r"""The *cube* of an undirected graph G is another graph denoted $G^3$
    that has the same set of vertices, but in which two vertices are adjacent when their distance in $G$
    is at most 3. The residue of a graph $G$, denoted by $R(G)$, is the
    number of zeros at the termination of the Havel-Hakimi proccess on the degree sequence of $G$.""",

    "cube_annihilation": r"""The *cube* of an undirected graph G is another graph denoted $G^3$
    that has the same set of vertices, but in which two vertices are adjacent when their distance in $G$
    is at most 3. If $d_1, \dots, d_n$ is the degree sequence of a graph $G$ with $m$ edges, where $d_1 \leq \cdots \leq d_n$,
    then the *annihilation number* of $G$ is the largest integer $k$ such that $\sum_{i=1}^{k} d_i \leq m$, or equivalently, the largest integer
    $k$ such that $\sum_{i=1}^{k} d_i \leq \sum_{i=k+1}^{n} d_i$.""",

    "square_clique_number": r""" The square of an undirected graph G is another graph denoted $G^2$
    that has the same set of vertices, but in which two vertices are adjacent when their distance in $G$
    is at most 2. The clique number of the square of a graph $G$, denoted by $\omega(G^2)$,
    is the maximum cardinality of a clique in $G^2$.""",

    "LG_residue": r"""The residue of a graph $G$, denoted by $R(G)$, is the number of zeros at the
    termination of the Havel-Hakimi proccess on the degree sequence of $G$. The line graph of a graph $G$,
    denoted by $L(G)$, is the graph whose vertices correspond to the edges of $G$ and two vertices in $L(G)$
    are adjacent if their corresponding edges in $G$ share a common vertex.""",

    "LG_annihilation": r"""The annihilation number of a graph $G$, denoted by $a(G)$, is a degree sequence invariant introduced by R. Pepper. The line graph of a graph $G$, denoted by $L(G)$, is the graph whose vertices correspond to the edges of $G$ and two vertices in $L(G)$ are adjacent if their corresponding edges in $G$ share a common vertex.""",
    "semitotal_domination_number": r"""A *semitotal dominating set* is a set of vertices $S \subseteq V(G)$ in $G$ such that $S$ is a dominating set and each vertex of $S$ within distance 2 to another vertex in $S$.
    The *semitotal domination number* of $G$ is the minimum cardinality of a semitotal dominating set of $G$, and is denoted by $\gamma_{2t}(G)$.""",

    "power_2_residue_sum": r"""The square of an undirected graph G is another graph denoted $G^2$
    that has the same set of vertices, but in which two vertices are adjacent when their distance in $G$
    is at most 2. The sum of the residue of a graph $G$ and the residue of the square of $G$.""",
    "power_3_residue_sum": r"""The sum of the residue of a graph $G$, the residue of the square of $G$, and the residue of the cube of $G$.""",
    "sum_connectivity_index": r"""The sum connectivity index of a graph $G$ is a degree sequence graph invariant denoted by $\text{sum}_c(G)$.""",
    "power_2_annihilation_sum": r"""The square of an undirected graph G is another graph denoted $G^2$
    that has the same set of vertices, but in which two vertices are adjacent when their distance in $G$
    is at most 2. The sum of the annihilation number of a graph $G$ and the annihilation number of the square of $G$.""",
    "power_3_annihilation_sum": r"""The sum of the annihilation number of a graph $G$, the annihilation number of the square of $G$, and the annihilation number of the cube of $G$.""",
    "min_edge_cover": r"""A *minimum edge cover* of $G$ is a set $E \subseteq E(G)$ of edges such that every vertex in $G$ is incident to an edge in $E$. The *minimum edge cover number* of a graph $G$, denoted by $\beta'(G)$, is the minimum cardinality of a minimum edge cover of $G$.""",
    "randic_index": r"""The Randić index $R(G)$ is defined as the sum of the reciprocals of the square roots of the product of the degrees of adjacent vertices in a graph.
    For each edge $uv \in E(G)$, where $d(u)$ and $d(v)$ are the degrees of the vertices $u$ and $v$, the Randić index is given by $R(G) = \sum_{uv \in E(G)} \frac{1}{\sqrt{d(u) \cdot d(v)}}$.""",

    "square_positive_energy" : r"""The square positive energy of a graph $G$, denoted $[s^{+}(G)]$, is
    the sum of the squares of the eigenvalues of the adjacency matrix of $G$ *rounded to the nearest integer*.""",

    "square_negative_energy" : r"""The square negative energy of a graph $G$, denoted $[s^{-}(G)]$, is the
    sum of the squares of the negative eigenvalues of the adjacency matrix of $G$ *rounded to the nearest integer*.""",

    "graph_energy" : r"""The energy of a graph $G$, denoted $[\mathcal{E}(G)]$, is the sum of the absolute values
    of the eigenvalues of the adjacency matrix of $G$ *rounded to the nearest integer*.""",

    "second_largest_eigenvalue" : r"""The second largest eigenvalue of a graph $G$, denoted by $[\lambda_2(G)]$, is
    the second largest eigenvalue of the adjacency matrix of $G$ *rounded to the nearest integer*.""",

    "min_maximal_matching_number" : r"""The minimum maximal matching number of a graph $G$, denoted by $i(L(G))$,
    is the minimum cardinality of a maximal matching in $G$; equivalently, the independent domination number of
    the line graph L(G).""",

    "positive_semidefinite_zero_forcing_number" : r"""In a graph $G$ where some vertices $S$ are colored blue and
    the remaining vertices are colored white, the positive semidefinite color change rule is: If $W_1, \dots, W_k$
    are the sets of vertices of the $k$ components of $G - S$ (note that it is possible that $k=1$), $w \in W_i$,
    $u \in S$, and $w$ is the only white neighbor of $u$ in the subgraph of $G$ induced by $W_i \cup S$, then change
    the color of $w$ to blue; in this case, we say $u$ forces $w$ and write $u \to w$. Given an initial set $B$ of
    blue vertices, the derived set of $B$ is the set of blue vertices that results from applying the positive
    semidefinite color change rule until no more changes are possible. A positive semidefinite zero forcing set
    is an initial set $B$ of vertices such that the derived set of $B$ is all the vertices of $G$. The
    *positive semidefinite zero forcing number* of a graph $G$, denoted $Z_+(G)$, is the minimum of $|B|$ over all
    positive semidefinite zero forcing sets $B \subseteq V(G)$.""",

    "residue" : r"""The residue of a graph $G$, denoted by $R(G)$, is the number of zeros at the termination of the Havel-Hakimi proccess on
    the degree sequence of $G$.""",

    "harmonic_index" : r"""The *harmonic index* of a graph $G$, denoted by $H(G)$, is a degree-based graph invariant defined as the sum of the reciprocals of the degrees of the adjacent vertices. Formally, if $d(u)$ and $d(v)$ are the degrees of adjacent vertices $u$ and $v$, then
    $$H(G) = \sum_{\{u,v\} \in E(G)} \frac{2}{d(u) + d(v)}.$$""",

    "strong_harmonic_index" : r"""The *strong harmonic index* of a graph $G$, denoted by $H_s(G)$, is a degree-based graph invariant defined as the sum of the minimum of reciprocals of the degrees of the adjacent vertices.
    Formally, if $d(u)$ and $d(v)$ are the degrees of adjacent vertices $u$ and $v$, then
    $$H_s(G) = \sum_{\{u,v\} \in E(G)} \min\{\frac{1}{d(u)}, \frac{1}{d(v)}\}.$$""",


    "square_zero_forcing_number" : r"""Given a blue and white coloring of the vertices of $G$, the *zero forcing color change rule*
    allows any blue colored vertex with exactly one white colored neighbor to force its one white colored neighbor to become
    colored blue. A set $B \subseteq V(G)$ of initially blue colored vertices is called a *zero forcing set* of $G$ if by iteratively
    applying the zero forcing color change rule all of the vertices in $G$ become colored blue. The *zero forcing number* of
    a graph $G$, denoted by $Z(G)$, is the minimum cardinality of a zero forcing set of $G$. The square of an undirected graph G is another graph denoted $G^2$
    that has the same set of vertices, but in which two vertices are adjacent when their distance in $G$ is at most 2.""",

    "LG_graph_energy" : r"""The energy of the line graph of a graph $G$, denoted by $[\mathcal{E}(L(G))]$, is
    the sum of the absolute values of the eigenvalues of the adjacency matrix of $L(G)$ *rounded to the nearest integer*.""",

    "LG_slater" : r"""The Slater number of the line graph of a graph $G$ is a degree sequence graph invariant denoted by $sl(L(G))$.""",

    "k_slater_index": r"""The $k$-Slater index of a graph $G$, is the smallest integer $k \geq 1$ so that $sl_k(G) \geq \gamma(G)$,
     where $sl_k(G)$ is the $k$-slater number of $G$, the smallest integer $j$ such that $j + \frac{1}{k}(d_1 + \dots + d_j) \geq n(G)$, where $d_1, \dots, d_n$ is the degree sequence of $G$ with $d_i \geq d_{i+1}$ for all $i \in [n(G) - 1]$.""",

    "k_residual_index" : r"""The $k$-residual index of a graph $G$, denoted by $R(G, k)$, is the smallest integer $k \geq 1$ so that $\text{R}_k(G) \geq \alpha(G)$,
    where $\text{R}_k(G)$ is the $k$-residue of $G$ and $\alpha(G)$ is the independence number of $G$.""",

    "(order - domination_number)":  r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The domination number of a graph $G$, denoted by $\gamma(G)$, is the minimum cardinality of a dominating set of $G$.
    A dominating set of $G$ is a set $D \subseteq V(G)$ of vertices such that every vertex in $G$ is either in $D$ or adjacent to a vertex in $D$.""",
    "(order - total_domination_number)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The total domination number of a graph $G$,
    denoted by $\gamma_t(G)$, is the minimum cardinality of a total dominating set of $G$. A total dominating set of $G$ is a set $D \subseteq V(G)$ of vertices such that every vertex in $G$ is adjacent to a vertex in $D$.""",
    "(order - connected_domination_number)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The connected domination number of a graph $G$,
    denoted by $\gamma_c(G)$, is the minimum cardinality of a connected dominating set of $G$. A connected dominating set of $G$ is a dominating set $D \subseteq V(G)$ of vertices such that the subgraph induced by $D$ is connected.""",
    "(order - power_domination_number)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The power domination number of a graph $G$, denoted by $\gamma_P(G)$,
    is the minimum cardinality of a power dominating set of $G$.""",
    "(order - zero_forcing_number)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The zero forcing number of a graph $G$, denoted by $Z(G)$, is the minimum size of a zero forcing set of $G$.
    A zero forcing set of $G$ is a set $S \subseteq V(G)$ of vertices such that if the vertices in $S$ are initially colored blue and all other vertices are initially colored white, then the coloring process will eventually turn all vertices blue.""",
    "(order - diameter)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The diameter of a graph $G$, denoted by $\text{diam}(G)$, is the maximum distance between any two vertices in $G$.""",
    "(order - radius)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The radius of a graph $G$, denoted by $\text{rad}(G)$, is the minimum distance between any two vertices in $G$.""",
    "(order - triameter)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The triameter of a graph $G$is denoted by $\text{tri}(G)$.""",
    "(order - independent_domination_number)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The independent domination number of a graph $G$, denoted by $i(G)$, is the minimum cardinality of an independent dominating set of $G$.
    An independent dominating set of $G$ is a set $D \subseteq V(G)$ of vertices such that $D$ is independent and every vertex in $G$ is adjacent to a vertex in $D$.""",
    "(order - chromatic_number)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The chromatic number of a graph $G$, denoted by $\chi(G)$, is the minimum number of colors needed to color the
    vertices of $G$ such that no two adjacent vertices have the same color.""",
    "square_residue": r"""The square residue of a graph $G$, denoted by $R(G^2)$, is the number of zeros at the termination of the Havel-Hakimi proccess on the degree sequence of $G^2$.""",
    "square_annihilation": r"""The square annihilation number of a graph $G$, denoted by $a(G^2)$, is a degree sequence invariant introduced by R. Pepper.""",
    "(order - matching_number)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The matching number of a graph $G$, denoted by $\mu(G)$, is the maximum cardinality of a matching in $G$.
    A matching in $G$ is a set of edges that do not share any common vertices.""",
    "(order - min_maximal_matching_number)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The minimum maximal matching number of a graph $G$, denoted by $\gamma_e(G)$, is the minimum cardinality of a maximal matching in $G$.""",
    "(order - min_degree)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The minimum degree of a graph $G$, denoted by $\delta(G)$, is the minimum degree of a vertex in $G$.""",
    "(order - max_degree)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.""",
    "(order - clique_number)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The clique number of a graph $G$, denoted by $\omega(G)$, is the maximum cardinality of a clique in $G$.
    A clique in $G$ is a set of vertices that induces a complete subgraph of $G$.""",
    "(order - residue)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The residue of a graph $G$, denoted by $R(G)$, is the number of zeros at the termination of the Havel-Hakimi proccess on the degree sequence of $G$.""",
    "(order - annihilation_number)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The annihilation number of a graph $G$, denoted by $a(G)$, is a degree sequence invariant introduced by R. Pepper.""",
    "(order - sub_total_domination_number)" : r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The sub-total domination number of a graph $G$ is denoted by $\text{sub}_t(G)$.""",
    "(order - slater)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The Slater number of a graph $G$ is a degree sequence graph invariant denoted by $sl(G)$.""",
    "(order - k_slater_index)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The $k$-Slater index of a graph $G$, denoted by $sl(G, k)$, is the smallest integer $k \geq 1$ so that $\text{sub}_k(G) \geq \gamma(G)$.""",
    "(order - k_residual_index)": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The $k$-residual index of a graph $G$, denoted by $R(G, k)$, is the smallest integer $k \geq 1$ so that $\text{R}_k(G) \geq \alpha(G)$.""",
    "[(annihilation_number + residue)/ max_degree]": r"""The annihilation number of a graph $G$, denoted by $a(G)$, is a degree sequence invariant introduced by R. Pepper. The residue of a graph $G$, denoted by $R(G)$, is the number of zeros at the termination of the Havel-Hakimi proccess on the degree sequence of $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.""",
    "[order/ max_degree]": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.""",
    "[order/ (max_degree + 1)]": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.""",
    "[order/ (max_degree - 1)]": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.""",
    "[order/ (max_degree + 2)]": r"""The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.""",
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
    "outer_connected_domination_number": r"""The outer connected domination number of a graph $G$, denoted by $\tilde{\gamma}_{c}(G)$, is the minimum cardinality of a dominating set $S$ of $G$ such that $V(G)\setminus S$ induces a connected subgraph.""",
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
    "a connected graph that is a line graph": r"""A *line graph* is a graph whose vertices correspond to the edges of a given graph $G$ and two vertices in the line graph are adjacent if their corresponding edges in $G$ share a common vertex.""",
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
    "a block graph": """A block graph is a connected graph in which every biconnected component is a clique.""",
    # Existing indices
    "reciprocal_first_zagreb_index": r"""The reciprocal first Zagreb index $RZ_1(G)$ is defined as the sum of the reciprocals of the square of the degrees of the vertices of $G$: $RZ_1(G) = \sum_{v \in V(G)} \frac{1}{d(v)^2}$.""",

    "reciprocal_second_zagreb_index": r"""The reciprocal second Zagreb index $RZ_2(G)$ is defined as the sum of the reciprocals of the product of degrees of adjacent vertices in $G$: $RZ_2(G) = \sum_{uv \in E(G)} \frac{1}{d(u) \cdot d(v)}$.""",

    "reciprocal_estrada_index": r"""The reciprocal Estrada index $REE(G)$ is defined as the sum of the reciprocals of the exponential of the eigenvalues of the adjacency matrix of $G$: $REE(G) = \sum_{i=1}^{n} \frac{1}{e^{\lambda_i}}$.""",

    "reciprocal_harary_index": r"""The reciprocal Harary index $RH(G)$ is the sum of the reciprocals of the square of the shortest path distances between distinct vertices in $G$: $RH(G) = \sum_{u \neq v} \frac{1}{d_G(u,v)^2}$.""",

    "reciprocal_second_zagreb_variation": r"""The reciprocal second Zagreb variation $RZ_2^*(G)$ is the sum of the reciprocals of the sum of the degrees of adjacent vertices: $RZ_2^*(G) = \sum_{uv \in E(G)} \frac{1}{d(u) + d(v)}$.""",

    "reciprocal_randic_index": r"""The reciprocal Randić index $RR(G)$ is the sum of the reciprocals of the square roots of the product of degrees of adjacent vertices: $RR(G) = \sum_{uv \in E(G)} \frac{1}{\sqrt{d(u) \cdot d(v)}}$.""",

    "reciprocal_augmented_zagreb_index": r"""The reciprocal augmented Zagreb index $RAZI(G)$ is the sum of the cubes of the reciprocals of the product of the degrees of adjacent vertices, adjusted by the sum of their degrees: $RAZI(G) = \sum_{uv \in E(G)} \left( \frac{d(u) + d(v) - 2}{d(u) \cdot d(v)} \right)^3$.""",

    "reciprocal_sum_connectivity_index": r"""The reciprocal sum-connectivity index $R\chi(G)$ is the sum of the reciprocals of the square roots of the sum of the degrees of adjacent vertices: $R\chi(G) = \sum_{uv \in E(G)} \frac{1}{\sqrt{d(u) + d(v)}}$.""",

    "reciprocal_hyper_zagreb_index": r"""The reciprocal hyper-Zagreb index $RHM_1(G)$ is the sum of the reciprocals of the product of the degrees of vertices and one less than their degrees: $RHM_1(G) = \sum_{v \in V(G)} \frac{1}{d(v)(d(v) - 1)}$.""",

    "reciprocal_geometric_arithmetic_index": r"""The reciprocal geometric-arithmetic index $RGA(G)$ is the sum of the ratios of twice the square root of the product of the degrees of adjacent vertices to the sum of their degrees: $RGA(G) = \sum_{uv \in E(G)} \frac{2\sqrt{d(u) \cdot d(v)}}{d(u) + d(v)}$.""",

    # 2-degree-based indices
    "first_zagreb_index_2_degree": r"""The first Zagreb index for the 2-degree $Z_1^{(2)}(G)$ is defined as the sum of the squares of the 2-degrees of the vertices: $Z_1^{(2)}(G) = \sum_{v \in V(G)} d_2(v)^2$.""",

    "second_zagreb_index_2_degree": r"""The second Zagreb index for the 2-degree $Z_2^{(2)}(G)$ is defined as the sum of the products of the 2-degrees of adjacent vertices: $Z_2^{(2)}(G) = \sum_{uv \in E(G)} d_2(u) \cdot d_2(v)$.""",

    "reciprocal_first_zagreb_index_2_degree": r"""The reciprocal first Zagreb index for the 2-degree $RZ_1^{(2)}(G)$ is the sum of the reciprocals of the squares of the 2-degrees of the vertices: $RZ_1^{(2)}(G) = \sum_{v \in V(G)} \frac{1}{d_2(v)^2}$.""",

    "reciprocal_second_zagreb_index_2_degree": r"""The reciprocal second Zagreb index for the 2-degree $RZ_2^{(2)}(G)$ is the sum of the reciprocals of the products of the 2-degrees of adjacent vertices: $RZ_2^{(2)}(G) = \sum_{uv \in E(G)} \frac{1}{d_2(u) \cdot d_2(v)}$.""",

    "average_degree_2_degree": r"""The average 2-degree $\bar{d_2}(G)$ is the average number of vertices within distance 2 from each vertex in the graph: $\bar{d_2}(G) = \frac{1}{n} \sum_{v \in V(G)} d_2(v)$.""",

    "reciprocal_randic_index_2_degree": r"""The reciprocal Randić index for the 2-degree $RR^{(2)}(G)$ is the sum of the reciprocals of the square roots of the products of the 2-degrees of adjacent vertices: $RR^{(2)}(G) = \sum_{uv \in E(G)} \frac{1}{\sqrt{d_2(u) \cdot d_2(v)}}$.""",

    "reciprocal_sum_connectivity_index_2_degree": r"""The reciprocal sum-connectivity index for the 2-degree $R\chi^{(2)}(G)$ is the sum of the reciprocals of the square roots of the sum of the 2-degrees of adjacent vertices: $R\chi^{(2)}(G) = \sum_{uv \in E(G)} \frac{1}{\sqrt{d_2(u) + d_2(v)}}$.""",

    "hyper_zagreb_index_2_degree": r"""The hyper-Zagreb index for the 2-degree $HM_1^{(2)}(G)$ is the sum of the products of the 2-degrees of the vertices and one less than their 2-degrees: $HM_1^{(2)}(G) = \sum_{v \in V(G)} d_2(v)(d_2(v) - 1)$.""",

    "reciprocal_geometric_arithmetic_index_2_degree": r"""The reciprocal geometric-arithmetic index for the 2-degree $RGA^{(2)}(G)$ is the sum of the ratios of twice the square root of the product of the 2-degrees of adjacent vertices to the sum of their 2-degrees: $RGA^{(2)}(G) = \sum_{uv \in E(G)} \frac{2 \sqrt{d_2(u) \cdot d_2(v)}}{d_2(u) + d_2(v)}$.""",

    "augmented_average_edge_degree": r"""The augmented average edge degree is defined as $\frac{2|E(G)|}{\bar{d}_e(G) + 2}$, where $|E(G)|$ is the number of edges in the graph and $\bar{d}_e(G)$ is the average edge degree of $G$. The average edge degree $\bar{d}_e(G)$ is the average number of edges that share an endpoint with a given edge.""",

    "inverse_edge_degree_plus_two_sum": r"""The inverse edge degree plus two sum is defined as $\sum_{e \in E(G)} \frac{1}{d(e) + 2}$, where $E(G)$ is the set of edges in the graph and $d(e)$ is the degree of edge $e$.""",

    "inverse_edge_degree_plus_one_sum": r"""The inverse edge degree plus one sum is defined as $\sum_{e \in E(G)} \frac{1}{d(e) + 1}$, where $E(G)$ is the set of edges in the graph and $d(e)$ is the degree of edge $e$.""",

    "inverse_degree_plus_two_sum": r"""$V(G)$ is the set of vertices in the graph and $d(v)$ is the degree of vertex $v$.""",

    "inverse_degree_plus_one_sum": r"""$V(G)$ is the set of vertices in the graph and $d(v)$ is the degree of vertex $v$.""",
}




def long_computation():
    progress_bar = st.progress(0)
    status_text = st.empty()

    for i in range(100):
        progress_bar.progress(i + 1)
        status_text.text(f'Filtering and sorting the proposed inequalities... {i + 1}%')
        time.sleep(0.1)  # Simulate a long computation

    status_text.text('Done!')
    st.success('Process complete!')


def fraction_to_str(fraction):
    return f"{fraction.numerator}/{fraction.denominator}"

def str_to_fraction(string):
    numerator, denominator = map(int, string.split('/'))
    return Fraction(numerator, denominator)

# def conjecture_to_dict(conjecture):
#     return {
#         "hypothesis": conjecture.hypothesis.statement,
#         "conclusion": {
#             "lhs": conjecture.conclusion.lhs,
#             "inequality": conjecture.conclusion.inequality,
#             "slope": fraction_to_str(conjecture.conclusion.slope) if isinstance(conjecture.conclusion.slope, Fraction) else conjecture.conclusion.slope,
#             "rhs": conjecture.conclusion.rhs,
#             "intercept": fraction_to_str(conjecture.conclusion.intercept) if isinstance(conjecture.conclusion.intercept, Fraction) else conjecture.conclusion.intercept
#         },
#         "symbol": conjecture.symbol,
#         "touch": conjecture.touch
#     }

def conjecture_to_dict(conjecture):
    # Convert the list of slopes into strings (using fraction_to_str if they are Fractions)
    slopes = [
        fraction_to_str(slope) if isinstance(slope, Fraction) else slope
        for slope in conjecture.conclusion.slopes
    ]

    # Handle the right-hand side variables as a list
    rhs_vars = conjecture.conclusion.rhs

    return {
        "hypothesis": conjecture.hypothesis.statement,
        "conclusion": {
            "lhs": conjecture.conclusion.lhs,
            "inequality": conjecture.conclusion.inequality,
            "slopes": slopes,  # Store all slopes
            "rhs": rhs_vars,   # Store all right-hand side variables
            "intercept": fraction_to_str(conjecture.conclusion.intercept) if isinstance(conjecture.conclusion.intercept, Fraction) else conjecture.conclusion.intercept
        },
        "symbol": conjecture.symbol,
        "touch": conjecture.touch
    }


def def_map(x):
    if type(x) == str:
        return DEF_MAP[x]
    else:
        return DEF_MAP[x[0]]

def tex_map(x):
    return TEX_MAP[x]

# def conjecture_to_latex(conjecture):
#     conj_dict = conjecture_to_dict(conjecture)
#     slope_numerator = conjecture.conclusion.slope.numerator
#     slope_denominator = conjecture.conclusion.slope.denominator
#     if slope_numerator == slope_denominator:
#         slope = ""
#     else:
#         slope = r"\frac{" + f"{slope_numerator}" + "}{" + f"{slope_denominator}" + "}" if slope_denominator != 1 else str(slope_numerator)

#     intercept_numerator = abs(conjecture.conclusion.intercept.numerator)
#     intercept_denominator = abs(conjecture.conclusion.intercept.denominator)
#     operation = "+" if conjecture.conclusion.intercept.numerator >= 0 else "-"
#     if intercept_numerator == 0:
#         tex_string = TEX_MAP[conj_dict["conclusion"]["lhs"]] + " " + TEX_MAP[conj_dict["conclusion"]["inequality"]] + " " + slope + "" + TEX_MAP[conj_dict["conclusion"]["rhs"]] + ","
#     elif intercept_numerator == 1 and intercept_denominator == 1:
#         tex_string = TEX_MAP[conj_dict["conclusion"]["lhs"]] + " " + TEX_MAP[conj_dict["conclusion"]["inequality"]] + " " + slope + "" + TEX_MAP[conj_dict["conclusion"]["rhs"]] + f" {operation} " + "1"+ ","
#     else:
#         intercept = r"\frac{" + f"{intercept_numerator}" + "}{" + f"{intercept_denominator}" + "}" if intercept_denominator != 1 else str(intercept_numerator)
#         tex_string = TEX_MAP[conj_dict["conclusion"]["lhs"]] + " " + TEX_MAP[conj_dict["conclusion"]["inequality"]] + " " + slope + "" + TEX_MAP[conj_dict["conclusion"]["rhs"]] + f" {operation} " + intercept + ","
#     return tex_string

def conjecture_to_latex(conjecture):
    conj_dict = conjecture_to_dict(conjecture)
    slopes = conjecture.conclusion.slopes
    rhs_vars = conjecture.conclusion.rhs
    intercept_numerator = abs(conjecture.conclusion.intercept.numerator)
    intercept_denominator = abs(conjecture.conclusion.intercept.denominator)
    operation = "+" if conjecture.conclusion.intercept >= 0 else "-"

    # Construct the slope * variable terms
    slope_terms = []
    for slope, var in zip(slopes, rhs_vars):
        slope_numerator = slope.numerator
        slope_denominator = slope.denominator

        # Handle slope formatting
        if slope_numerator == slope_denominator:  # If slope is 1
            slope_str = ""
        else:
            slope_str = r"\frac{" + f"{slope_numerator}" + "}{" + f"{slope_denominator}" + "}" if slope_denominator != 1 else str(slope_numerator)

        # Append the corresponding term with its variable
        slope_terms.append(slope_str + TEX_MAP[var])

    # Join slope terms with " + "
    slope_str = " + ".join(slope_terms)

    # Handle intercept formatting
    if intercept_numerator == 0:  # No intercept term
        intercept_str = ""
    elif intercept_numerator == 1 and intercept_denominator == 1:  # Intercept is 1
        intercept_str = f" {operation} 1"
    else:  # General intercept case
        intercept_str = r"\frac{" + f"{intercept_numerator}" + "}{" + f"{intercept_denominator}" + "}" if intercept_denominator != 1 else str(intercept_numerator)
        intercept_str = f" {operation} {intercept_str}"

    # Combine everything into a LaTeX formatted string
    tex_string = (
        TEX_MAP[conj_dict["conclusion"]["lhs"]] + " " +
        TEX_MAP[conj_dict["conclusion"]["inequality"]] + " " +
        slope_str + intercept_str + ","
    )

    return tex_string


def conjecture_to_lean(conjecture):
    ineq_map = {"<=": "≤", ">=": "≥", "=": "="}
    lean_var = {
        "order": "Fintype.card V",
        "size": "Finset.card G.edgeFinset",
        "chromatic_number": "G.chromaticNumber",
    }

    lhs = lean_var.get(conjecture.conclusion.lhs, f"{conjecture.conclusion.lhs} G")

    rhs_terms = []
    for slope, var in zip(conjecture.conclusion.slopes, conjecture.conclusion.rhs):
        term = lean_var.get(var, f"{var} G")
        if slope == 1:
            rhs_terms.append(term)
        else:
            rhs_terms.append(f"({slope}) * {term}")
    rhs = " + ".join(rhs_terms)
    if conjecture.conclusion.intercept != 0:
        rhs += f" + {conjecture.conclusion.intercept}"

    inequality = ineq_map.get(conjecture.conclusion.inequality, conjecture.conclusion.inequality)
    hypothesis = "(hG : G.Connected)" if conjecture.hypothesis.statement == "a connected graph" else ""

    return (
        "theorem generated {V} [Fintype V] (G : SimpleGraph V) "
        f"{hypothesis} : {lhs} {inequality} {rhs} := by\n  sorry"
    )


def multi_radio(label, options):
    selections = {option: False for option in options}

    st.write(label)
    for option in options:
        selections[option] = st.checkbox(option, key=option)

    selected_options = [option for option, selected in selections.items() if selected]
    return selected_options

def rows_multi_radio(label, options):
    st.write(label)
    selections = {option: False for option in options}
    rows = (len(options) + 3) // 2  # Calculate number of rows needed

    for i in range(rows):
        cols = st.columns(2)
        for j in range(2):
            if 2 * i + j < len(options):
                option = options[2 * i + j]
                selections[option] = cols[j].checkbox(option, key=option)

    selected_options = [option for option, selected in selections.items() if selected]
    return selected_options