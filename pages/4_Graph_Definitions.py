import streamlit as st

st.title("Definitions")


# Display the relevant section
st.markdown(r"""

## Domination Number
A *dominating set* of $G$ is a set $D \subseteq V(G)$ of vertices such that every vertex in $G$ is either in $D$
or adjacent to a vertex in $D$. The *domination number* of a graph $G$, denoted by $\gamma(G)$, is the minimum cardinality of a
dominating set of $G$.

## Independence Number
An *independent set* of a graph $G$ is a set $I \subseteq V(G)$ of vertices such that no two vertices in $I$ are adjacent.
The *independence number* of a graph $G$, denoted by $\alpha(G)$, is the maximum cardinality of an independent set of $G$.

## Chromatic Number
The *chromatic number* of a graph $G$, denoted by $\chi(G)$, is the minimum number of colors needed
to color the vertices of $G$ such that no two adjacent vertices have the same color.

## Clique Number
A *clique* in $G$ is a set of vertices that induces a complete subgraph of $G$. The *clique number* of a graph $G$, denoted by $\omega(G)$, is the maximum cardinality of a clique in $G$.

## Vertex Cover Number
A *vertex cover* of $G$ is a set $C \subseteq V(G)$ of vertices such that every edge in $G$ is incident to at least one
vertex in $C$. The *vertex cover number* of a graph $G$, denoted by $\beta(G)$, is the minimum cardinality of a
vertex cover of $G$.

## Zero Forcing Number
A *zero forcing set* of $G$ is a set $S \subseteq V(G)$ of vertices such that if the vertices in $S$ are initially colored blue and
all other vertices are initially colored white, then the coloring process will eventually turn all vertices blue. The *zero forcing number* of a graph $G$, denoted by $Z(G)$, is the minimum size of a zero forcing
set of $G$.

## Total Zero Forcing Number
A *total zero forcing set* of $G$ is a set $S \subseteq V(G)$ of vertices with no isolates, such that if the vertices in $S$ are initially
colored blue and all other vertices are initially colored white, then the coloring process will eventually turn all vertices blue
and white. The *total (zero) forcing number* of a graph $G$, denoted by $Z_t(G)$, is the minimum size of a total
zero forcing set of $G$.

## Total Domination Number
A *total dominating set* of $G$ is a set $D \subseteq V(G)$ of vertices such that every vertex in $G$ is adjacent
to a vertex in $D$. The *total domination number* of a graph $G$, denoted by $\gamma_t(G)$, is the minimum cardinality of a total
dominating set of $G$.

## Minimum Edge Cover
An *edge cover* of $G$ is a set $M \subseteq E(G)$ of edges such that every vertex in $G$ is incident to an edge in $M$. The *minimum edge cover number* of a graph $G$, denoted by $\beta'(G)$, is the minimum cardinality of a minimum edge cover of $G$.

## Randić Index
The Randić index of a graph $G$ is defined as the sum of weights $1/\sqrt{d_ud_v}$ over all edges $uv$, where $d_u$ and $d_v$ are the degrees of the vertices $u$ and $v$ in $G$, respectively.

## Connected Domination Number
A *connected dominating set* of $G$ is a dominating set $D \subseteq V(G)$ of vertices such that the subgraph induced by $D$ is connected.
The *connected domination number* of a graph $G$, denoted by $\gamma_c(G)$, is the minimum cardinality of a connected dominating set of $G$.

## Independent Domination Number
An *independent dominating set* of $G$ is a set $D \subseteq V(G)$ of vertices such that $D$ is an independent set, and every vertex in $G$ is either adjacent to a vertex in $D$, or is in $D$.
The *independent domination number* of a graph $G$, denoted by $i(G)$, is the minimum cardinality of an independent dominating set of $G$.

## Power Domination Number
A set $S\subseteq V(G)$ of vertices in $G$ is defined to be a *power dominating set* of a graph if every vertex and every edge in the system is monitored by the set $S$ (following a set of rules for power system monitoring).The *power domination number* of a graph $G$, denoted by $\gamma_P(G)$, is the minimum cardinality of a power dominating set of $G$.

## Matching Number
A *matching* in $G$ is a set of edges that do not share any common vertices. The *matching number* of a graph $G$, denoted by $\mu(G)$, is the maximum cardinality of a matching in $G$.

## Minimum Maximal Matching Number
The *minimum maximal matching number* of a graph $G$, denoted by $\gamma_e(G)$, is the minimum cardinality of a maximal matching in $G$. This invariant is also known as the *edge domination number* of $G$.

## Minimum Degree
The *minimum degree* of a graph $G$, denoted by $\delta(G)$, is the minimum degree of a vertex in $G$.

## Maximum Degree
The *maximum degree* of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.

## Diameter
The *diameter* of a graph $G$, denoted by $\text{diam}(G)$, is the maximum distance between any two vertices in $G$.

## Radius
The *radius* of a graph $G$, denoted by $\text{rad}(G)$, is the minimum distance between any two vertices in $G$.

## Triameter
The *triameter* of a connected graph $G$, denoted by $tr(G)$, is defined as $\max \{d(u,v)+d(v,w)+d(u,w) : \: u,v,w \in V(G) \}$, where $d(u, v)$, $d(v, w)$, and $d(u, w)$, denote the distances from $u$ to $v$, from $v$ to $w$, and from $u$ to $w$, respectively.

## Order
The *order* of a graph $G$, denoted by $n(G)$, is the number of vertices in $G$. That is, $n(G) = |V(G)|$.

## Size
The *size* of a graph $G$, denoted by $m(G)$, is the number of edges in $G$. That is, $m(G) = |E(G)|$.

## Residue
The *residue* of a graph $G$, denoted by $R(G)$, is the number of zeros obtained at the termination of the Havel-Hakimi process on
the degree sequence of $G$.

## Harmonic Index
The harmonic index of a graph $G$ is a degree sequence graph invariant denoted by $\text{harmonic}(G)$.

## Annihilation Number
The annihilation number of a graph $G$, denoted by $a(G)$, is a degree sequence invariant introduced by R. Pepper.

## Sub-Total Domination Number
The sub-total domination number of a graph $G$ is denoted by $\text{sub}_t(G)$.

## Slater Number
The Slater number of a graph $G$ is a degree sequence graph invariant denoted by $sl(G)$.

## k-Slater Index
The $k$-Slater index of a graph $G$, denoted by $sl(G, k)$, is the smallest integer $k \geq 1$ so that $\text{sub}_k(G) \geq \gamma(G)$,
where $\text{sub}_k(G)$ is the sub-$k$-domination number of $G$.

## k-Residual Index
The $k$-residual index of a graph $G$, denoted by $R(G, k)$, is the smallest integer $k \geq 1$ so that $\text{R}_k(G) \geq \alpha(G)$,
where $\text{R}_k(G)$ is the $k$-residue of $G$ and $\alpha(G)$ is the independence number of $G$.

## (Order - Domination Number)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The domination number of a graph $G$, denoted by $\gamma(G)$, is the minimum cardinality of a dominating set of $G$.
A dominating set of $G$ is a set $D \subseteq V(G)$ of vertices such that every vertex in $G$ is either in $D$ or adjacent to a vertex in $D$.

## (Order - Total Domination Number)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The total domination number of a graph $G$,
denoted by $\gamma_t(G)$, is the minimum cardinality of a total dominating set of $G$. A total dominating set of $G$ is a set $D \subseteq V(G)$ of vertices such that every vertex in $G$ is adjacent to a vertex in $D$.

## (Order - Connected Domination Number)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The connected domination number of a graph $G$,
denoted by $\gamma_c(G)$, is the minimum cardinality of a connected dominating set of $G$. A connected dominating set of $G$ is a dominating set $D \subseteq V(G)$ of vertices such that the subgraph induced by $D$ is connected.

## (Order - Power Domination Number)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The power domination number of a graph $G$, denoted by $\gamma_P(G)$,
is the minimum cardinality of a power dominating set of $G$.

## (Order - Zero Forcing Number)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The zero forcing number of a graph $G$, denoted by $Z(G)$, is the minimum size of a zero forcing set of $G$.
A zero forcing set of $G$ is a set $S \subseteq V(G)$ of vertices such that if the vertices in $S$ are initially colored blue and all other vertices are initially colored white, then the coloring process will eventually turn all vertices blue.

## (Order - Diameter)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The diameter of a graph $G$, denoted by $\text{diam}(G)$, is the maximum distance between any two vertices in $G$.

## (Order - Radius)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The radius of a graph $G$, denoted by $\text{rad}(G)$, is the minimum distance between any two vertices in $G$.

## (Order - Triameter)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The triameter of a graph $G$ is denoted by $\text{triam}(G)$.

## (Order - Independent Domination Number)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The independent domination number of a graph $G$, denoted by $i(G)$, is the minimum cardinality of an independent dominating set of $G$.
An independent dominating set of $G$ is a set $D \subseteq V(G)$ of vertices such that $D$ is independent and every vertex in $G$ is adjacent to a vertex in $D$.

## (Order - Chromatic Number)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The chromatic number of a graph $G$, denoted by $\chi(G)$, is the minimum number of colors needed to color the
vertices of $G$ such that no two adjacent vertices have the same color.

## (Order - Matching Number)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The matching number of a graph $G$, denoted by $\mu(G)$, is the maximum cardinality of a matching in $G$.
A matching in $G$ is a set of edges that do not share any common vertices.

## (Order - Minimum Maximal Matching Number)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The minimum maximal matching number of a graph $G$, denoted by $\gamma_e(G)$, is the minimum cardinality of a maximal matching in $G$.

## (Order - Minimum Degree)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The minimum degree of a graph $G$, denoted by $\delta(G)$, is the minimum degree of a vertex in $G$.

## (Order - Maximum Degree)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.

## (Order - Clique Number)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The clique number of a graph $G$, denoted by $\omega(G)$, is the maximum cardinality of a clique in $G$.
A clique in $G$ is a set of vertices that induces a complete subgraph of $G$.

## (Order - Residue)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The residue of a graph $G$, denoted by $R(G)$, is the number of zeros at the termination of the Havel-Hakimi process on the degree sequence of $G$.

## (Order - Annihilation Number)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The annihilation number of a graph $G$, denoted by $a(G)$, is a degree sequence invariant introduced by R. Pepper.

## (Order - Sub-Total Domination Number)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The sub-total domination number of a graph $G$ is denoted by $\text{sub}_t(G)$.

## (Order - Slater Number)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The Slater number of a graph $G$ is a degree sequence graph invariant denoted by $sl(G)$.

## (Order - k-Slater Index)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The $k$-Slater index of a graph $G$, denoted by $sl(G, k)$, is the smallest integer $k \geq 1$ so that $\text{sub}_k(G) \geq \gamma(G)$.

## (Order - k-Residual Index)
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The $k$-residual index of a graph $G$, denoted by $R(G, k)$, is the smallest integer $k \geq 1$ so that $\text{R}_k(G) \geq \alpha(G)$.

## [(Annihilation Number + Residue)/ Max Degree]
The annihilation number of a graph $G$, denoted by $a(G)$, is a degree sequence invariant introduced by R. Pepper. The residue of a graph $G$, denoted by $R(G)$, is the number of zeros at the termination of the Havel-Hakimi process on the degree sequence of $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.

## [Order/ Max Degree]
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.

## [Order/ (Max Degree + 1)]
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.

## [Order/ (Max Degree - 1)]
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.

## [Order/ (Max Degree + 2)]
The order of $G$, denoted $n(G)$, is the number of vertices in $G$. The maximum degree of a graph $G$, denoted by $\Delta(G)$, is the maximum degree of a vertex in $G$.

## (Residue + Annihilation Number)
The residue of a graph $G$, denoted by $R(G)$, is the number of zeros at the termination of the Havel-Hakimi process on the degree sequence of $G$. The annihilation number of a graph $G$, denoted by $a(G)$, is a degree sequence invariant introduced by R. Pepper.

## Connected Graph
A connected graph is a graph in which there is a path between every pair of vertices.

## Connected and Bipartite Graph
A connected and bipartite graph is a graph in which the vertices can be partitioned into two sets such that
no two vertices in the same set are adjacent.

## Eulerian Graph
An *Eulerian trail* (or *Eulerian path*) is a trail in a finite graph that visits every edge exactly once (allowing for revisiting vertices).
Similarly, an *Eulerian circuit* or *Eulerian cycle* is an Eulerian trail that starts and ends on the same vertex. The term *Eulerian graph* has two common meanings in graph theory.
One meaning is a graph with an Eulerian circuit, and the other is a graph with every vertex of even degree. These definitions coincide for connected graphs.

## Connected and Planar Graph
A *planar graph* is a graph that can be embedded in the plane without any edges crossing.

## Connected and Regular Graph
A connected and $r$-regular graph with $r>0$ is a non-trivial graph in which every vertex has degree $r$.

## Connected and Cubic Graph
A connected and cubic graph is a graph in which every vertex has degree 3.

## Connected Graph which is not $K_n$
A connected graph which is not $K_n$ is a graph with $n$ vertices that is not a complete graph.

## Connected and Triangle-Free Graph
A connected and triangle-free graph is a graph in which no three vertices form a triangle.

## Connected and AT-Free Graph
A connected graph is a graph in which there is a path between every pair of vertices. Three vertices of a graph form an *asteroidal triple*
if every two of them are connected by a path avoiding the neighborhood of the third. A graph is *AT-free* if it does not contain any asteroidal triple.

## Tree Graph
A tree is a connected graph with no cycles.

## Connected and Chordal Graph
A *chordal graph* is one in which all cycles of four or more vertices have a *chord*, which is an edge that is not part of the cycle but connects two
vertices of the cycle. Equivalently, every induced cycle in the graph should have exactly three vertices.

## Connected and Claw-Free Graph
A *claw* is another name for the complete bipartite graph $K_{1,3}$ (that is, a star graph comprising three edges, three leaves, and a central vertex).
A *claw-free graph* is a graph in which no induced subgraph is a claw; i.e., any subset of four vertices has other than only three edges connecting them in this pattern. Equivalently,
a claw-free graph is a graph in which the neighborhood of any vertex is the complement of a triangle-free graph.

## Connected Graph with Maximum Degree at Most 3
A connected graph with maximum degree at most 3 is a graph in which every vertex has degree at most 3.

## Connected Graph which is not $K_n$ and has Maximum Degree at Most 3
A connected graph which is not $K_n$ and has maximum degree at most 3 is a graph in which every vertex has degree at most 3 and is not a complete graph with $n$ vertices.

## Connected, Claw-Free, and Cubic Graph
A *cubic graph* is a graph where every vertex has degree 3. A *claw* is another name for the complete bipartite graph $K_{1,3}$ (that is, a star graph comprising three edges, three leaves, and a central vertex).
A *claw-free graph* is a graph in which no induced subgraph is a claw; i.e., any subset of four vertices has other than only three edges connecting them in this pattern. Equivalently,
a claw-free graph is a graph in which the neighborhood of any vertex is the complement of a triangle-free graph.

## Connected, Planar, and Cubic Graph
A connected, planar, and cubic graph is a graph in which every vertex has degree 3 and can be embedded in the plane without any edges crossing.

## Connected and Cubic Graph which is not $K_4$
A connected and cubic graph which is not $K_4$ is a graph in which every vertex has degree 3 and is not a complete graph on 4 vertices.

## Connected and Well-Covered Graph
A connected and well-covered graph is a graph in which every maximal independent set is also maximum.

## Connected Graph with Diameter at Most 3
A connected graph with diameter at most 3 is a graph in which the maximum distance between any two vertices is at most 3.

## Connected and Planar Graph with Diameter at Most 3
A connected and planar graph with diameter at most 3 is a graph that can be embedded in the plane without any edges crossing and the maximum distance between any two vertices is at most 3.

## Connected Graph with a Total Domination Number Equal to the Domination Number
A connected graph with a total domination number equal to the domination number is a graph in which the minimum cardinality of a total dominating set is equal to the minimum cardinality of a dominating set.

## Connected Graph with Minimum Degree at Least 2
A connected graph with minimum degree at least 2 is a graph in which every vertex has degree at least 2.

## Connected Graph with Minimum Degree at Least 3
A connected graph with minimum degree at least 3 is a graph in which every vertex has degree at least 3.

## Connected Graph with Minimum Degree at Least 4
A connected graph with minimum degree at least 4 is a graph in which every vertex has degree at least 4.

## Connected and Bipartite Graph with Minimum Degree at Least 2
A connected and bipartite graph with minimum degree at least 2 is a graph in which the vertices can be partitioned into two sets such that no two vertices in the same set are adjacent and every vertex has degree at least 2.

## Connected and Bipartite Graph with Minimum Degree at Least 3
A connected and bipartite graph with minimum degree at least 3 is a graph in which the vertices can be partitioned into two sets such that no two vertices in the same set are adjacent and every vertex has degree at least 3.

## Connected and Bipartite Graph with Minimum Degree at Least 4
A connected and bipartite graph with minimum degree at least 4 is a graph in which the vertices can be partitioned into two sets such that no two vertices in the same set are adjacent and every vertex has degree at least 4.

## Connected and Planar Graph with Minimum Degree at Least 2
A connected and planar graph with minimum degree at least 2 is a graph that can be embedded in the plane without any edges crossing and every vertex has degree at least 2.

## Connected and Planar Graph with Minimum Degree at Least 3
A connected and planar graph with minimum degree at least 3 is a graph that can be embedded in the plane without any edges crossing and every vertex has degree at least 3.

## Connected and Planar Graph with Minimum Degree at Least 4
A connected and planar graph with minimum degree at least 4 is a graph that can be embedded in the plane without any edges crossing and every vertex has degree at least 4.

## Connected Graph which is not $K_n$ with Minimum Degree at Least 2
A connected graph which is not $K_n$ with minimum degree at least 2 is a graph with $n$ vertices that is not a complete graph and every vertex has degree at least 2.

## Connected Graph which is not $K_n$ with Minimum Degree at Least 3
A connected graph which is not $K_n$ with minimum degree at least 3 is a graph with $n$ vertices that is not a complete graph and every vertex has degree at least 3.

## Connected Graph which is not $K_n$ with Minimum Degree at Least 4
A connected graph which is not $K_n$ with minimum degree at least 4 is a graph with $n$ vertices that is not a complete graph and every vertex has degree at least 4.

## Connected and Triangle-Free Graph with Minimum Degree at Least 2
A connected and triangle-free graph with minimum degree at least 2 is a graph in which no three vertices form a triangle and every vertex has degree at least 2.

## Connected and Triangle-Free Graph with Minimum Degree at Least 3
A connected and triangle-free graph with minimum degree at least 3 is a graph in which no three vertices form a triangle and every vertex has degree at least 3.

## Connected and Triangle-Free Graph with Minimum Degree at Least 4
A connected and triangle-free graph with minimum degree at least 4 is a graph in which no three vertices form a triangle and every vertex has degree at least 4.

## Connected and AT-Free Graph with Minimum Degree at Least 2
A connected and AT-free graph with minimum degree at least 2 is a graph in which every vertex has degree at least 2 and does not contain any asteroidal triple.

## Connected and AT-Free Graph with Minimum Degree at Least 3
A connected and AT-free graph with minimum degree at least 3 is a graph in which every vertex has degree at least 3 and does not contain any asteroidal triple.

## Connected and AT-Free Graph with Minimum Degree at Least 4
A connected and AT-free graph with minimum degree at least 4 is a graph in which every vertex has degree at least 4 and does not contain any asteroidal triple.

## Connected and Claw-Free Graph with Minimum Degree at Least 2
A connected and claw-free graph with minimum degree at least 2 is a graph in which every vertex has degree at least 2 and does not contain any claw.

## Connected and Claw-Free Graph with Minimum Degree at Least 3
A connected and claw-free graph with minimum degree at least 3 is a graph in which every vertex has degree at least 3 and does not contain any claw.

## Connected and Claw-Free Graph with Minimum Degree at Least 4
A connected and claw-free graph with minimum degree at least 4 is a graph in which every vertex has degree at least 4 and does not contain any claw.

## Connected Graph with Minimum Degree at Least 2 and Maximum Degree at Most 3
A connected graph with minimum degree at least 2 and maximum degree at most 3 is a graph in which every vertex has degree at least 2 and at most 3.

## Connected and Chordal Graph with Minimum Degree at Least 2
A connected and chordal graph with minimum degree at least 2 is a graph in which every vertex has degree at least 2 and every induced cycle has exactly three vertices.

## Connected and Chordal Graph with Minimum Degree at Least 3
A connected and chordal graph with minimum degree at least 3 is a graph in which every vertex has degree at least 3 and every induced cycle has exactly three vertices.

## Connected and Chordal Graph with Minimum Degree at Least 4
A connected and chordal graph with minimum degree at least 4 is a graph in which every vertex has degree at least 4 and every induced cycle has exactly three vertices.

""")
