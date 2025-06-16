# TxGraffiti: Automated Conjecturing on Graphs

*TxGraffiti* is an artificial intelligence program I developed to produce mathematical research conjectures.
Its earliest version, written around 2017 using C++ and later rewritten in Python, was tailored to graph theory,
the area of research of my advisor, Michael A. Henning at the University of Johannesburg. Writing such a program
during my dissertation years was a valuable tool, as the program's ability to generate meaningful conjectures
significantly contributed to many published and strong results in my dissertation [Davila 2019](https://ujcontent.uj.ac.za/esploro/outputs/9912111507691).

During the early days of writing TxGraffiti, I often read Siemion Fajtlowicz's [Examples are Forever (Preprint)](http://users.encs.concordia.ca/~chvatal/6621/fajtlowicz.pdf))"
which discussed Paul Erdös's interactions with the original GRAFFITI conjectures. Erdös is one of my favorite mathematicians,
so I found it fascinating that a computer program could intrigue such a mathematician. My primary inspiration for writing
TxGraffiti was Erdös, the original GRAFFITI program by Fajtlowicz, and its successor program, Graffiti.pc, written by Ermelinda DeLaVina.

However, it's crucial to note that TxGraffiti was conceived independently of these programs. This autonomy has allowed
TxGraffiti to evolve in its own unique way, setting it apart from GRAFFITI and Graffiti.pc in numerous aspects.
But one might ask, "How could a computer program ever produce meaningful mathematical conjectures?"
The answer that I eventually formulated was to use a data-driven approach to conjecturing.

Using a data-driven approach to conjecturing first consists of collecting, by hand, a small dataset of connected and simple
graphs - my earliest database of graphs consisted of about 100 or so handwritten edge lists made from examining images of
graphs available on the Wolfram Mathworld website. I was lucky that I found the cubic graphs on the Wolfram Mathworld website
easier to look at and more accessible for making edge lists. My tendency to prefer collecting cubic graph data, in turn,
led to the original database of TxGraffiti having many interesting such graphs. With these graphs, TxGraffiti seems
especially good at making conjectures on cubic graphs, some of which remain open even with considerable attention
from mathematicians. The actual database used by TxGraffiti does not consist of the edge lists of these graphs.
Instead, the database of TxGraffiti is a table of precomputed values on each edge list - the need for Python code to
compute things like the clique number, the independence number, and others led to the development of GrinPy with David Amos.

After collecting a database of interesting graphs, the next stage of TxGraffiti involves formulating factual statements
based on this database of graphs. The form of these statements will be an upper (or lower) bound inequality on a given
graph invariant in terms of some function of other graph invariants. The original GRAFFITI (and Graffiti.pc) used expression
trees to search for possible arithmetic combinations of graph invariants to serve as the upper (or lower) bound on a given
invariant. The results of the expression trees often led to complicated upper (and lower) bounds, often in terms of sums of
logs, square roots, and squares of graph invariants. Complicated upper (and lower) bounds were not always produced with the
expression trees, as some of GRAFFITI's most famous conjectures were simple and easy to state, such as the residue lower
bound on the independence number.

Because my attention span can be short sometimes, I was always drawn towards the most simple conjectures about GRAFFITI and
Graffiti.pc. Thus, when designing TxGraffiti, I wanted to keep the possible inequalities as simple as possible. How TxGraffiti
achieves this is by solving a linear program to find some slope ($m$) and intercept ($b$) so that $i(G) \leq m*x(G) + b$ is
satisfied for all graphs in the database. Proposing inequalities as the result of a solved linear program ensures that any
conjectures of TxGraffiti are simple linear functions and, thus, easy to think about. When selecting an invariant of a graph to
conjecture on, TxGraffiti recomputes each possible linear inequality, bounding it from above and below. The reason for this
recomputation is that one may enter a counter-example graph into the database, which, in turn, would alter the solutions found for
each of the linear programs used to generate possible conjectures.

Looking at combinations of graph invariants and solving linear programs based on these combinations generates thousands of possible
linear inequalities as conjectures for TxGraffiti to consider. There are far too many possible inequalities to present as conjectures.
A user would have to sift through hundreds or thousands of garbage conjectures to find hidden diamonds or remarkable conjectures.
The simplest way to reduce the number of conjectures is to limit the number of inequalities presented to the user based on "strength ."

To measure the strength of a conjecture, I borrow terminology from Fajtlowicz and say that a conjecture's *touch number* is the number
of times the conjecture's inequality holds with equality. In terms of graphs and the proposed upper bound $i(G) \leq m*x(G) + b$,
the touch number would be the number of graphs in the database for which $i(G) = m*x(G) + b$. This notion immediately gives rise
to a strong conjecture versus a weak conjecture, for if one conjecture has touch number 20, and another has touch number 1.
The conjecture holding with equality 20 times is a sharper conjecture on the database stored.

Until 2023, TxGraffiti only used the touch number to filter possible linear conjectures. That is, TxGraffiti would compute the touch number
of each conjectured inequality found by solving the linear programs and then present to the user only the top 50 (or so) conjectures relative
to their touch number. This technique was surprisingly valuable and led to several astonishing results, including that the independence number
is, at most, the matching number for $r$-regular graphs with $r>0$. The latest version of TxGraffiti (and Conjecturing.jl - the Julia counterpart to TxGraffiti)
now also gives the user the ability to implement Fajtlowicz's Dalmation heuristic for further filtering of the conjectures; see Larson's [excellent paper](https://www.sciencedirect.com/science/article/pii/S0004370215001575)
on the heuristic for more details.


For a detailed mathematical description of **TxGraffiti**'s algorithms and the history of automated conjecturing in mathematics, see our preprint on arXiv: [arXiv preprint 2409.19379](https://arxiv.org/abs/2409.19379)
## Conjecture Generator Utility

A small standalone script lives in `utils/conjecture_generator.py`. It outputs a sequence
of Lean `conjecture` statements similar to those in Graffiti Conjectures 100.
Run it directly from the command line:

```bash
python utils/conjecture_generator.py        # prints 100 conjectures (by default)

python utils/conjecture_generator.py --limit 50 > demo.lean

python3 utils/conjecture_generator.py \
  --lhs independence_number \
  --rhs '*' \
  --k 1:3 --c 0:2 --limit 50 > indep_vs_all.lean
```

The `--limit` (or `-n`) argument controls how many conjectures are emitted. You can
redirect the output into a `.lean` file and paste it into Lean for exploration.

Example output:

```
import Mathlib.Data.Nat.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace AutoGraffiti
variable {V : Type*}
/- Conjecture 1: For every finite simple graph G, independence number(G) ≤ 1 * chromatic number(G) + 0. -/
conjecture independence_number_le_1_chromatic_number (G : SimpleGraph V) [Fintype V] :
  independence number G ≤ chromatic number G := by
  sorry

/- Conjecture 2: For every finite simple graph G, independence number(G) ≤ 1 * matching number(G) + 0. -/
conjecture independence_number_le_1_matching_number (G : SimpleGraph V) [Fintype V] :
  independence number G ≤ matching number G := by
  sorry

/- Conjecture 3: For every finite simple graph G, independence number(G) ≤ 1 * clique number(G) + 0. -/
conjecture independence_number_le_1_clique_number (G : SimpleGraph V) [Fintype V] :
  independence number G ≤ clique number G := by
  sorry

/- Conjecture 4: For every finite simple graph G, independence number(G) ≤ 1 * vertex cover number(G) + 0. -/
conjecture independence_number_le_1_vertex_cover_number (G : SimpleGraph V) [Fintype V] :
  independence number G ≤ vertex cover number G := by
  sorry
```

## WOWII‑style Conjecture Examples

Below is a ready‑made cheat‑sheet that shows how some classical WOWII inequalities can be recreated with **`utils/conjecture_generator.py`**.  Each row links the original wording to a Lean stub and the exact command to produce it.

> **Tip —** if an invariant name such as `gamma_t` (total domination number) is not yet in `INVARIANTS`, simply add it to the list or pass it via `--lhs/--rhs`.

| WOWII statement                                   | Lean statement                                                              | Parameters `(lhs, k, rhs, c)`                      | Generator example                                                                                                                                                |
| ------------------------------------------------- | --------------------------------------------------------------------------- | -------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| For any graph *G*, **γₜ(G) ≤ a(G) + 1**           | `∀ G, gamma t G ≤ annihilation number G + 1`                                  | `(gamma_t, 1, annihilation_number, 1)`             | `python3 utils/conjecture_generator.py --lhs gamma_t --rhs annihilation_number --k 1:1 --c 1:1 --limit 1 > wowii_gt_a1.lean`                                     |
| For any graph *G*, **γ₂(G) ≤ a(G) + 1**           | `∀ G, gamma 2 G ≤ annihilation number G + 1`                                  | `(gamma_2, 1, annihilation_number, 1)`             | `python3 utils/conjecture_generator.py --lhs gamma_2 --rhs annihilation_number --k 1:1 --c 1:1 --limit 1 > wowii_g2_a1.lean`                                     |
| For any graph *G*, **R(G) ≤ α(G)**                | `∀ G, randic index G ≤ independence number G`                               | `(randic_index, 1, independence_number, 0)`        | `python3 utils/conjecture_generator.py --lhs randic_index --rhs independence_number --k 1:1 --c 0:0 --limit 1 > wowii_r_alpha.lean`                              |
| For any graph *G*, **r(G) ≤ α(G)**                | `∀ G, radius G ≤ independence number G`                                     | `(radius, 1, independence_number, 0)`              | `python3 utils/conjecture_generator.py --lhs radius --rhs independence_number --k 1:1 --c 0:0 --limit 1 > wowii_r_small_alpha.lean`                              |
| For any graph *G*, **d̄(G) ≤ α(G)**               | `∀ G, average distance G ≤ independence number G`                           | `(average_distance, 1, independence_number, 0)`    | `python3 utils/conjecture_generator.py --lhs average_distance --rhs independence_number --k 1:1 --c 0:0 --limit 1 > wowii_dbar_alpha.lean`                       |
| For any graph *G*, **Z(G) ≤ α(G) + 1**            | `∀ G, zero forcing number G ≤ independence number G + 1`                    | `(zero_forcing_number, 1, independence_number, 1)` | `python3 utils/conjecture_generator.py --lhs zero_forcing_number --rhs independence_number --k 1:1 --c 1:1 --limit 1 > wowii_zf_alpha1.lean`                     |

### Testing the Generator

The examples provided in the table above are covered by automated tests in `tests/test_conjecture_generator.py`. These tests use `pytest` to verify that the `conjecture_generator.py` script produces the expected Lean output for each set of parameters.

To run these tests, you can use the following command from the root of the repository:

```bash
pytest tests/test_conjecture_generator.py
```

Make sure you have `pytest` and the necessary dependencies (like `networkx` and `pandas`) installed in your Python environment.

### How the flags map to the inequality

```text
lhs(G) ≤ k · rhs(G) + c
‾‾‾        ‾‾‾‾‾‾     ‾
--lhs      --k        --c
            --rhs
```

* `--lhs` / `--rhs` — invariant names (must appear in `INVARIANTS` or be added).
* `--k` — inclusive range `a:b`; `1:1` fixes it to *k* = 1.
* `--c` — inclusive range `a:b`; `0:0` or `1:1` fix the offset.
* `--limit` — stop after that many conjectures (we only need the first one).

Note: The script generates general conjectures. Conditions like `Connected G` or `Cubic G` that might appear in classical statements are not automatically added to the Lean output by this script and would need to be manually added or handled during the proving process if required. The `--graph-class` flag is not currently supported by this utility.

Save the resulting `.lean` file next to your Lean project or drop it into `lakefile.lean`, run `lake build`, and start proving!




## Sample Fajtlowicz Conjectures

The repository also keeps track of various classic inequalities. Below is a larger sampling from the dataset.  The list mirrors some of the statements found in Fajtlowicz's work:

- **Conjecture 21:** If G is a simple connected graph, then b(G) ≥ CEIL(2dist_avg(B,V))
- **Conjecture 22:** If G is a simple connected graph, then CEIL(2dist(B,V)))≥ CEIL(2dist_avg(V))
- **Conjecture 23:** If G is a simple connected graph, then b(G) ≥ FLOOR[α(G) + dist_avg(M)/2]
- **Conjecture 24:** If G is a simple connected graph, then b(G) ≥ l(G) + CEIL[minimum of dist_even(v)/3]
- **Conjecture 25:** If G is a simple connected graph, then b(G) ≥ 2CEIL[(1 + minimum of dist_even(v))/3]
- **Conjecture 26:** If G is a simple connected graph, then b(G) ≥ CEIL[1 + dd(G)^0.25]
- **Conjecture 28:** If G is a simple connected graph, then b(G) ≥ dist_min(A)+ (dist_min(M))^0.25
- **Conjecture 30:** If G is a simple connected graph, then b(G) ≥ dist_min(A)+ |E_G¯(M(G¯))|^0.25
- **Conjecture 32:** If G is a simple connected graph, then path(G) ≥ dist_avg(A) + 0.5 ecc_avg(M)
- **Conjecture 33:** If G is a simple connected graph, then path(G) ≥ CEIL[2dist_avg(M,V)]
- **Conjecture 36:** If G is a simple connected graph, then path(G) ≥ 2rad(G)/dp(G)
- **Conjecture 38:** If G is a simple connected graph, then f(G) ≥ CEIL[0.5(res(G)+b(G))]
- **Conjecture 39:** If G is a simple connected graph, then f(G) ≥ α(G) + CEIL[(1/3) dist_avg(B,V))]
- **Conjecture 41:** If G is a simple connected graph, then f(G) ≥ CEIL[dist_avg(V)*(1 + sqrt(p(G)) ]
- **Conjecture 42:** If G is a simple connected graph, then f(G) ≥ CEIL(2dist_avg(B,V))
- **Conjecture 43:** If G is a simple connected graph, then f(G) ≥ FLOOR[sqrt[path(G)*(b(G)-1)]]
- **Conjecture 44:** If G is a simple connected graph, then f(G) ≥ α(G) + FLOOR[(1/2) average of ecc(v)]
- **Conjecture 45:** If G is a simple connected graph, then f(G) ≥ FLOOR[path(G) - 1 + (1/3)(n mod Δ(G¯)) ]
- **Conjecture 46:** If G is a simple connected graph, then f(G) ≥ FLOOR[path(G) - 1 + (1/3)(n mod Δ(G)) ]
- **Conjecture 49:** If G is a simple connected graph, then f(G) ≥ CEIL[ 2 + (1/6)*length(G¯) ]
- **Conjecture 51:** If G is a simple connected graph, then f(G) ≥ diam(G) + FLOOR[(1/3)*dd(G) ]
- **Conjecture 52:** If G is a simple connected graph, then f(G) ≥ CEIL[(1/2)*[dd(G) + 1 + (n mod Δ(G))] ]
- **Conjecture 53:** If G is a simple connected graph, then f(G) ≥ 2CEIL[mode_min(G¯)/deg_avg(G)]
- **Conjecture 54:** If G is a simple connected graph, then f(G) ≥ CEIL[dist_avg(V) +(1/2)*minimum of dist_even(v)]
- **Conjecture 55:** If G is a simple connected graph, then f(G) ≥ CEIL[minimum of dist_even(v) -1 + |N(A)|/3], where A is the set of vertices of minimum degree.
- **Conjecture 56:** If G is a simple connected graph, then f(G) ≥ CEIL[sqrt[dist_max(A)*(1+deg_avg(G¯))]], where A is the set of vertices of minimum degree.
- **Conjecture 60:** If G is a simple connected graph, then f(G) ≥ domination(G) + FLOOR[tree(G)/2]
- **Conjecture 62:** If G is a simple connected graph, then f(G) ≥ domination(G) + maximum of l(v) -1
- **Conjecture 69:** If G is a simple connected graph, then tree(G) ≥ maximum of l(v) + FLOOR[sqrt(domination(G))]
- **Conjecture 70:** If G is a simple connected graph, then tree(G) ≥ FLOOR[dist_avg(C,V)] + maximum of l(v)
- **Conjecture 71:** If G is a simple connected graph, then tree(G) ≥ FLOOR[dist_avg(B,V)/3] + maximum of l(v)
- **Conjecture 73:** If G is a simple connected graph, then tree(G) ≥ FLOOR[average of ecc(v)/2] + maximum of l(v)
- **Conjecture 74:** If G is a simple connected graph, then tree(G) ≥ CEIL(2dist_avg(B,V))
- **Conjecture 75:** If G is a simple connected graph, then tree(G) ≥ b(G)/FLOOR[deg_avg(G)]
- **Conjecture 77:** If G is a simple connected graph, then tree(G) ≥ dist_avg(C,V) + ecc(B) + 1, where B is the set of vertices of boundary vertices.
- **Conjecture 78:** If G is a simple connected graph, then tree(G) ≥ CEIL[path(G)/3 + maximum of l(v) -1]
- **Conjecture 79:** If G is a simple connected graph, then tree(G) ≥ (n mod 2)* CEIL(2dist_avg(V))
- **Conjecture 80:** If G is a simple connected graph, then tree(G) ≥ CEIL[sqrt[2*sqrt[|N(M¯)| + 1]]], where M¯ is the set of vertices of maximum degree of the complement of G.
- **Conjecture 81:** If G is a simple connected graph, then tree(G) ≥ CEIL[sqrt[2*(1+sqrt[|N(A)|])]], where A is the set of vertices of minimum degree.
- **Conjecture 82:** If G is a simple connected graph, then tree(G) ≥ 2CEIL[(2*ecc(B) + 1)/3], where B is the set of vertices of boundary vertices.
- **Conjecture 87:** If G is a simple connected graph, then b(G) ≤ 1 + minimum of l(v)  + Δ(G¯)
- **Conjecture 88:** If G is a simple connected graph, then b(G) ≤ 1 + average of l(v)  + average degree of G¯.
- **Conjecture 90:** If G is a simple connected graph, then b(G) ≤ f(G) * (FLOOR[2^average of l(v)])/2
- **Conjecture 95:** If G is a simple connected graph, then α(G) ≤ CEIL[f(G) -LN(path(G))]
- **Conjecture 104:** If G is a simple connected graph, then α(G) ≤ rad(G) + maximum of l(v) + |N(S) - S| -1, where S is the set of minimum degree vertices of the complement of the graph G and the neighborhood is taken in the complement.
- **Conjecture 105:** If G is a simple connected graph, then α(G) ≤ tree(G)*SQRT[domination(G)] - 1
- **Conjecture 107:** If G is a simple connected graph, then α(G) ≤ maximum dist_even(v)* CEIL[dist_avg(B,V)/2]
- **Conjecture 110:** If G is a simple connected graph, then α(G) ≤ FLOOR[(residue(G)+1)* average of l(v) - 1]
- **Conjecture 123:** If G is a connected X,Y bigraph such that |X| ≤ |Y|, then m(G) ≥ minimum{FLOOR[1 + deg_avg(G)}, |X|}
- **Conjecture 126:** Let G be a connected X,Y bigraph such that |X| ≤ |Y|, and let A be the set of vertices of minimum degree. Then m(G) ≥ minimum{|N(A)-A|, |X|}
- **Conjecture 128:** Let G be a connected X,Y bigraph such that |X| ≤ |Y|,. Then m(G) ≥ minimum of { freq(δ(G)), freq(σ(G)), Δ(Y)}
- **Conjecture 132:** If G is a simple connected graph, then path(G) ≥ 2*rad(G)/|N(A)|, where A is the set of vertices of minimum degree.
- **Conjecture 134:** If G is a simple connected graph, then path(G) ≥ girth - 1+ ecc(centers(G^2))
- **Conjecture 139:** If G is a simple connected graph, then path(G) ≥ u(G)*(1+2*dist_avg(C))
- **Conjecture 148:** If G is a simple connected graph, then tree(G) ≥ diameter(G) -1 + CEIL(dist_avg(Centers(G^2,V))
- **Conjecture 149:** If G is a simple connected graph, then tree(G) ≥ 1+ m(G) *c_K3(G)
- **Conjecture 150:** If G is a simple connected graph, then tree(G) ≥ Tdist_min(v)/m(G)
- **Conjecture 151:** Let er = maximum of {|E(R(v))|: v is a center of G}. If G is a simple connected graph, then tree(G) ≥ 1 + er ^c_c4(G)
- **Conjecture 156:** If G is a simple connected graph, then L_s(G) ≥ order of the intersection of radial circles + CEIL[0.5*dist_avg(Centers)].
- **Conjecture 167:** If G is a simple connected graph, then L_s(G) ≥ δ(G) + FLOOR[(1/3)*|N(M^2)-M^2|], where M^2 is the set of vertices of maximum degree of G^2and the neighborhood is taken in G^2.
- **Conjecture 168:** If G is a simple connected graph, then L_s(G) ≥ 2CEIL[|N(A)-A|/3], where A is the set of vertices of minimum degree of G.
- **Conjecture 170:** If G is a simple connected graph, then L_s(G) ≥ [maximum  of  dist_even(v)  in G] - [minimum of  dist_even(v) in G^2.]
- **Conjecture 187:** If G is a simple connected graph on at least 2 vertices, then L_s(G) + b(G) ≥  |N(M^2)-M^2|+ minimum of l(v) + 2, where M^2 is the set of vertices of maximum degree of G^2.
- **Conjecture 193:** If G is a simple connected graph with n > 1 such that 1+  Σ(G¯) ≤ frequency of λ_max(G)  then G has a Hamiltonian path.
- **Conjecture 202:** If G is a simple connected graph with n > 1 such that λ_max(G) ≤  κ(G) , then G has a Hamiltonian path.
- **Conjecture 204:** If G is a simple connected graph with n > 1 such that induced circumference(G) ≥ 2+ median of degree sequence of G¯,  then G has a Hamiltonian path.
- **Conjecture 210:** If G is a simple connected graph with n > 1 such that (2/3)*lower median of degree sequence of G¯ ≤ λ_min(G¯), then G has a Hamiltonian path.
- **Conjecture 211:** If G is a simple connected graph with n > 1 such that 2*( the lower median of degree sequence of G¯ ) ≤ |N(A)|, then G has a Hamiltonian path, where A is the set of vertices of minimum degree.
- **Conjecture 212:** If G is a simple connected graph with n > 1 such that 2*(the median of degree sequence of G¯  - 1) ≤ |N(A) - A|, then G has a Hamiltonian path, where A is the set of vertices of minimum degree.
- **Conjecture 214:** Let M = {v:  λ(v) = λ_max(G)}. Then if G is a simple connected graph with n > 1 such that  3*g_2 (G¯)  ≤  |M|   , then G has a Hamiltonian path.
- **Conjecture 216:** If G is a simple connected graph with n > 1 such that 1/(2-B(G))  ≤  c_claw(G),  then G has a Hamiltonian path.
- **Conjecture 218:** If G is a simple connected graph with n > 1 such that maximum {dist_even(v) - even horizontal(v): v in V(G)}  ≤  4*c_residue=2(G) + 1,  then G has a Hamiltonian path.
- **Conjecture 219:** If G is a simple connected graph with maximum degree equal to minimum degree, then α(G) = maximum{ceiling[b(G)/2], maximum {dist_even(v) - even horizontal(v): v in V(G)}}
- **Conjecture 227:** If G is a simple connected graph such that Δ(G) ≤ n(G)/2 , then γ_t(G) ≥ γ(G¯)
- **Conjecture 234:** If G is a simple connected graph, then γ_t(G) ≥ ecc(B)/mode_min(G).
- **Conjecture 236:** If G is a simple connected graph such that girth(G) ≥ 5, then γ_t(G) ≥  ecc(B).
- **Conjecture 237:** If G is a simple connected graph such that δ(G) ≥ 2, then γ_t(G) ≥  ecc(B).
- **Conjecture 238:** If G is a simple connected graph, then γ_t(G) ≥  (3/2)*number of components(<N[S]>), where <N[S]> is the subgraph induced by the closed neighborhood of the set of vertices of degree two.
- **Conjecture 239:** If G is a simple connected C_4-free graph, then γ_t(G) ≥  number of components(<N(S)>), where <N(S)> is the subgraph induced by the neighborhood of the set of vertices of degree two.
- **Conjecture 240:** If G is a tree, then γ_t(G) ≥  number of components(<N(S)-S>), where S is the set of vertices of degree two.
- **Conjecture 243:** If G is a simple connected C_4-free graph, then γ_t(G) ≥ 1 + number of components(<M>), where <M> is the subgraph induced by the set of vertices of maximum degree.
- **Conjecture 244:** If G is a simple connected graph, then γ_t(G) ≥ [1 + components(<M>)]/median(G), where <M> is the subgraph induced by the set of vertices of maximum degree.
- **Conjecture 245:** If G is a simple connected graph such that δ(G) ≥ 3, then γ_t(G) ≥ FLOOR[ecc_avg(M)], where M is the set of vertices of maximum degree.
- **Conjecture 246:** If G is a tree, then γ_t(G) ≥  m(G) - 1
- **Conjecture 248:** If G is a  simple connected  graph such that girth(G) ≥  6, then γ_t(G) ≥  SQRT[2* p(G)]
- **Conjecture 250:** If G is a  simple connected C_4-free graph, then γ_t(G) ≥  circumference(G)/2.
- **Conjecture 254:** If G is a  simple connected graph, then γ_t(G) ≥  2*|N(C)|/[maximum of {N(e): e an edge of G}], where C is the set of vertices that are centers of G.
- **Conjecture 257:** If G is a  simple connected graph, then γ_t(G) ≥  2*|S|/[maximum of {N(e): e an edge of G}], where S = {v: even(v) = maximum {even(w) :  even(w) = |{u : dist(w,u} is even}|}.
- **Conjecture 262:** If G is a tree, then γ_t(G) ≥  (1/2)*|N(S)|, where S is the set of vertices of  degree two.
- **Conjecture 264:** If G is a  simple connected graph, then γ_t(G) ≥  FLOOR[average of {dist(C,v): v in V-C} + average of {dist(B,v): v in V-B}], where B is the set of vertices of maximum eccentricity , C the set of vertices of minimum eccentricity and dist(S,v) = minimum {dist(s,v): s in S}.
- **Conjecture 265:** If G is a  simple connected graph  such that Δ(G) ≤ 3, then γ_t(G) ≥  FLOOR[2dist_avg(B,V)].
- **Conjecture 266:** If G is a  simple connected graph, then γ_t(G) ≥  FLOOR[dist_avg(A,V)], where A is the set of minimum degree vertices.
- **Conjecture 270:** If G is a  simple connected graph  such that Δ(G) ≤ 3, then γ_t(G) ≥  (1/2)*|S|, where S = {v: even(v) = maximum {even(w) :  even(w) = |{u : dist(w,u} is even}|}. 
- **Conjecture 272:** If G is a  simple connected graph such that Δ(G) ≤ n(G)/2, then γ_t(G) ≥  2*SQRT[dist_max(M,V)], where M is the set of vertices of maximum degree.
- **Conjecture 273:** If G is a  simple connected C_4-free graph, then γ_t(G) ≥  2^(q-1), where q is the 1st quartile of the degree sequence.
- **Conjecture 274:** If G is a  simple connected graph, then γ_t(G) ≥  k/median(G), where k is the kth step for a zero in the Havil-Hakimi process.
- **Conjecture 275:** If G is a  simple connected graph such that girth(G) ≥ 6, then γ_t(G) ≥  δ(G^2) -1.
- **Conjecture 276:** If G is a  simple connected graph such that girth(G) ≥ 6, then γ_t(G) ≥  maximum{horizontal(v) : v a vertex} + 1.
- **Conjecture 282:** If G is a simple connected graph such that n(G)> 2, then γ_t(G) ≤  k+ m(G), where k = nonzero minimum{maximum{k,|D_k|: D_k is the set of vertices of degree k }: k a positive integer}.
- **Conjecture 283:** If G is a simple connected graph such that n(G)> 2, then γ_t(G) ≤ |N(A)|+ m(G), where A is the set of vertices of minimum degree.
- **Conjecture 284:** If G is a simple connected graph such that n(G)> 2, then γ_t(G) ≤  |A|+ m(G), where A is the set of vertices of minimum degree.
- **Conjecture 286:** If G is a simple connected graph such that n(G)> 2, then γ_t(G) ≤  m(G) + |{T(w) : T(w) = maximum{T(v): v a vertex}}|, where T(v) is the number of triangles incident to vertex v.
- **Conjecture 289:** If G is a simple connected graph such that n(G)> 2, then γ_t(G) ≤ p(G) + CEIL[(1/2)*b(G)]
- **Conjecture 292:** If G is a simple connected graph such that n(G)> 2, then γ_t(G) ≤ k + residue(G), where k is the first step in which a zero appears in the Havil-Hakimi process.
- **Conjecture 293:** If G is a simple connected graph such that n(G)> 2, then γ_t(G) ≤ 2*residue(G)
- **Conjecture 307:** If G is a simple connected graph such that n(G)> 2 with at least one vertex of even degree, then γ_t(G) ≤ maxine(G) + maximum of even degrees
- **Conjecture 311:** If G is a simple connected graph such that n(G)> 2, then γ_t(G) ≤ radius(G) + frequency of minimum{K(v): K(v) is the number of K4 incident to a vertex v}
- **Conjecture 312:** If G is a simple connected graph such that n(G)> 2 with at least one vertex of even degree, then γ_t(G) ≤ maximum of even degrees + independence number
- **Conjecture 313:** If G is a simple connected graph such that n(G)> 2, then γ_t(G) ≤ diameter(G) + frequency T_min(v)
- **Conjecture 335:** If T is a tree on n > 2 vertices with degree 2 vertices,  then γ_t≤ number of isolates of <S(T)> + γ(T) * order of a largest component of <D_2>, where S(T) is the set of support vertices of T and D_2={v| deg(v) = 2} 
- **Conjecture 336:** If T is a tree on n > 2 vertices,  then γ_t ≤  number of isolates of <S(T)> + γ(T) + |E_B(T)| ,  where E_B(T) = {(uv}=e ∈E(T): deg(u)=deg(v)} called here the balanced edges of the graph. 
- **Conjecture 337:** If T is a tree on n > 2 vertices,  then γ_t ≤  |S(T)| + ⌈ half of nonzero minimum of maximum{k, |D_k(T¯)|}⌉, where S(T) is the set of support vertices of T and D_k(T¯) = {v: deg(v) =k} 
- **Conjecture 338:** If T is a tree on n > 2 vertices,  then γ_t ≤ diam(T)* ⌈|S(T)|/3⌉ 
- **Conjecture 339:** If T is a tree on n > 2 vertices,  then γ_t ≤ ecc(B) + mode_max(T)* γ(T) 
- **Conjecture 368:** If T is a tree on n>2 vertices, then γ_T(T) ≥  1 + k, where k corresponds to the kth step for a zero in the Havil-Hakimi process of a degree sequence.
- **Conjecture 400a:** Let G be a connected graph on n > 3 vertices. Then γ_2 ≤  A(G) + FLOOR[1/dd_k4], where A(G) is the annihilation number and dd_k4 is the number of distinct values that occur in the sequence k_1, k_2, ...k_n where k_i is the number of  K_4 incident to vertex i.
- **Conjecture 400b:** Let G be a connected graph on n > 3 vertices.  Then  if G has more than n(n-1)/4 edges, then γ_2 ≤   A(G) + (n mod 3 ), if G has at most n(n-1)/4 edges, then γ_2 ≤   A(G) + (n mod 3 )+ 1, where  A(G) is the annihilation number .
- **Conjecture 414:** Let G be a connected graph on n > 3 vertices and H the union of all maximum critical independent sets of G. Then |H| ≥ α_c(G)*FLOOR[1/lower median].
- **Conjecture 418d:** Let G be a connected graph on n > 3 vertices, A the set of minimum degree vertices, M the maximum degree vertices of G, and K_4(G) the vertices incident to the most K_4. Then i(G) ≤ |A| *|K_4(G)| + γ(G[V-M])
- **Conjecture 418e:** Let G be a connected graph on n > 3 vertices, A the set of minimum degree vertices, and D the set of neighbor dominators. Then i(G) ≤  |A|  +  diameter(G) + |E(D, V-D)|.
- **Conjecture 421d:** Let G be a connected graph on n > 3 vertices and M the vertices of maximum degree. Then i(G) ≤  FLOOR[0.5γ_2(G)]α(G[N(M)]). 
- **Conjecture 424:** Let G be a connected graph on n > 3 vertices, M its set of maximum degree vertices and D the set of vertices each of whose closed neighborhood contains the closed neighborhood of some other vertex. Then i(G) ≤  |E(D,V-D)|+ α(G[M]) + γ(G[V-M]). 
- **Conjecture 425a:** Let G be a connected graph on n > 3 vertices and M the vertices of maximum degree. Then i(G) ≤  |T_min(G)|+ isol(G[B]) + γ(G[V-N(P)]). 
- **Conjecture 425b:** Let G be a connected graph on n > 3 vertices and A the core of G. Then i(G) ≤  2|T_min(G)|(2+c(G[N[A]])), where c(G[N[A]]) is the order of a largest component of the subgraph induced by N[A]. 
- **Conjecture 425c:** Let G be a connected graph on n > 3 vertices and M the vertices of maximum local independence of G. Then i(G) ≤ 2|T_min(G)|FLOOR[0.5|N[M]|]. 
- **Conjecture 428:** Let G be a connected graph on n > 3 vertices and M the vertices of maximum degree and x = the number of vertices with  minimum{deg(v) + m(G[V-N(v)])  : v in V(G) }. Then i(G) ≤  γ(G[V-N(P)]) + (n mod Δ(G)) + x.
- **Conjecture 429:** Let G be a connected graph on n > 3 vertices and M the vertices of maximum degree and D_avg(P)  average of distance from each periphery vertex of graph. Then i(G) ≤  D_avg(P)*(α(G[N(M)]) + 1)
- **Conjecture 445b:** Let G be a connected graph on n > 3 vertices. Then α_2(G)≤ α_3(G) - FLOOR[c(G[H_3]/3], where H_3 is the set of vertices of degree at least 3 in G.

## Selected WOWII Open Problems

Below are 25 inequalities from the WOWII list that remain unsolved. Each one can be generated with `utils/conjecture_generator.py`.

- **Open Problem 1:** independence_number(G) ≤ vertex_cover_number(G) + 1
- **Open Problem 2:** chromatic_number(G) ≤ vertex_cover_number(G) + 1
- **Open Problem 3:** matching_number(G) ≤ vertex_cover_number(G) + 1
- **Open Problem 4:** clique_number(G) ≤ chromatic_number(G) + 1
- **Open Problem 5:** vertex_cover_number(G) ≤ 2 · matching_number(G)
- **Open Problem 6:** min_edge_cover(G) ≤ vertex_cover_number(G) + 1
- **Open Problem 7:** diameter(G) ≤ 2 · triameter(G)
- **Open Problem 8:** randic_index(G) ≤ independence_number(G) + 1
- **Open Problem 9:** harmonic_index(G) ≤ independence_number(G) + 2
- **Open Problem 10:** sum_connectivity_index(G) ≤ independence_number(G) + 3
- **Open Problem 11:** residue(G) ≤ independence_number(G)
- **Open Problem 12:** annihilation_number(G) ≤ 2 · independence_number(G)
- **Open Problem 13:** sub_total_domination_number(G) ≤ independence_number(G) + 2
- **Open Problem 14:** slater(G) ≤ independence_number(G) + 1
- **Open Problem 15:** wiener_index(G) ≤ 2 · independence_number(G) + 3
- **Open Problem 16:** independence_number(G) ≤ annihilation_number(G) + 1
- **Open Problem 17:** chromatic_number(G) ≤ clique_number(G) + 1
- **Open Problem 18:** matching_number(G) ≤ min_edge_cover(G) + 1
- **Open Problem 19:** triameter(G) ≤ 3 · radius(G)
- **Open Problem 20:** randic_index(G) ≤ wiener_index(G) + 1
- **Open Problem 21:** harmonic_index(G) ≤ wiener_index(G) + 2
- **Open Problem 22:** sum_connectivity_index(G) ≤ wiener_index(G) + 2
- **Open Problem 23:** residue(G) ≤ wiener_index(G)
- **Open Problem 24:** annihilation_number(G) ≤ wiener_index(G) + 3
- **Open Problem 25:** independence_number(G) ≤ wiener_index(G) + 2

