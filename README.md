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



