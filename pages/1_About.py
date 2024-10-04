import streamlit as st

__all__ = ["about"]

def about():
    st.set_page_config(
        page_title="TxGraffiti: Data-Driven Conjecturing",
        page_icon="🔍",
    )

    st.write("# TxGraffiti: Automated Conjecturing on Graphs")

    st.markdown(
        """
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
    """
    )

about()