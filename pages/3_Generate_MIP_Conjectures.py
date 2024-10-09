import streamlit as st
import pandas as pd
from functions import (
    rows_multi_radio,
    multi_radio,
    invariants,
    booleans,
    conjecture_to_latex,
    conjecture_to_dict,
    def_map,
    tex_map,
)

from functions.write_on_the_wall import write_on_the_wall_with_mip
import json


DATA_FILE = "training-data/data.csv"
CONJECTURE_DATA = "training-data/conjecture-data.json"

# Load data from JSON file
with open(CONJECTURE_DATA, 'r') as f:
    data = json.load(f)

known_conjectures = data["known_conjectures"]
known_inequalities = data["known_inequalities"]

df = pd.read_csv(DATA_FILE)

numerical_columns = [col for col in df.columns if col in invariants if col not in ["semitotal_domination_number", "square_negative_energy", "square_positive_energy", "second_largest_eigenvalues", "size"]]
boolean_columns = [col for col in df.columns if col in booleans]


def generate_conjectures():
    # st.title("Generate Conjectures")
    st.set_page_config(page_title="Conjecture Generator") #, page_icon="📈")
    st.markdown("# Conjecturing with TxGraffiti")
    # st.sidebar.header("Plotting Demo")
    st.write(
        """Generate conjectures using a *mixed-integer program* that maximizes the number of equalities found in the
        formulaiton of linear inequalities.
        """
    )

    st.markdown(
    """
    # Mixed-Integer Programming (MIP) Formulation

    We define the mixed-integer programming (MIP) formulation for finding both upper and lower bounds on the target invariant $Y$ as follows:

    ## Objective
    """
    )

    # Display the objective using st.latex()
    st.latex(r"\text{Maximize} \quad \sum_{j=1}^{N} \left( z_j^{\text{upper}} + z_j^{\text{lower}} \right)")

    st.markdown(
        """
        ## Subject to:

        """
    )

    # Display the constraints using st.latex() and st.markdown() to align content
    st.latex(r"\sum_{i=1}^{k} w_i^{\text{upper}} X_{i,j} + b^{\text{upper}} \geq Y_j \quad \forall j = 1, 2, \dots, N")
    st.latex(r"\sum_{i=1}^{k} w_i^{\text{upper}} X_{i,j} + b^{\text{upper}} - Y_j \leq M(1 - z_j^{\text{upper}}) \quad \forall j = 1, 2, \dots, N")
    st.latex(r"\sum_{i=1}^{k} w_i^{\text{lower}} X_{i,j} + b^{\text{lower}} \leq Y_j \quad \forall j = 1, 2, \dots, N")
    st.latex(r"Y_j - \sum_{i=1}^{k} w_i^{\text{lower}} X_{i,j} - b^{\text{lower}} \leq M(1 - z_j^{\text{lower}}) \quad \forall j = 1, 2, \dots, N")

    st.markdown(
        """
        ## Where:
        """
    )

    # Use markdown for the list of variables
    st.markdown(
        """
        - $w_i^{\text{upper}}, w_i^{\text{lower}}$ are the weights for the upper and lower bounds, respectively,
        - $b^{\text{upper}}, b^{\text{lower}}$ are the intercepts for the upper and lower bounds, respectively,
        - $z_j^{\text{upper}}, z_j^{\text{lower}}$ are binary variables indicating if the upper or lower bounds hold with equality for each data point $j$,
        - $M$ is a large constant (Big-M) used to relax the equality constraints,
        - $X_{i,j}$ is the value of the $i$-th invariant for the $j$-th data point,
        - $Y_j$ is the value of the target invariant for the $j$-th data point.
        """
    )

    st.markdown(
        """
        This formulation ensures that the MIP solver maximizes the number of times the upper and lower bounds hold with equality, resulting in tight bounds for the target invariant $Y$. Thereafter, we apply the standard *TxGraffiti* heuristics.
        """
    )

    df = pd.read_csv(DATA_FILE)

    numerical_columns = [col for col in df.columns if col in invariants if col not in ["semitotal_domination_number", "square_negative_energy", "square_positive_energy", "second_largest_eigenvalues", "size"]]
    boolean_columns = [col for col in df.columns if col in booleans]


    # data = st.button("Update Graph Database")
    # if data:
    #     make_graph_dataframe_from_edgelists()

    # with st.sidebar:

    invariant_column = rows_multi_radio('### Select one or more graph invariants to conjecture on:', numerical_columns)
    if invariant_column == []:
        invariant_column = numerical_columns

    # removal_invariants = multi_radio('### Exclude any invariants?', numerical_columns)
    # invariant_column = [invariant for invariant in invariant_column if invariant not in removal_invariants]

    single_property = multi_radio('### Would you like TxGraffiti to focus on specific families of graphs?', boolean_columns)
    type_two_conjectures = st.radio('### Type 2 Conjecturing? (will increase the run time by several minutes)', ['no', 'yes'])
    dalmatian_answer = st.radio('### Apply the **weak**-Dalmatian heuristic or **strong**-Dalmatian heuristic for conjecture (further) filtering?', ['weak', 'strong'])

    use_strong_dalmatian = False if dalmatian_answer == 'weak' else True
    type_two_conjectures = False if type_two_conjectures == 'no' else True

    generate_conjectures = st.button('Generate Conjectures')
    conjectures = []
    if generate_conjectures:
        if single_property != []:
            boolean_columns = single_property
        for invariant in invariant_column:

            with st.spinner(f'Learning conjectures for the {invariant} ...'):
                conjectures += write_on_the_wall_with_mip(
                    df,
                    invariant,
                    numerical_columns,
                    boolean_columns,
                    known_inequalities=known_inequalities,
                    known_conjectures=known_conjectures,
                    use_strong_dalmatian=use_strong_dalmatian,
                    type_two_conjectures=type_two_conjectures,
                )
        for conj in conjectures:
            print(conj)
        st.subheader("TxGraffiti conjectures the following inequalities:")
        for i, conjecture in enumerate(conjectures):
            with st.expander(f"# Conjecture {i + 1}"):
                hypothesis = tex_map(conjecture.hypothesis.statement)
                st.write(f"{hypothesis}")
                st.latex(conjecture_to_latex(conjecture))
                st.write(r" $\text{with equality on }$" +  f"{conjecture.touch}" +  r"$\text{ graphs in the known collection of graphs.}$")

                lhs = conjecture.conclusion.lhs
                rhs = conjecture.conclusion.rhs
                st.write(f"**Definitions:** {def_map(conjecture.hypothesis.statement)} \n \n {def_map(lhs)} \n \n {def_map(rhs)}")

                # Generate the plot for the conjecture
                fig = conjecture.plot(df)
                if fig:
                    st.pyplot(fig)  # Display the plot below the conjecture

                print(conjecture.false_graphs(df))


        st.session_state.conjectures = [conjecture_to_dict(conj) for conj in conjectures]
        st.session_state.filtered_indices = list(range(len(conjectures)))


generate_conjectures()
