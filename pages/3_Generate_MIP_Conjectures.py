import streamlit as st
import pandas as pd
from functions import (
    rows_multi_radio,
    multi_radio,
    invariants,
    booleans,
    conjecture_to_latex,
    conjecture_to_lean,
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

invariants = [
    line.rstrip("\n")
    for line in open("functions/invariants.txt")
]

booleans = [
    line.rstrip("\n")
    for line in open("functions/properties.txt")
]

computable_invariants = [
    line.rstrip("\n")
    for line in open("functions/computable_invariants.txt")
]

classic_invariants = [
    line.rstrip("\n")
    for line in open("functions/classic_invariants.txt")
]

degree_sequence_invariants = [
    line.rstrip("\n")
    for line in open("functions/degree_sequence_invariants.txt")
]

domination_invariants = [
    line.rstrip("\n")
    for line in open("functions/domination_invariants.txt")
]

zero_forcing_invariants = [
    line.rstrip("\n")
    for line in open("functions/zero_forcing_invariants.txt")
]

energy_invariants = [
    line.rstrip("\n")
    for line in open("functions/energy_invariants.txt")
]

def generate_conjectures():
    st.set_page_config(page_title="Conjecture Generator") #, page_icon="📈")
    st.markdown("# Conjecturing with **TxGraffiti II**")
    st.write(
        """**TxGraffiti** is an automated conjecturing program for generating inequalities on graph invariants. The
        inequalities are generated by solving an optimization model and then filtering the conjectures using the
        variations of Fajtlowicz's Dalmatian heuristic and new custom heuristics. This version of *TxGraffiti*
        uses a mixed-integer programming (MIP) model to generate conjectures. The conjectures are then filtered
        using the Dalmatian heuristic and other custom heuristics. The conjectures are then displayed below.
        """
    )

    st.markdown("## 1. Select Target Invariants")
    st.write(
        """The invariants that you select will be the graph invariants that TxGraffiti will conjecture on.
        """
    )

    df = pd.read_csv(DATA_FILE)
    numerical_columns = [col for col in df.columns if col in invariants if col not in ["semitotal_domination_number", "square_negative_energy", "square_positive_energy", "second_largest_eigenvalues", "size"]]
    boolean_columns = ["all"]
    for col in df.columns:
        if col in booleans:
            boolean_columns.append(col)

    classic_column = rows_multi_radio('### Classic Invariants:', classic_invariants)
    domination_column = rows_multi_radio('### Domination Invariants:', domination_invariants)
    zero_forcing_column = rows_multi_radio('### Zero Forcing Invariants:', zero_forcing_invariants)
    energy_column = rows_multi_radio('### Spectral Invariants:', energy_invariants)

    invariant_column = classic_column + domination_column + zero_forcing_column + energy_column
    # invariant_column = st.multiselect('### The target invariants. Select one or more graph invariants to *target your conjectures* on:', numerical_columns)

    if invariant_column == []:
        invariant_column = numerical_columns

    st.markdown("## 2. Select Graph Families")
    st.write(
        """Use the dropdown below to select the families of graphs that you would like to conjecture on. The default choice is all types of graphs.
        """
    )
    single_property = st.multiselect('## Please specify famlies of graphs to conjecture on. The default choice being all types of graphs. ', boolean_columns)

    st.markdown("## 3. Select Conjecture Options")
    st.write(
        """Select the options below to further customize the conjectures. The **Type 2 Conjecturing** option will increase the run time by several minutes, but will
        provide inequalities with two invariants on the right-hand side. The **Dalmatian heuristics** filter conjectures based on the strength of the conjecture; the **weak**-Dalmatian heuristic
        is less strict than the **strong**-Dalmatian heuristic. The **Generate computable bounds only** option will only generate conjectures that are computable.
        """
    )
    type_two_conjectures = st.radio('### Type 2 Conjecturing? (will increase the run time by several minutes)', ['no', 'yes'])
    dalmatian_answer = st.radio('### Apply the **weak**-Dalmatian heuristic or **strong**-Dalmatian for conjecture (further) filtering?', ['weak', 'strong'])

    use_against_computable = st.radio('### Generate computable bounds only?', ['yes', 'no'])
    if use_against_computable == 'yes':
        numerical_columns = [col for col in df.columns if col in computable_invariants]

    use_strong_dalmatian = False if dalmatian_answer == 'weak' else True
    type_two_conjectures = False if type_two_conjectures == 'no' else True
    single_property = ["all"] if single_property == [] else single_property

    generate_conjectures = st.button('Generate Conjectures')
    conjectures = []
    if generate_conjectures:
        if "all" not in single_property:
            boolean_columns = single_property
        else:
            boolean_columns = [col for col in df.columns if col in booleans]
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
            print(conjecture)
            with st.expander(f"# Conjecture {i + 1}"):
                hypothesis = tex_map(conjecture.hypothesis.statement)
                st.write(f"{hypothesis}")
                st.latex(conjecture_to_latex(conjecture))
                st.code(conjecture_to_lean(conjecture), language="lean")
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
