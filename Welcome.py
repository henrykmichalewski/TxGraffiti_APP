
import streamlit as st
from pages import *

def main():

    st.write("# TxGraffiti")

    st.markdown(
        """
        TxGraffiti is an artificial intelligence designed to generate potential research conjectures in graph theory.
        Developed using Python, and inspired Fajtlowicz's GRAFFITI and DeLaVina's Graffiti.pc,
        TxGraffiti leverages machine learning and fine-tuned heuristics to identify significant relationships
        within mathematical data. By systematically calculating numerical properties and testing for potential inequalities,
        TxGraffiti highlights the most promising conjectures for further exploration.

        To conjecture with TxGraffiti, go to the Generate Conjectures page.

        """
    )



if __name__ == "__main__":
    main()
