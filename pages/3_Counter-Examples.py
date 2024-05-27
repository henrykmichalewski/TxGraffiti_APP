import streamlit as st
import networkx as nx
import pandas as pd
import os
from fractions import Fraction
from pyvis.network import Network
import streamlit.components.v1 as components
from functions import (
    make_all_upper_linear_conjectures,
    make_all_lower_linear_conjectures,
    make_graph_dataframe,
    dalmatian,
    filter_conjectures,
    invariants,
    booleans,
    compute
)

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

def get_edge_list(graph):
    return list(graph.edges)

def create_empty_graph(n):
    G = nx.Graph()
    G.add_nodes_from(range(1, n + 1))
    return G

def draw_graph(graph):
    net = Network(height='500px', width='100%', notebook=True)
    for node in graph.nodes:
        net.add_node(node, label=str(node))
    for edge in graph.edges:
        net.add_edge(edge[0], edge[1])
    net.show('graph.html')
    return 'graph.html'

def save_edgelist_to_file(edgelist, filename):
    with open(filename, 'w') as f:
        f.write(edgelist)

def make_graph_dataframe_from_edgelists(path="graph-edgelists", invariants=invariants, properties=booleans):
    graph_names = os.listdir(path)
    graphs = []
    for graph_name in graph_names:
        if graph_name.endswith(".txt"):
            graphs.append(nx.read_edgelist(os.path.join(path, graph_name)))
    df = make_graph_dataframe(graphs, graph_names, invariants, properties)
    df.set_index("name", inplace=True)
    return df

def enter_counterexample():
    # st.title("Generate Conjectures")
    st.set_page_config(page_title="Counter-Examples") #, page_icon="📈")
    st.markdown("""

                # Provide TxGraffiti with a Counter-Example

        Here you can provide TxGraffiti with a counter-example graph. You can build the graph by adding edges
        and then use the graph to update the data and generate conjectures. You can also compute properties of the graph
        and generate conjectures based on the properties.

        To build the graph, enter the number of vertices and click the 'Create Graph' button. Then you can add edges
        by entering the nodes of the edge and clicking the 'Add Edge' button. Once you have added all the edges, you can
        click the 'Use this graph to update data used to generate conjectures' button to update the data and generate conjectures.

        """
    )
    num_vertices = st.number_input("Number of vertices", min_value=1, max_value=20, value=5, key="num_vertices_counter")
    create_graph = st.button("Create Graph", key="create_graph_counter")

    if create_graph:
        graph = create_empty_graph(num_vertices)
        st.session_state.graph_counter = graph

    if 'graph_counter' in st.session_state:
        graph = st.session_state.graph_counter

        st.subheader("Graph Editor")
        graph_html = draw_graph(graph)
        components.html(open(graph_html, 'r').read(), height=600)

        st.subheader("Add Edges")
        node1 = st.number_input("Node 1", min_value=1, max_value=num_vertices, value=1, key="node1_counter")
        node2 = st.number_input("Node 2", min_value=1, max_value=num_vertices, value=2, key="node2_counter")
        add_edge = st.button("Add Edge", key="add_edge_counter")

        if add_edge:
            graph.add_edge(node1, node2)
            st.session_state.graph_counter = graph
            st.experimental_rerun()

        if st.button("Use this graph to update database of graphs?", key="generate_conjectures_counter"):
            edgelist = get_edge_list(graph)
            edgelist_str = "\n".join([f"{edge[0]} {edge[1]}" for edge in edgelist])
            save_edgelist_to_file(edgelist_str, "graph-edgelists/temp_graph_counter.txt")
            df = make_graph_dataframe_from_edgelists(path="graph-edgelists", invariants=invariants, properties=booleans)
            st.write("Data updated successfully!")

            numerical_columns = [col for col in df.columns if col in invariants]
            boolean_columns = [col for col in df.columns if col in booleans]
            invariant_column = st.selectbox('Select the invariant to conjecture on:', numerical_columns, key='invariant_counter')
            single_property = st.selectbox('Would you like to only consider a single property?', ['none'] + boolean_columns, key='single_property_counter')
            dalmatian_answer = st.radio('Apply Dalmatian heuristic?', ['y', 'n'], key='dalmatian_counter')
            if st.button('Generate Conjectures', key="generate_conjectures_from_counter"):
                if single_property != 'none':
                    boolean_columns = [single_property]
                upper_conjectures = make_all_upper_linear_conjectures(df, invariant_column, numerical_columns, boolean_columns)
                lower_conjectures = make_all_lower_linear_conjectures(df, invariant_column, numerical_columns, boolean_columns)
                conjectures = upper_conjectures + lower_conjectures
                if dalmatian_answer == 'y':
                    conjectures = dalmatian(df, conjectures)
                conjectures = filter_conjectures(df, conjectures)
                st.subheader("Generated Conjectures")
                for i, conjecture in enumerate(conjectures):
                    with st.expander(f"Conjecture {i + 1}"):
                        st.write(f"{conjecture}")
                st.session_state.conjectures_counter = [conjecture_to_dict(conj) for conj in conjectures]
                st.session_state.filtered_indices_counter = list(range(len(conjectures)))

        st.subheader("Compute Graph Properties")
        properties = booleans + invariants

        property1 = st.selectbox("Select Property 1", properties, key="property1")
        property2 = st.selectbox("Select Property 2", properties, key="property2")
        property3 = st.selectbox("Select Property 3", properties, key="property3")
        property4 = st.selectbox("Select Property 4", properties, key="property4")

        if st.button("Compute Property 1"):
            value1 = compute(graph, property1)
            st.write(f"Value of {property1}: {value1}")

        if st.button("Compute Property 2"):
            value2 = compute(graph, property2)
            st.write(f"Value of {property2}: {value2}")

        if st.button("Compute Property 3"):
            value3 = compute(graph, property3)
            st.write(f"Value of {property3}: {value3}")

        if st.button("Compute Property 4"):
            value4 = compute(graph, property4)
            st.write(f"Value of {property4}: {value4}")

enter_counterexample()