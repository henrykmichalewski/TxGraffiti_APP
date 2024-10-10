from functions.invariant_functions import compute
import os
import grinpy as gp
import pandas as pd
import networkx as nx

__all__ = [
    "compute_graph_values_from_instance",
    "compute_graph_values_from_edgelist",
    "make_graph_dataframe",
    "get_graph_names",
    "make_graph_dataframe_from_edgelists",
    "write_graph_data_to_csv",
    "get_edges_from_user_input",
    "create_graph_from_user_input",
    "write_edgelist_from_user_input",
    "update_data_from_user",
    "invariants",
    "booleans",
    "add_new_invariant",
    "add_new_invariants",
]

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


def add_new_invariant(file_path, invariant):
    df = pd.read_csv(file_path)

    # Print the names of the graphs for debugging
    print("Graph names:", df.name.tolist())

    # Initialize the new column data
    new_column = []

    # Loop through each graph name and compute the strong harmonic index
    for name in df.name:
        graph_edgelist = f"graph-edgelists/{name}.txt"

        # Check if the graph file exists and handle potential errors
        try:
            G = nx.read_edgelist(graph_edgelist)
            strong_harmonic_index = compute(G, invariant)
        except Exception as e:
            print(f"Error processing {name}: {e}")
            strong_harmonic_index = None  # Handle missing or error case appropriately

        new_column.append(strong_harmonic_index)

    # Add the new data as a column to the dataframe
    df["strong_harmonic_index"] = new_column

    # Save the updated dataframe back to the CSV
    df.to_csv(file_path, index=False)

    print(f"Updated data saved to {file_path}")

def add_new_invariants(file_path, invariants):
    df = pd.read_csv(file_path)

    # Print the names of the graphs for debugging
    print("Graph names:", df.name.tolist())

    for invariant in invariants:
        # Initialize the new column data
        new_column = []

        # Loop through each graph name and compute the strong harmonic index
        for name in df.name:
            graph_edgelist = f"graph-edgelists/{name}.txt"

            G = nx.read_edgelist(graph_edgelist)
            index = compute(G, invariant)
            new_column.append(index)

        # Add the new data as a column to the dataframe
        df[f"{invariant}"] = new_column

    # Save the updated dataframe back to the CSV
    df.to_csv(file_path, index=False)

    print(f"Updated data saved to {file_path}")

def compute_graph_values_from_instance(G, name="G", invariants=invariants, properties=booleans):
    """
    Returns a dictionary of graph invariants and properties of a given graph G.

    Parameters
    ----------
    G : NetworkX graph
        An undirected graph.
    name : string
        The name of the graph G.
    invariants : list of strings
        A list of graph invariants to be calculated for the graph G.
    properties : list of strings
        A list of graph properties to be checked for the graph G.

    Returns
    -------
    dict
        A dictionary of graph invariants and properties of the graph G.
    """
    data = {}
    data["name"] = name
    for invariant in invariants:
        data[invariant] = compute(G, invariant)
    for property in properties:
        data[property] = compute(G, property)
    return data

def compute_graph_values_from_edgelist(name, path="graph-edgelists", invariants=invariants, properties=booleans):
    """
    Returns a dictionary of graph invariants and properties of a given graph G.

    Parameters
    ----------
    name : string
        The name of the file containing the graph G.
    path : string
        The path to the directory containing the graphs.
    invariants : list of strings
        A list of graph invariants to be calculated for the graph G.
    properties : list of strings
        A list of graph properties to be checked for the graph G.

    Returns
    -------
    dict
        A dictionary of graph invariants and properties of the graph G.
    """
    G = gp.read_edgelist(path + "/" + name + ".txt")
    return compute_graph_values_from_instance(G, name, invariants, properties)

def make_graph_dataframe(graphs, names, invariants=invariants, properties=booleans):
    """
    Returns a pandas dataframe of graph invariants and properties of a list of graphs.

    Parameters
    ----------
    graphs : list of NetworkX graphs
        A list of undirected graphs.
    invariants : list of strings
        A list of graph invariants to be calculated for the graphs.
    properties : list of strings
        A list of graph properties to be checked for the graphs.

    Returns
    -------
    pandas dataframe
        A pandas dataframe of graph invariants and properties of the graphs.
    """
    data = []
    for G, name in zip(graphs, names):
        data.append(compute_graph_values_from_instance(G, name, invariants, properties))
    return pd.DataFrame(data)

def get_graph_names(path="graph-edgelists"):
    """
    Returns a list of graph names from a given path.

    Parameters
    ----------
    path : string
        The path to the directory containing the graphs.

    Returns
    -------
    list of strings
        A list of graph names.
    """
    return [name[:-4] for name in os.listdir(path)]

def make_graph_dataframe_from_edgelists(path="graph-edgelists", invariants=invariants, properties=booleans):
    """
    Returns a pandas dataframe of graph invariants and properties of a list of graphs.

    Parameters
    ----------
    path : string
        The path to the directory containing the graphs.
    invariants : list of strings
        A list of graph invariants to be calculated for the graphs.
    properties : list of strings
        A list of graph properties to be checked for the graphs.

    Returns
    -------
    pandas dataframe
        A pandas dataframe of graph invariants and properties of the graphs.
    """
    graph_names = get_graph_names(path)
    graphs = []
    for graph_name in graph_names:
        graphs.append(gp.read_edgelist(path + "/" + graph_name + ".txt"))
    df = make_graph_dataframe(graphs, graph_names, invariants, properties)
    df.set_index("name", inplace=True)
    return df

def write_graph_data_to_csv():
    """
    Writes graph data to a csv file.
    """
    df = make_graph_dataframe_from_edgelists()
    df.to_csv(f"training-data/data.csv")
    return None

def get_edges_from_user_input():
    """
    Requests the user to input the name of the edgelist file.
    """
    name = input("Enter the name of your graph: ")

    # Check if the file exists
    if os.path.exists(f"graph-edgelists/{name}.txt"):
        print("This graph name exists in the database of graphs.")
        return None

    # Have the user enter each edge one by one
    edges = []
    print("Enter each edge one by one.")
    print("Enter 'done' when you are finished.")
    while True:
        edge = input("Enter the edge (v, w) in the form v w: ")
        if edge == "done":
            break
        else:
            edge = edge.split()
            edges.append((edge[0], edge[1]))

    return edges

def create_graph_from_user_input():
    edges = get_edges_from_user_input()
    return gp.Graph(edges)

def write_edgelist_from_user_input():
    name = input("Enter the name of your graph: ")

    # Check if the file exists
    if os.path.exists(f"graph-edgelists/{name}.txt"):
        print("This graph name exists in the database of graphs.")
        return None

    # Have the user enter each edge one by one
    edges = []
    print("Enter each edge one by one.")
    print("Enter 'done' when you are finished.")
    while True:
        edge = input("Enter the edge (v, w) in the form v w: ")
        if edge == "done":
            break
        else:
            edge = edge.split()
            edges.append((edge[0], edge[1]))
    with open(f"graph-edgelists/{name}.txt", "w") as f:
            for edge in edges:
                f.write(edge + "\n")
    return None

def update_data_from_user():
    name = input("Enter the name of your graph: ")

    # Check if the file exists
    if os.path.exists(f"graph-edgelists/{name}.txt"):
        print("This graph name exists in the database of graphs.")
        return None

    # Have the user enter each edge one by one
    edges = []
    print("Enter each edge one by one.")
    print("Enter 'done' when you are finished.")
    while True:
        edge = input("Enter the edge (v, w) in the form v w: ")
        if edge == "done":
            break
        else:
            edge = edge.split()
            edges.append((edge[0], edge[1]))
    with open(f"graph-edgelists/{name}.txt", "w") as f:
            for edge in edges:
                f.write(edge[0] + " " + edge[1] + "\n")
    G = gp.Graph(edges)
    values = compute_graph_values_from_instance(G, name)
    df = pd.read_csv("training-data/data.csv")
    # Append the new values to the dataframe, note that dataframes
    # do not have an append method, so we concatenate the two dataframes
    # and then drop the duplicates.
    df = pd.concat([df, pd.DataFrame(values, index=[0])], ignore_index=True)
    df.set_index("name", inplace=True)
    df.to_csv("training-data/data.csv")
    return None
