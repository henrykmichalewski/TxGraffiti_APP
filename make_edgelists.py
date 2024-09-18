import os
import itertools
import networkx as nx
from functions import compute, factors_compute
import os
import itertools
import networkx as nx
import pandas as pd
import itertools

# Function to read invariants from the file
def read_invariants(file_path):
    with open(file_path, 'r') as f:
        invariants = [line.strip() for line in f if line.strip()]  # Stripping whitespace and newlines
    return invariants

# Function to write the combinations (products and sums) to a file
def write_combinations(invariants, output_file):
    with open(output_file, 'w') as f:
        for inv in invariants:
            f.write(f"{inv} * {inv}\n")
            f.write(f"{inv} + {inv}\n")
        # Generate all combinations of two invariants
        for inv1, inv2 in itertools.combinations(invariants, 2):
            # Write both product and sum combinations
            f.write(f"{inv1} * {inv2}\n")
            f.write(f"{inv1} + {inv2}\n")

# Main function to process the file
def process_invariants(input_file, output_file):
    # Read the invariants
    invariants = read_invariants(input_file)
    # Write the combinations
    write_combinations(invariants, output_file)

# Example usage
input_file = 'functions/product_invariants.txt'
output_file = 'functions/invariant_combinations.txt'
process_invariants(input_file, output_file)



# Main function to process the graphs
def create_product_data(graph_dir='graph-small-edgelists', output_dir='training-data'):
    # Get all graph file names
    graph_files = [f for f in os.listdir(graph_dir) if f.endswith('.txt')]

    # Read single invariants
    with open('functions/product_invariants.txt', 'r') as f:
        single_invariants = [line.strip() for line in f if line.strip()]

    # Read product invariants
    with open('functions/invariant_combinations.txt', 'r') as f:
        product_invariants = [line.strip() for line in f if line.strip()]

    data = []  # This will store the rows of data

    for graph in graph_files:
        graph1_path = os.path.join(graph_dir, graph)
        graph2_path= os.path.join(graph_dir, graph)
        name = f"{graph.split('.')[0]}_product_{graph.split('.')[0]}.txt"

        # Read graphs using networkx.read_edgelist
        G1 = nx.read_edgelist(graph1_path, nodetype=int)
        G2 = nx.read_edgelist(graph2_path, nodetype=int)


        row_data = {'graph_name': name}  # Dictionary for storing invariant values for this row

        # Compute single invariants for the product graph
        for inv in single_invariants:
            # Compute the Cartesian product using networkx.cartesian_product
            product_graph = nx.cartesian_product(G1, G2)
            row_data[f"cartesian_product_{inv}"] = compute(product_graph, inv)

            product_graph = nx.tensor_product(G1, G2)
            row_data[f"tensor_product_{inv}"] = compute(product_graph, inv)

            product_graph = nx.strong_product(G1, G2)
            row_data[f"strong_product_{inv}"] = compute(product_graph, inv)

            product_graph = nx.lexicographic_product(G1, G2)
            row_data[f"lexicographic_product_{inv}"] = compute(product_graph, inv)


        # Compute product invariants for the two original graphs
        for inv in product_invariants:
            row_data[inv] = factors_compute(G1, G2, inv)

        # Append the row data to the list
        data.append(row_data)


    # Generate all combinations of 2 graph names
    for graph1_name, graph2_name in itertools.combinations(graph_files, 2):
        graph1_path = os.path.join(graph_dir, graph1_name)
        graph2_path = os.path.join(graph_dir, graph2_name)
        name = f"{graph1_name.split('.')[0]}_product_{graph2_name.split('.')[0]}.txt"


        # Read graphs using networkx.read_edgelist
        G1 = nx.read_edgelist(graph1_path, nodetype=int)
        G2 = nx.read_edgelist(graph2_path, nodetype=int)


        row_data = {'graph_name': name}  # Dictionary for storing invariant values for this row

        # Compute single invariants for the product graph
        for inv in single_invariants:
            # Compute the Cartesian product using networkx.cartesian_product
            product_graph = nx.cartesian_product(G1, G2)
            row_data[f"cartesian_product_{inv}"] = compute(product_graph, inv)

            product_graph = nx.tensor_product(G1, G2)
            row_data[f"tensor_product_{inv}"] = compute(product_graph, inv)

            product_graph = nx.strong_product(G1, G2)
            row_data[f"strong_product_{inv}"] = compute(product_graph, inv)

            product_graph = nx.lexicographic_product(G1, G2)
            row_data[f"lexicographic_product_{inv}"] = compute(product_graph, inv)


        # Compute product invariants for the two original graphs
        for inv in product_invariants:
            row_data[inv] = factors_compute(G1, G2, inv)

        # Append the row data to the list
        data.append(row_data)

    # Convert the list of dictionaries to a pandas DataFrame
    df = pd.DataFrame(data)

    # Write the DataFrame to a CSV file
    output_csv_path = os.path.join(output_dir, 'full-graph-product-data.csv')
    df.to_csv(output_csv_path, index=False)

    print(f"Data written to {output_csv_path}")


create_product_data()