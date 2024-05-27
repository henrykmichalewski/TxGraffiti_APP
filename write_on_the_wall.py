import pandas as pd
import pickle
import os
from functions import (
    make_all_upper_linear_conjectures,
    make_all_lower_linear_conjectures,
    dalmatian,
    filter_conjectures,
    filter_known_conjectures,
    invariants,
    booleans,
    print_title
)

# Constants
VERSION = '1.0.0'
DATA_FILE = "training-data/data.csv"
KNOWN_CONJECTURES_FILE = "known_theorems.pkl"

def load_known_conjectures(file_path):
    if os.path.exists(file_path):
        with open(file_path, 'rb') as file:
            return pickle.load(file)
    return {"conjectures": [], "citations": []}

def save_known_conjectures(file_path, known_conjectures):
    with open(file_path, 'wb') as file:
        pickle.dump(known_conjectures, file)

def get_user_input(prompt, options):
    print(prompt)
    for i, option in enumerate(options, start=1):
        print(f"{i}: {option}")
    choice = int(input("Enter the index of your choice: ")) - 1
    print()
    return choice

def main():
    # Print the title of the program.
    print_title(version=VERSION)

    # Read the CSV file into a DataFrame.
    df = pd.read_csv(DATA_FILE)

    # Load known conjectures and citations.
    known_conjectures_data = load_known_conjectures(KNOWN_CONJECTURES_FILE)
    known_conjectures = known_conjectures_data["conjectures"]
    known_citations = known_conjectures_data["citations"]

    # Gather numerical and boolean columns.
    numerical_columns = [col for col in df.columns if col in invariants]
    boolean_columns = [col for col in df.columns if col in booleans]

    # Print and select the invariant to conjecture on.
    invariant_index = get_user_input("The graph invariants to conjecture on are:", numerical_columns)
    target = numerical_columns[invariant_index]

    # Ask if the user wants to consider a single property.
    single_property_answer = input("Would you like to only consider a specific type of graph? (y/n): ").strip().lower() == "y"
    print()

    if single_property_answer:
        # Print and select the specific property to consider.
        property_index = get_user_input("The types of objects are:", boolean_columns)
        boolean_columns = [boolean_columns[property_index]]

    # Ask if the user wants to apply the Dalmatian heuristic.
    dalmatian_answer = input("Apply the Dalmatian heuristic to the list of conjectures? (y/n): ").strip().lower() == "y"
    print()

    # Generate conjectures.
    upper_conjectures = make_all_upper_linear_conjectures(df, target, numerical_columns, boolean_columns)
    lower_conjectures = make_all_lower_linear_conjectures(df, target, numerical_columns, boolean_columns)
    conjectures = upper_conjectures + lower_conjectures

    if dalmatian_answer:
        conjectures = dalmatian(df, conjectures)

    conjectures = filter_conjectures(df, conjectures)
    conjectures = filter_known_conjectures(conjectures, known_conjectures)
    display_conjectures(conjectures)

    # Collect and filter known conjectures.
    known_conjecture_answer = input("Are any of the conjectures known to be true? (y/n): ").strip().lower() == "y"
    while known_conjecture_answer:
        new_known_conjectures, conjectures, new_known_citations = handle_known_conjectures(conjectures, df, dalmatian_answer, upper_conjectures, lower_conjectures)
        known_conjectures.extend(new_known_conjectures)
        known_citations.extend(new_known_citations)
        save_known_conjectures(KNOWN_CONJECTURES_FILE, {"conjectures": known_conjectures, "citations": known_citations})
        display_conjectures(conjectures)
        known_conjecture_answer = input("Are any of the conjectures known theorems? (y/n): ").strip().lower() == "y"
        print()

def display_conjectures(conjectures):
    print_title(version=VERSION)
    print("The conjectures are:")
    for i, conjecture in enumerate(conjectures, start=1):
        print(f"Conjecture {i}: {conjecture} (conjecture touch number = {conjecture.touch}) \n")

def handle_known_conjectures(conjectures, df, dalmatian_answer, upper_conjectures, lower_conjectures):
    known_conjecture_indices = input("Enter the indices of the conjectures that are known to be true (separated by commas): ").split(",")
    known_conjecture_indices = [int(index) - 1 for index in known_conjecture_indices]
    known_conjectures = [conjectures[index] for index in known_conjecture_indices]

    known_conjecture_citations = []
    for index in known_conjecture_indices:
        citation = input(f"Enter the citation for conjecture {index + 1}: ")
        known_conjecture_citations.append(citation)

    conjectures = upper_conjectures + lower_conjectures
    conjectures = filter_known_conjectures(conjectures, known_conjectures)

    if dalmatian_answer:
        conjectures = dalmatian(df, conjectures)

    conjectures = filter_conjectures(df, conjectures)
    return known_conjectures, conjectures, known_conjecture_citations

if __name__ == "__main__":
    main()
