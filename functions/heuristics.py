
__all__ = [
    'sort_conjectures',
    'theo',
    'weak_dalmatian',
    'strong_dalmatian',
]

def sort_conjectures(conjectures):
    # Sort the conjectures by touch number.
    conjectures.sort(key=lambda x: x.touch, reverse=True)

    # Return the sorted list of conjectures.
    return conjectures

def theo(conjectures):
    """
    Removes redundant conjectures from a list.

    A conjecture is considered redundant if another conjecture has the same conclusion
    and a more general hypothesis (i.e., its true_object_set is a superset of the redundant one).

    Parameters:
    conjectures (list of Conjecture): The list of conjectures to filter.

    Returns:
    list of Conjectures: A list with redundant conjectures removed.
    """
    new_conjectures = conjectures.copy()

    for conj_one in conjectures:
        for conj_two in new_conjectures.copy():  # Make a copy for safe removal
            # Avoid comparing the conjecture with itself
            if conj_one != conj_two:
                # Check if conclusions are the same and conj_one's hypothesis is more general
                if conj_one.conclusion == conj_two.conclusion and conj_one.hypothesis > conj_two.hypothesis:
                    new_conjectures.remove(conj_two)  # Remove the less general conjecture (conj_two)

    return new_conjectures

def weak_dalmatian(conjectures):
    # Start with the conjecture that has the highest touch number (first in the list).
    conj = conjectures[0]

    # Initialize the list of strong conjectures with the first conjecture.
    strong_conjectures = [conj]

    # Get the set of sharp graphs (i.e., graphs where the conjecture holds as equality) for the first conjecture.
    sharp_graphs = conj.sharps

    # Iterate over the remaining conjectures in the list.
    for conj in conjectures[1:]:
        # Check if the current conjecture shares the same sharp graphs as any already selected strong conjecture.
        if any(conj.sharps.issuperset(known.sharps) for known in strong_conjectures):
            # If it does, add the current conjecture to the list of strong conjectures.
            strong_conjectures.append(conj)
            # Update the set of sharp graphs to include the newly discovered sharp graphs.
            sharp_graphs = sharp_graphs.union(conj.sharps)
        # Otherwise, check if the current conjecture introduces new sharp graphs (graphs where the conjecture holds).
        elif conj.sharps - sharp_graphs != set():
            # If new sharp graphs are found, add the conjecture to the list.
            strong_conjectures.append(conj)
            # Update the set of sharp graphs to include the newly discovered sharp graphs.
            sharp_graphs = sharp_graphs.union(conj.sharps)

    # Return the list of strong, non-redundant conjectures.
    return strong_conjectures

def strong_dalmatian(conjectures):
    # Start with the conjecture that has the highest touch number (first in the list).
    conj = conjectures[0]

    # Initialize the list of strong conjectures with the first conjecture.
    strong_conjectures = [conj]

    # Get the set of sharp graphs (i.e., graphs where the conjecture holds as equality) for the first conjecture.
    sharp_graphs = conj.sharps


    # Iterate over the remaining conjectures in the list.
    for conj in conjectures[1:]:
        # Check if the current conjecture set of sharp graphs is a superset of any already selected strong conjecture.
        if any(conj.sharps.issuperset(known.sharps) for known in strong_conjectures):
            # If it does, add the current conjecture to the list of strong conjectures.
            strong_conjectures.append(conj)

    # Return the list of strong, non-redundant conjectures.
    return strong_conjectures

