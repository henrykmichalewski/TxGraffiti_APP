from classes.conjecture_class import Hypothesis, LinearConclusion, LinearConjecture
from pulp import *
import numpy as np
from fractions import Fraction

__all__ = [
    "make_upper_linear_conjecture",
    "make_lower_linear_conjecture",
    "make_all_upper_linear_conjectures",
    "make_all_lower_linear_conjectures",
    "filter_conjectures",
    "filter_known_conjectures",
    "dalmatian",
    "write_on_the_wall",
]

def make_upper_linear_conjecture(
        df,
        target,
        other,
        hyp = "is_connected",
        symbol = "G",
    ):
    """
    Returns a LinearConjecture object with the given hypothesis, target, and other variables. The
    conclusion is determined by solving a linear program. The inequality is <=.

    Parameters
    ----------
    df : pandas.DataFrame
        The dataframe containing the data.
    target : string
        The name of the target variable.
    other : string
        The name of the other variable.
    hyp : string
        The name of the hypothesis variable.
    symbol : string
        The symbol of the object in the conjecture.

    Returns
    -------
    LinearConjecture
        The conjecture with the given hypothesis, target, and other variables.

    Examples
    --------
    >>> from functions import make_upper_linear_conjecture
    >>> import pandas as pd
    >>> df = pd.read_csv("training-data/data.csv")
    >>> make_upper_linear_conjecture(df, "zero_forcing_number", "independence_number")
    """

    # Extract the data from the dataframe.
    df = df[df[hyp] == True]
    X = df[other].to_numpy()
    Y = df[target].to_numpy()

    # Initialize the LP, say "prob".
    prob = LpProblem("Test_Problem", LpMinimize)

    # Initialize the variables for the LP.
    w = LpVariable("w")
    b = LpVariable("b")

    # Define the objective function.
    prob += np.sum(X*w + b - Y)

    # Define the LP constraints.
    for x, y in zip(X, Y):
        prob += w*x + b - y >= 0
        # prob += w*x - b >= 1

    # Solve the LP.
    prob.solve()

    # Extract the solution.
    m = Fraction(w.varValue).limit_denominator(10)
    b = Fraction(b.varValue).limit_denominator(10)

    # Compute the number of instances of equality.
    touch = np.sum(Y == m*X + b)

    # Create the hypothesis and conclusion objects.
    hypothesis = Hypothesis(hyp)
    conclusion = LinearConclusion(target, "<=", m, other, b)

    return LinearConjecture(hypothesis, conclusion, symbol, touch)

def make_lower_linear_conjecture(
        df,
        target,
        other,
        hyp = "is_connected",
        symbol = "G",
    ):
    """
    Returns a LinearConjecture object with the given hypothesis, target, and other variables. The
    conclusion is determined by solving a linear program. The inequality is >=.

    Parameters
    ----------
    df : pandas.DataFrame
        The dataframe containing the data.
    target : string
        The name of the target variable.
    other : string
        The name of the other variable.
    hyp : string
        The name of the hypothesis variable.
    symbol : string
        The symbol of the object in the conjecture.

    Returns
    -------
    LinearConjecture
        The conjecture with the given hypothesis, target, and other variables.

    Examples
    --------
    >>> from functions import make_lower_linear_conjecture
    >>> import pandas as pd
    >>> df = pd.read_csv("training-data/data.csv")
    >>> make_lower_linear_conjecture(df, "zero_forcing_number", "independence_number")
    """

    # Extract the data from the dataframe.
    df = df[df[hyp] == True]
    X = df[other].to_numpy()
    Y = df[target].to_numpy()

    # Initialize the LP, say "prob".
    prob = LpProblem("Test_Problem", LpMaximize)

    # Initialize the variables for the LP.
    w = LpVariable("w")
    b = LpVariable("b")

    # Define the objective function.
    prob += np.sum(X*w + b - Y)

    # Define the LP constraints.
    for x, y in zip(X, Y):
        prob += w*x + b - y <= 0

    # Solve the LP.
    prob.solve()

    # Extract the solution.
    m = Fraction(w.varValue).limit_denominator(10)
    b = Fraction(b.varValue).limit_denominator(10)

    # Compute the number of instances of equality.
    touch = np.sum(Y == m*X + b)

    # Create the hypothesis and conclusion objects.
    hypothesis = Hypothesis(hyp)
    conclusion = LinearConclusion(target, ">=", m, other, b)

    return LinearConjecture(hypothesis, conclusion, symbol, touch)

def make_all_upper_linear_conjectures(df, target, others, properties):
    """
    Returns a list of LinearConjecture objects with the given target variable and other variables.

    Parameters
    ----------
    df : pandas.DataFrame
        The dataframe containing the data.
    target : string
        The name of the target variable.
    others : list of strings
        The names of the other variables.
    properties : list of strings
        The names of the hypothesis variables.

    Returns
    -------
    list of LinearConjecture
        The list of conjectures with the given target variable and other variables.

    Examples
    --------
    >>> from functions import make_all_upper_linear_conjectures
    >>> import pandas as pd
    >>> df = pd.read_csv("training-data/data.csv")
    >>> make_all_upper_linear_conjectures(df, "zero_forcing_number", ["independence_number", "order"], ["is_connected", "is_regular"])
    """
    return [make_upper_linear_conjecture(df, target, other, hyp = prop)
            for other in others for prop in properties if other != target]

def make_all_lower_linear_conjectures(df, target, others, properties):
    """
    Returns a list of LinearConjecture objects with the given target variable and other variables.

    Parameters
    ----------
    df : pandas.DataFrame
        The dataframe containing the data.
    target : string
        The name of the target variable.
    others : list of strings
        The names of the other variables.
    properties : list of strings
        The names of the hypothesis variables.

    Returns
    -------
    list of LinearConjecture
        The list of conjectures with the given target variable and other variables.

    Examples
    --------
    >>> from functions import make_all_lower_linear_conjectures
    >>> import pandas as pd
    >>> df = pd.read_csv("training-data/data.csv")
    >>> make_all_lower_linear_conjectures(df, "zero_forcing_number", ["independence_number", "order"], ["is_connected", "is_regular"])
    """
    return [make_lower_linear_conjecture(df, target, other, hyp = prop)
              for other in others for prop in properties if other != target]

def filter_conjectures(df, conjectures):
    """
    Returns a list of conjectures with the same conclusion, but with the hypothesis that has the
    most instances of equality.

    Parameters
    ----------
    df : pandas.DataFrame
        The dataframe containing the data.
    conjectures : list of LinearConjecture
        The list of conjectures to be filtered.

    Returns
    -------
    list of LinearConjecture
        The list of conjectures with the same conclusion, but with the hypothesis that has the
        most instances of equality.

    Examples
    --------
    >>> from functions import make_all_upper_linear_conjectures
    >>> from functions import filter_conjectures
    >>> import pandas as pd
    >>> df = pd.read_csv("training-data/data.csv")
    >>> conjectures = make_all_upper_linear_conjectures(df, "zero_forcing_number", ["independence_number", "order"], ["is_connected", "is_regular"])
    >>> filter_conjectures(df, conjectures)
    """
    conjectures = [conj for conj in conjectures if conj.touch > 0 and conj.conclusion.slope > 0]
    conjectures.sort(key = lambda x: x.touch, reverse=True)
    new_conjectures = conjectures.copy()
    for conj_one in conjectures:
            for conj_two in new_conjectures:
                    if conj_one.conclusion == conj_two.conclusion:
                        if len(df[df[conj_one.hypothesis.statement] == True]) > len(df[df[conj_two.hypothesis.statement] == True]):
                            new_conjectures.remove(conj_two)
    return new_conjectures

def filter_known_conjectures(conjectures, known_conjectures):
    """
    Returns a list of conjectures with the same conclusion, but with the hypothesis that has the
    most instances of equality. This is used to filter out conjectures that are already known.

    Parameters
    ----------
    conjectures : list of LinearConjecture
        The list of conjectures to be filtered.
    known_conjectures : list of LinearConjecture
        The list of conjectures that are already known.

    Returns
    -------
    list of LinearConjecture
        The list of conjectures with the same conclusion, but with the hypothesis that has the
        most instances of equality.

    Examples
    --------
    >>> from functions import make_all_upper_linear_conjectures
    >>> from functions import filter_known_conjectures
    >>> import pandas as pd
    >>> df = pd.read_csv("training-data/data.csv")
    >>> conjectures = make_all_upper_linear_conjectures(df, "zero_forcing_number", ["independence_number", "order"], ["is_connected", "is_regular"])
    >>> filter_known_conjectures(conjectures, known_conjectures)
    """
    new_conjectures = conjectures.copy()
    for conj_one in conjectures:
            for conj_two in known_conjectures:
                    if conj_one.conclusion == conj_two.conclusion and conj_one.hypothesis.statement == conj_two.hypothesis.statement:
                        new_conjectures.remove(conj_one)
    return new_conjectures

def dalmatian(df, conjectures):
    """
    Returns a list of conjectures with the same conclusion, but with the hypothesis that has the
    most instances of equality. This is used to filter out conjectures that are already known.

    Parameters
    ----------
    df : pandas.DataFrame
        The dataframe containing the data.
    conjectures : list of LinearConjecture
        The list of conjectures to be filtered.

    Returns
    -------
    list of LinearConjecture
        The list of conjectures with the same conclusion, but with the hypothesis that has the
        most instances of equality.

    Examples
    --------
    >>> from functions import make_all_upper_linear_conjectures
    >>> from functions import dalmation
    >>> import pandas as pd
    >>> df = pd.read_csv("training-data/data.csv")
    >>> conjectures = make_all_upper_linear_conjectures(df, "zero_forcing_number", ["independence_number", "order"], ["is_connected", "is_regular"])
    >>> dalmation(df, conjectures)
    """
    conj = conjectures[0]
    new_conjectures = [conj]
    sharps = set(conj.get_sharp_graphs(df).index)
    for conj in conjectures[1:]:
        if set(conj.get_sharp_graphs(df).index) - sharps != set():
            new_conjectures.append(conj)
            sharps = sharps.union(conj.get_sharp_graphs(df).index)
    return new_conjectures

def write_on_the_wall(df, targets, invariant_names, property_names, use_dalmation=True):
    """
    Returns a list of conjectures with the same conclusion, but with the hypothesis that has the
    most instances of equality. This is used to filter out conjectures that are already known.

    Parameters
    ----------
    df : pandas.DataFrame
        The dataframe containing the data.
    targets : list of str
        The list of targets.
    invariant_names : list of str
        The list of invariant names.
    property_names : list of str
        The list of property names.
    use_dalmation : bool
        Whether or not to use dalmation.

    Returns
    -------
    list of LinearConjecture
        The list of conjectures with the same conclusion, but with the hypothesis that has the
        most instances of equality.

    Examples
    --------
    >>> from functions import make_all_upper_linear_conjectures
    >>> from functions import write_on_the_wall
    >>> import pandas as pd
    >>> df = pd.read_csv("training-data/data.csv")
    >>> write_on_the_wall(df, ["zero_forcing_number"], ["independence_number", "order"], ["is_connected", "is_regular"])
    """
    conjectures = []
    for target in targets:
        upper_conjectures = make_all_upper_linear_conjectures(df, target, invariant_names, property_names)
        lower_conjectures = make_all_lower_linear_conjectures(df, target, invariant_names, property_names)
        if use_dalmation:
            conjectures += dalmatian(df, upper_conjectures + lower_conjectures)
        else:
            conjectures += upper_conjectures + lower_conjectures
    return filter_conjectures(df, conjectures)
