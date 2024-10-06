from pulp import LpProblem, LpMinimize, LpMaximize, LpVariable, lpSum
from fractions import Fraction
from itertools import combinations
from classes.conjecture import Hypothesis, MultiLinearConclusion, MultiLinearConjecture

__all__ = [
    "make_upper_linear_conjecture",
    "make_lower_linear_conjecture",
    "make_all_upper_linear_conjectures",
    "make_all_lower_linear_conjectures",
]

def make_upper_linear_conjecture(
        df,
        target,
        others,
        hyp="a connected graph",
        symbol="G"
    ):
    """
    Returns a LinearConjecture object with the given hypothesis, target, and k other variables.
    The conclusion is determined by solving a linear program. The inequality is <=.

    Parameters
    ----------
    df : pandas.DataFrame
        The dataframe containing the data.
    target : string
        The name of the target variable.
    others : list of strings
        A list of the names of other variables (invariants).
    hyp : string
        The name of the hypothesis variable.
    symbol : string
        The symbol of the object in the conjecture.

    Returns
    -------
    LinearConjecture
        The conjecture with the given hypothesis, target, and k other variables.
    """

    # Filter data for the hypothesis condition.
    df = df[df[hyp] == True]

    # Get the names of each row in the dataframe.
    true_objects = df["name"].tolist()

    # df = df.groupby(others, as_index=False)[target].max()
    # Compute the maximum for each group and compare with the target column
    df['max_target'] = df.groupby(others)[target].transform('max')

    # Filter rows where the target value is equal to the group max
    df = df[df[target] == df['max_target']]

    # Extract the data from the dataframe for each 'other' variable and the target variable.
    Xs = [df[other].tolist() for other in others]  # List of lists, one list for each variable
    Y = df[target].tolist()   # List of values for the target variable

    # Initialize the LP problem.
    prob = LpProblem("Test_Problem", LpMinimize)

    # Initialize the variables for the LP, one for each "other" variable.
    ws = [LpVariable(f"w{i+1}", upBound=4, lowBound=-4) for i in range(len(others))]  # List of weight variables (w1, w2, ..., wk)
    b = LpVariable("b", upBound=3, lowBound=-3)

    # Define the objective function.
    prob += lpSum([lpSum([ws[i] * Xs[i][j] for i in range(len(others))]) + b - Y[j] for j in range(len(Y))])

    # Define the LP constraints.
    for j in range(len(Y)):
        prob += lpSum([ws[i] * Xs[i][j] for i in range(len(others))]) + b >= Y[j]
        prob += lpSum([ws[i] * Xs[i][j] for i in range(len(others))]) - b >= 0.0

    # Solve the LP.
    prob.solve()

    # Extract the solution.
    weights = [Fraction(w.varValue).limit_denominator(10) for w in ws]
    b_value = Fraction(b.varValue).limit_denominator(10)

    # Compute the number of instances of equality - the touch number of the conjecture.
    touch_set = set([true_objects[j] for j in range(len(Y))
                if Y[j] == sum(weights[i] * Xs[i][j] for i in range(len(others))) + b_value])

    touch = len(touch_set)

    # Create the hypothesis and conclusion objects.
    hypothesis = Hypothesis(hyp, true_object_set=true_objects)
    conclusion = MultiLinearConclusion(target, "<=", weights, others, b_value)

    # Return the full conjecture object (not the conclusion directly).
    return MultiLinearConjecture(hypothesis, conclusion, symbol, touch, touch_set)


def make_lower_linear_conjecture(
        df,
        target,
        others,
        hyp="a connected graph",
        symbol="G"
    ):
    """
    Returns a LinearConjecture object with the given hypothesis, target, and k other variables.
    The conclusion is determined by solving a linear program. The inequality is >=.

    Parameters
    ----------
    df : pandas.DataFrame
        The dataframe containing the data.
    target : string
        The name of the target variable.
    others : list of strings
        A list of the names of other variables (invariants).
    hyp : string
        The name of the hypothesis variable.
    symbol : string
        The symbol of the object in the conjecture.

    Returns
    -------
    LinearConjecture
        The conjecture with the given hypothesis, target, and k other variables.
    """

    # Filter data for the hypothesis condition.
    df = df[df[hyp] == True]

    # Get the names of each row in the dataframe.
    true_objects = df["name"].tolist()

    # Compute the maximum for each group and compare with the target column
    df['min_target'] = df.groupby(others)[target].transform('min')

    # Filter rows where the target value is equal to the group max
    df = df[df[target] == df['min_target']]

    # Extract the data from the dataframe for each 'other' variable and the target variable.
    Xs = [df[other].tolist() for other in others]  # List of lists, one list for each variable
    Y = df[target].tolist()   # List of values for the target variable

    # Initialize the LP problem.
    prob = LpProblem("Test_Problem", LpMaximize)

    # Initialize the variables for the LP, one for each "other" variable.
    ws = [LpVariable(f"w{i+1}", upBound=4, lowBound=-4) for i in range(len(others))]  # List of weight variables (w1, w2, ..., wk)
    b = LpVariable("b", upBound=3, lowBound=-3)  # Intercept

    # Define the objective function.
    prob += lpSum([lpSum([ws[i] * Xs[i][j] for i in range(len(others))]) + b - Y[j] for j in range(len(Y))])

    # Define the LP constraints.
    for j in range(len(Y)):
        prob += lpSum([ws[i] * Xs[i][j] for i in range(len(others))]) + b <= Y[j]
        prob += lpSum([ws[i] * Xs[i][j] for i in range(len(others))]) - b >= 0.0

    # Solve the LP.
    prob.solve()

    # Extract the solution.
    weights = [Fraction(w.varValue).limit_denominator(10) for w in ws]
    b_value = Fraction(b.varValue).limit_denominator(10)

    # Compute the number of instances of equality - the touch number of the conjecture.
    touch_set = set([true_objects[j] for j in range(len(Y))
                if Y[j] == sum(weights[i] * Xs[i][j] for i in range(len(others))) + b_value])

    touch = len(touch_set)

    # Create the hypothesis and conclusion objects.
    hypothesis = Hypothesis(hyp, true_object_set=true_objects)
    conclusion = MultiLinearConclusion(target, ">=", weights, others, b_value)

    # Return the full conjecture object (not the conclusion directly).
    return MultiLinearConjecture(hypothesis, conclusion, symbol, touch, touch_set)


def make_all_upper_linear_conjectures(df, target, others, properties):
    """
    Generates upper bound conjectures for all combinations of two invariants in the dataset.

    Parameters
    ----------
    df : pandas.DataFrame
        The dataframe containing the data.
    target : string
        The name of the target variable.
    others : list of strings
        The list of invariant names to consider for generating conjectures.
    properties : list of strings
        The list of boolean properties (hypotheses) to filter the dataset.

    Returns
    -------
    list
        A list of LinearConjecture objects representing the conjectures.
    """

    # Create conjectures for every pair of invariants in 'others' combined with each property
    conjectures = []

    # Iterate over all combinations of two invariants from 'others'
    for invariant in others:
        if invariant != target:
            for prop in properties:
                conjecture = make_upper_linear_conjecture(df, target, [invariant], hyp=prop)
                conjectures.append(conjecture)
    for other1, other2 in combinations(others, 2):
        for prop in properties:
            # Ensure that neither of the 'other' invariants is equal to the target
            if other1 != target and other2 != target:
                # Generate the conjecture for this combination of two invariants
                conjecture = make_upper_linear_conjecture(df, target, [other1, other2], hyp=prop)
                conjectures.append(conjecture)
    return conjectures

def make_all_lower_linear_conjectures(df, target, others, properties):
    # Create conjectures for every pair of invariants in 'others' combined with each property
    conjectures = []

    # Iterate over all combinations of two invariants from 'others'
    for invariant in others:
        if invariant != target:
            for prop in properties:
                conjecture = make_lower_linear_conjecture(df, target, [invariant], hyp=prop)
                conjectures.append(conjecture)
    for other1, other2 in combinations(others, 2):
        for prop in properties:
            # Ensure that neither of the 'other' invariants is equal to the target
            if other1 != target and other2 != target:
                # Generate the conjecture for this combination of two invariants
                conjecture = make_lower_linear_conjecture(df, target, [other1, other2], hyp=prop)

    return conjectures
