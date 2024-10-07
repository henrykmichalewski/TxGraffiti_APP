from pulp import LpProblem, LpMinimize, LpMaximize, LpVariable, lpSum
from fractions import Fraction
from itertools import combinations
from classes.conjecture import Hypothesis, MultiLinearConclusion, MultiLinearConjecture

__all__ = [
    "make_upper_linear_conjecture",
    "make_lower_linear_conjecture",
    "make_upper_mip_linear_conjecture",
    "make_lower_mip_linear_conjecture",
    "make_upper_lower_mip_linear_conjecture",
    "make_all_upper_linear_conjectures",
    "make_all_lower_linear_conjectures",
    "make_all_mip_linear_conjectures",
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

from pulp import *

def make_upper_mip_linear_conjecture(
        df,
        target,
        others,
        hyp="a connected graph",
        symbol="G",
    ):
    df = df[df[hyp] == True]
    true_objects = df["name"].tolist()
    df['max_target'] = df.groupby(others)[target].transform('max')
    df = df[df[target] == df['max_target']]

    Xs = [df[other].tolist() for other in others]
    Y = df[target].tolist()

    prob = LpProblem("Maximize_Equality", LpMaximize)
    ws = [LpVariable(f"w{i+1}", upBound=4, lowBound=-4) for i in range(len(others))]
    b = LpVariable("b", upBound=3, lowBound=-3)

    # Binary variables z_j to maximize equality conditions
    zs = [LpVariable(f"z{j}", cat="Binary") for j in range(len(Y))]

    M = 1000  # Big-M value
    for j in range(len(Y)):
        # Standard constraints (upper bound inequality)
        prob += lpSum([ws[i] * Xs[i][j] for i in range(len(others))]) + b >= Y[j]

        # Equality constraints using Big-M technique
        prob += lpSum([ws[i] * Xs[i][j] for i in range(len(others))]) + b - Y[j] <= M * (1 - zs[j])

    # Maximize the number of equalities
    prob += lpSum(zs)

    prob.solve()

    weights = [Fraction(w.varValue).limit_denominator(10) for w in ws]
    b_value = Fraction(b.varValue).limit_denominator(10)

    touch_set = set([true_objects[j] for j in range(len(Y)) if zs[j].varValue == 1])
    touch = len(touch_set)

    hypothesis = Hypothesis(hyp, true_object_set=true_objects)
    conclusion = MultiLinearConclusion(target, "<=", weights, others, b_value)

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

def make_lower_mip_linear_conjecture(
        df,
        target,
        others,
        hyp="a connected graph",
        symbol="G",
    ):
    df = df[df[hyp] == True]
    true_objects = df["name"].tolist()
    df['min_target'] = df.groupby(others)[target].transform('min')
    df = df[df[target] == df['min_target']]

    Xs = [df[other].tolist() for other in others]
    Y = df[target].tolist()

    prob = LpProblem("Maximize_Equality", LpMaximize)
    ws = [LpVariable(f"w{i+1}", upBound=4, lowBound=-4) for i in range(len(others))]
    b = LpVariable("b", upBound=3, lowBound=-3)

    # Binary variables z_j to maximize equality conditions
    zs = [LpVariable(f"z{j}", cat="Binary") for j in range(len(Y))]

    M = 1000  # Big-M value
    for j in range(len(Y)):
        # Standard constraints (lower bound inequality)
        prob += lpSum([ws[i] * Xs[i][j] for i in range(len(others))]) + b <= Y[j]
        prob += lpSum([ws[i] * Xs[i][j] for i in range(len(others))]) - b >= 0.0

        # Equality constraints using Big-M technique
        prob += Y[j] - lpSum([ws[i] * Xs[i][j] for i in range(len(others))]) - b <= M * (1 - zs[j])

    # Maximize the number of equalities
    prob += lpSum(zs)

    prob.solve()

    weights = [Fraction(w.varValue).limit_denominator(10) for w in ws]
    b_value = Fraction(b.varValue).limit_denominator(10)

    touch_set = set([true_objects[j] for j in range(len(Y)) if Y[j] == sum(ws[i] * Xs[i][j] for i in range(len(others))) + b])
    touch = len(touch_set)

    hypothesis = Hypothesis(hyp, true_object_set=true_objects)
    conclusion = MultiLinearConclusion(target, ">=", weights, others, b_value)

    return MultiLinearConjecture(hypothesis, conclusion, symbol, touch, touch_set)

# def make_upper_lower_mip_linear_conjecture(
#         df,
#         target,
#         others,
#         hyp="a connected graph",
#         symbol="G",
#     ):
#     """
#     Returns a MultiLinearConjecture object with different slopes for upper and lower bounds,
#     using a mixed-integer program to maximize the number of equalities.

#     Parameters
#     ----------
#     df : pandas.DataFrame
#         The dataframe containing the data.
#     target : string
#         The name of the target variable.
#     others : list of strings
#         A list of the names of other variables (invariants).
#     hyp : string
#         The name of the hypothesis variable.
#     symbol : string
#         The symbol of the object in the conjecture.

#     Returns
#     -------
#     MultiLinearConjecture
#         The conjecture with both upper and lower bounds, each with different slopes.
#     """

#     # Filter data for the hypothesis condition.
#     df = df[df[hyp] == True]
#     true_objects = df["name"].tolist()

#     # Extract the data from the dataframe for each 'other' variable and the target variable.
#     Xs = [df[other].tolist() for other in others]  # List of lists, one list for each variable
#     Y = df[target].tolist()   # List of values for the target variable

#     # Initialize the MIP problem.
#     prob = LpProblem("Maximize_Equality", LpMaximize)

#     # Initialize the variables for the MIP (one set for upper bound and one for lower bound).
#     ws_upper = [LpVariable(f"w_upper{i+1}", upBound=4, lowBound=-4) for i in range(len(others))]  # Weights for upper bound
#     ws_lower = [LpVariable(f"w_lower{i+1}", upBound=4, lowBound=-4) for i in range(len(others))]  # Weights for lower bound
#     b_upper = LpVariable("b_upper", upBound=3, lowBound=-3)
#     b_lower = LpVariable("b_lower", upBound=3, lowBound=-3)

#     # Binary variables z_j^upper and z_j^lower to maximize equality conditions
#     z_upper = [LpVariable(f"z_upper{j}", cat="Binary") for j in range(len(Y))]
#     z_lower = [LpVariable(f"z_lower{j}", cat="Binary") for j in range(len(Y))]

#     M = 1000  # Big-M value

#     for j in range(len(Y)):
#         # Upper bound constraints
#         prob += lpSum([ws_upper[i] * Xs[i][j] for i in range(len(others))]) + b_upper >= Y[j]
#         prob += lpSum([ws_upper[i] * Xs[i][j] for i in range(len(others))]) - b_upper >= 0.0
#         prob += lpSum([ws_upper[i] * Xs[i][j] for i in range(len(others))]) + b_upper - Y[j] <= M * (1 - z_upper[j])

#         # Lower bound constraints
#         prob += lpSum([ws_lower[i] * Xs[i][j] for i in range(len(others))]) + b_lower <= Y[j]
#         prob += lpSum([ws_lower[i] * Xs[i][j] for i in range(len(others))]) - b_lower >= 0.0
#         prob += Y[j] - lpSum([ws_lower[i] * Xs[i][j] for i in range(len(others))]) - b_lower <= M * (1 - z_lower[j])

#     # Maximize the number of equalities for both upper and lower bounds
#     prob += lpSum(z_upper) + lpSum(z_lower)

#     # Solve the MIP
#     prob.solve()

#     # Extract the solution.
#     weights_upper = [Fraction(w.varValue).limit_denominator(10) for w in ws_upper]
#     weights_lower = [Fraction(w.varValue).limit_denominator(10) for w in ws_lower]
#     b_upper_value = Fraction(b_upper.varValue).limit_denominator(10)
#     b_lower_value = Fraction(b_lower.varValue).limit_denominator(10)
#     if weights_lower == weights_upper and b_upper_value == b_lower_value:
#         touch_upper = len(true_objects)

#         # Create the hypothesis and conclusion objects for both upper and lower bounds.
#         hypothesis = Hypothesis(hyp, true_object_set=true_objects)
#         upper_conclusion = MultiLinearConclusion(target, "=", weights_upper, others, b_upper_value)

#         # Return the full conjecture object (not the conclusion directly).
#         return MultiLinearConjecture(hypothesis, upper_conclusion, symbol, touch_upper, true_objects), None
#     else:
#         # Compute the number of instances of equality - the touch number of the conjecture.
#         touch_set_upper = set([true_objects[j] for j in range(len(Y)) if Y[j] == sum(weights_upper[i] * Xs[i][j] for i in range(len(others))) + b_upper_value])
#         touch_set_lower = set([true_objects[j] for j in range(len(Y)) if Y[j] == sum(weights_lower[i] * Xs[i][j] for i in range(len(others))) + b_lower_value])

#         touch_upper = len(touch_set_upper)
#         touch_lower = len(touch_set_lower)

#         # Create the hypothesis and conclusion objects for both upper and lower bounds.
#         hypothesis = Hypothesis(hyp, true_object_set=true_objects)
#         upper_conclusion = MultiLinearConclusion(target, "<=", weights_upper, others, b_upper_value)
#         lower_conclusion = MultiLinearConclusion(target, ">=", weights_lower, others, b_lower_value)

#         # Return the full conjecture object (not the conclusion directly).
#         return MultiLinearConjecture(hypothesis, upper_conclusion, symbol, touch_upper, touch_set_upper), \
#             MultiLinearConjecture(hypothesis, lower_conclusion, symbol, touch_lower, touch_set_lower)


def make_upper_lower_mip_linear_conjecture(
        df,
        target,
        others,
        hyp="a connected graph",
        symbol="G",
    ):
    """
    Returns a MultiLinearConjecture object with different slopes for upper and lower bounds,
    using a mixed-integer program to maximize the number of equalities on the extreme values.

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
    MultiLinearConjecture
        The conjecture with both upper and lower bounds, each with different slopes.
    """

    # Filter data for the hypothesis condition.
    df = df[df[hyp] == True]
    true_objects = df["name"].tolist()

    # Preprocess the data to find the maximum Y for each X for the upper bound
    df_upper = df.loc[df.groupby(others)[target].idxmax()]
    # Preprocess the data to find the minimum Y for each X for the lower bound
    df_lower = df.loc[df.groupby(others)[target].idxmin()]

    # Extract the data for the upper and lower bound problems
    Xs_upper = [df_upper[other].tolist() for other in others]
    Y_upper = df_upper[target].tolist()
    Xs_lower = [df_lower[other].tolist() for other in others]
    Y_lower = df_lower[target].tolist()

    # Initialize the MIP problem.
    prob = LpProblem("Maximize_Equality", LpMaximize)

    # Initialize the variables for the MIP (one set for upper bound and one for lower bound).
    ws_upper = [LpVariable(f"w_upper{i+1}", upBound=4, lowBound=-4) for i in range(len(others))]  # Weights for upper bound
    ws_lower = [LpVariable(f"w_lower{i+1}", upBound=4, lowBound=-4) for i in range(len(others))]  # Weights for lower bound
    b_upper = LpVariable("b_upper", upBound=3, lowBound=-3)
    b_lower = LpVariable("b_lower", upBound=3, lowBound=-3)

    # Binary variables z_j^upper and z_j^lower to maximize equality conditions for extreme points
    z_upper = [LpVariable(f"z_upper{j}", cat="Binary") for j in range(len(Y_upper))]
    z_lower = [LpVariable(f"z_lower{j}", cat="Binary") for j in range(len(Y_lower))]

    M = 1000  # Big-M value

    # Upper bound constraints (maximize equality on max Y values)
    for j in range(len(Y_upper)):
        prob += lpSum([ws_upper[i] * Xs_upper[i][j] for i in range(len(others))]) + b_upper >= Y_upper[j]
        prob += lpSum([ws_upper[i] * Xs_upper[i][j] for i in range(len(others))]) + b_upper - Y_upper[j] <= M * (1 - z_upper[j])

    # Lower bound constraints (maximize equality on min Y values)
    for j in range(len(Y_lower)):
        prob += lpSum([ws_lower[i] * Xs_lower[i][j] for i in range(len(others))]) + b_lower <= Y_lower[j]
        prob += Y_lower[j] - lpSum([ws_lower[i] * Xs_lower[i][j] for i in range(len(others))]) - b_lower <= M * (1 - z_lower[j])

    # Maximize the number of equalities for both upper and lower bounds
    prob += lpSum(z_upper) + lpSum(z_lower)

    # Solve the MIP
    prob.solve()

    # Extract the solution.
    weights_upper = [Fraction(w.varValue).limit_denominator(10) for w in ws_upper]
    weights_lower = [Fraction(w.varValue).limit_denominator(10) for w in ws_lower]
    b_upper_value = Fraction(b_upper.varValue).limit_denominator(10)
    b_lower_value = Fraction(b_lower.varValue).limit_denominator(10)

    if weights_lower == weights_upper and b_upper_value == b_lower_value:
        touch_upper = len(true_objects)

        # Create the hypothesis and conclusion objects for both upper and lower bounds.
        hypothesis = Hypothesis(hyp, true_object_set=true_objects)
        upper_conclusion = MultiLinearConclusion(target, "=", weights_upper, others, b_upper_value)

        # Return the full conjecture object (not the conclusion directly).
        return MultiLinearConjecture(hypothesis, upper_conclusion, symbol, touch_upper, true_objects), None
    else:
        Xs_true_upper = [df[other].tolist() for other in others]
        Y_true_upper = df[target].tolist()
        Xs_true_lower = [df[other].tolist() for other in others]
        Y_true_lower = df[target].tolist()
        # Compute the number of instances of equality - the touch number of the conjecture.
        touch_set_upper = set([true_objects[j] for j in range(len(Y_true_upper)) if
                               Y_true_upper[j] == sum(weights_upper[i] * Xs_true_upper[i][j] for i in range(len(others))) + b_upper_value])
        touch_set_lower = set([true_objects[j] for j in range(len(Y_true_lower)) if Y_true_lower[j] == sum(weights_lower[i] * Xs_true_lower[i][j] for i in range(len(others))) + b_lower_value])

        touch_upper = len(touch_set_upper)
        touch_lower = len(touch_set_lower)

        # Create the hypothesis and conclusion objects for both upper and lower bounds.
        hypothesis = Hypothesis(hyp, true_object_set=true_objects)
        upper_conclusion = MultiLinearConclusion(target, "<=", weights_upper, others, b_upper_value)
        lower_conclusion = MultiLinearConclusion(target, ">=", weights_lower, others, b_lower_value)

        # Return the full conjecture object (not the conclusion directly).
        return MultiLinearConjecture(hypothesis, upper_conclusion, symbol, touch_upper, touch_set_upper), \
            MultiLinearConjecture(hypothesis, lower_conclusion, symbol, touch_lower, touch_set_lower)



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


def make_all_mip_linear_conjectures(df, target, others, properties):
    # Create conjectures for every pair of invariants in 'others' combined with each property
    upper_conjectures = []
    lower_conjectures = []

    # Iterate over all combinations of two invariants from 'others'
    for invariant in others:
        if invariant != target:
            for prop in properties:
                upper_conj, lower_conj = make_upper_lower_mip_linear_conjecture(df, target, [invariant], hyp=prop)
                upper_conjectures.append(upper_conj)
                if lower_conj:
                    lower_conjectures.append(lower_conj)
    for other1, other2 in combinations(others, 2):
        for prop in properties:
            # Ensure that neither of the 'other' invariants is equal to the target
            if other1 != target and other2 != target:
                # Generate the conjecture for this combination of two invariants
                upper_conj, lower_conj = make_upper_lower_mip_linear_conjecture(df, target, [other1, other2], hyp=prop)
                upper_conjectures.append(upper_conj)
                if lower_conj:
                    lower_conjectures.append(lower_conj)

    return upper_conjectures, lower_conjectures