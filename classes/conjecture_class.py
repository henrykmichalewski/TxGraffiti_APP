
__all__ = ["Hypothesis", "LinearConclusion", "LinearConjecture"]

class Hypothesis:
    """
    A class for graph hypotheses.

    Attributes
    ----------
    statement : string
        The statement of the hypothesis.

    Methods
    -------
    __str__():
        Returns the statement of the hypothesis.
    __repr__():
        Returns the statement of the hypothesis.
    __call__(name, df):
        Returns the value of the hypothesis for the graph with the given name in the given dataframe.
    """
    def __init__(self, statement):
        self.statement = statement

    def __str__(self):
        return f"{self.statement}"

    def __repr__(self):
        return f"{self.statement}"

    def __call__(self, name, df):
        return df.loc[df["name"] == f"{name}.txt"][self.statement]


class LinearConclusion:
    """
    A class for linear graph conclusions.

    Attributes
    ----------
    lhs : string
        The left-hand side of the conclusion.
    inequality : string
        The inequality of the conclusion.
    slope : float
        The slope of the conclusion.
    rhs : string
        The right-hand side of the conclusion.
    intercept : float
        The intercept of the conclusion.

    Methods
    -------
    __str__():
        Returns the conclusion as a string.
    __repr__():
        Returns the conclusion as a string.
    __eq__(other):
        Returns True if the conclusion is equal to the other conclusion, and False otherwise.
    __ne__(other):
        Returns True if the conclusion is not equal to the other conclusion, and False otherwise.
    __call__(name, df):
        Returns the value of the conclusion for the graph with the given name in the given dataframe.
    """
    def __init__(self, lhs, inequality, slope, rhs, intercept):
        self.lhs = lhs
        self.inequality = inequality
        self.slope = slope
        self.rhs = rhs
        self.intercept = intercept

    def __str__(self):
        if self.slope == 1 and self.intercept == 0.0:
            return f"{self.lhs} {self.inequality} {self.rhs}"
        elif self.slope == 1 and self.intercept != 0.0:
            return f"{self.lhs} {self.inequality} {self.rhs} + {self.intercept}"
        elif self.slope != 1 and self.intercept == 0.0:
            return f"{self.lhs} {self.inequality} {self.slope} {self.rhs}"
        else:
            return f"{self.lhs} {self.inequality} {self.slope} {self.rhs} + {self.intercept}"

    def __repr__(self):
        if self.slope == 1 and self.intercept == 0.0:
            return f"{self.lhs} {self.inequality} {self.rhs}"
        elif self.slope == 1 and self.intercept != 0.0:
            return f"{self.lhs} {self.inequality} {self.rhs} + {self.intercept}"
        elif self.slope != 1 and self.intercept == 0.0:
            return f"{self.lhs} {self.inequality} {self.slope} {self.rhs}"
        else:
            return f"{self.lhs} {self.inequality} {self.slope} {self.rhs} + {self.intercept}"

    def __eq__(self, other):
        return self.lhs == other.lhs and self.inequality == other.inequality and self.slope == other.slope and self.rhs == other.rhs and self.intercept == other.intercept

    def __ne__(self, other):
        return not self.__eq__(other)

    def __call__(self, name, df):
        data = df.loc[df["name"] == f"{name}.txt"]
        if self.inequality == "<=":
            return data[self.lhs] <= self.slope * data[self.rhs] + self.intercept
        else:
            return data[self.lhs] >= self.slope * data[self.rhs] + self.intercept


class LinearConjecture:
    """
    A class for linear graph conjectures.

    Attributes
    ----------
    conclusion : LinearConclusion
        The conclusion of the conjecture.
    hypothesis : Hypothesis
        The hypothesis of the conjecture.
    symbol : string
        The symbol of the conjecture.
    touch : int
        The number of graphs that touch the conjecture, i.e. the number of graphs
        that satisfy the hypothesis and the conclusion with equality.

    Methods
    -------
    __repr__():
        Returns the conjecture as a string.
    __call__(name, df):
        Returns the value of the conjecture for the graph with the given name in the given dataframe.
    __eq__(other):
        Returns True if the conjecture is equal to the other conjecture, and False otherwise.
    get_sharp_graphs(df):
        Returns the graphs that touch the conjecture.

    Examples
    --------
    >>> from TxGraffiti.classes.conjecture_class import LinearConjecture
    >>> hypothesis = Hypothesis("is_connected")
    >>> conclusion = LinearConclusion("domination_number", "<=", 1/2, "order", 0)
    >>> conjecture = LinearConjecture(conclusion, hypothesis)
    >>> print(conjecture)
    """
    def __init__(self, hypothesis, conclusion, symbol="G", touch=0):
        self.hypothesis = hypothesis
        self.conclusion = conclusion
        self.symbol = symbol
        self.touch = touch

    def __repr__(self):
        hypothesis = f"If {self.symbol} is {self.hypothesis}"
        if self.conclusion.slope == 1 and self.conclusion.intercept == 0.0:
            return f"{hypothesis}, then {self.conclusion.lhs}({self.symbol}) {self.conclusion.inequality} {self.conclusion.rhs}({self.symbol})."
        elif self.conclusion.slope == 1 and self.conclusion.intercept != 0.0:
            return f"{hypothesis}, then {self.conclusion.lhs}({self.symbol}) {self.conclusion.inequality} {self.conclusion.rhs}({self.symbol}) + {self.conclusion.intercept}."
        elif self.conclusion.slope != 1 and self.conclusion.intercept == 0.0:
            return f"{hypothesis}, then {self.conclusion.lhs}({self.symbol}) {self.conclusion.inequality} {self.conclusion.slope} {self.conclusion.rhs}({self.symbol})."
        else:
            return f"{hypothesis}, then {self.conclusion.lhs}({self.symbol}) {self.conclusion.inequality} {self.conclusion.slope} {self.conclusion.rhs}({self.symbol}) + {self.conclusion.intercept}."

    def __call__(self, name, df):
        if self.hypothesis(name, df).values[0]:
            return self.conclusion(name, df).values[0]
        else:
            return False

    def __eq__(self, other):
        return self.hypothesis == other.hypothesis and self.conclusion == other.conclusion and self.symbol == other.symbol

    def get_sharp_graphs(self, df):
        return df.loc[(df[self.hypothesis.statement] == True) & (df[self.conclusion.lhs] == self.conclusion.slope * df[self.conclusion.rhs] + self.conclusion.intercept)]
