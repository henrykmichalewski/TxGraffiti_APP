__all__ =[
    "Hypothesis",
    "Conclusion",
    "Conjecture",
    "LinearConclusion",
    "MultiLinearConclusion",
    "MultiLinearConjecture"
]

class Hypothesis:
    """
    A base class for graph hypotheses.
    """
    def __init__(self, statement, true_object_set=None):
        self.statement = statement
        self.true_object_set = true_object_set

    def __str__(self):
        return f"{self.statement}"

    def __repr__(self):
        return f"{self.statement}"

    def __call__(self, name, df):
        return df.loc[df["name"] == f"{name}.txt"][self.statement]

    def _le__(self, other):
        return len(self.true_object_set) <= len(other.true_object_set)

    def __lt__(self, other):
        return len(self.true_object_set) < len(other.true_object_set)

    def __ge__(self, other):
        return len(self.true_object_set) >= len(other.true_object_set)

    def __gt__(self, other):
        return len(self.true_object_set) > len(other.true_object_set)

    def __eq__(self, other):
        return self.statement == other.statement





class Conclusion:
    """
    A base class for graph conclusions.
    """
    def __init__(self, lhs, inequality, rhs, intercept=0):
        self.lhs = lhs
        self.inequality = inequality
        self.rhs = rhs
        self.intercept = intercept

    def __str__(self):
        raise NotImplementedError("Subclasses must implement __str__")

    def __repr__(self):
        raise NotImplementedError("Subclasses must implement __repr__")

    def __call__(self, name, df):
        raise NotImplementedError("Subclasses must implement __call__")


class Conjecture:
    """
    A base class for graph conjectures.
    """
    def __init__(self, hypothesis, conclusion, symbol="G", touch=0, sharps=None):
        self.hypothesis = hypothesis
        self.conclusion = conclusion
        self.symbol = symbol
        self.touch = touch
        self.sharps = sharps

    def __str__(self):
        hypothesis = f"If {self.symbol} is {self.hypothesis}"
        return f"{hypothesis}, then {self.conclusion}"

    def __repr__(self):
        hypothesis = f"If {self.symbol} is {self.hypothesis}"
        return f"{hypothesis}, then {self.conclusion}"

    def __call__(self, name, df):
        if self.hypothesis(name, df).values[0]:
            return self.conclusion(name, df)
        else:
            return False

    def get_sharp_graphs(self, df):
        raise NotImplementedError("Subclasses must implement get_sharp_graphs")

    def __eq__(self, other):
        return self.__str__() == other.__str__()


    def __hash__(self):
        return hash((self.hypothesis, self.conclusion, self.symbol))


class LinearConclusion(Conclusion):
    """
    A class for linear graph conclusions.
    """
    def __init__(self, lhs, inequality, slope, rhs, intercept=0):
        super().__init__(lhs, inequality, rhs, intercept)
        self.slope = slope

    def __str__(self):
        if self.slope == 1 and self.intercept == 0.0:
            return f"{self.lhs} {self.inequality} {self.rhs}"
        elif self.slope == 1 and self.intercept != 0.0:
            return f"{self.lhs} {self.inequality} {self.rhs} + {self.intercept}"
        elif self.slope != 1 and self.intercept == 0.0:
            return f"{self.lhs} {self.inequality} {self.slope} * {self.rhs}"
        else:
            return f"{self.lhs} {self.inequality} {self.slope} * {self.rhs} + {self.intercept}"

    def __repr__(self):
        return self.__str__()

    def __call__(self, name, df):
        data = df.loc[df["name"] == f"{name}"]
        if self.inequality == "<=":
            return data[self.lhs] <= self.slope * data[self.rhs] + self.intercept
        elif self.inequality == ">=":
            return data[self.lhs] >= self.slope * data[self.rhs] + self.intercept
        else:
            return data[self.lhs] == self.slope * data[self.rhs] + self.intercept

    def __eq__(self, other):
        return self.__str__() == other.__str__()


class MultiLinearConclusion(Conclusion):
    """
    A class for multilinear graph conclusions.
    """
    def __init__(self, lhs, inequality, slopes, rhs, intercept):
        super().__init__(lhs, inequality, rhs, intercept)
        self.slopes = slopes

    def __str__(self):
        slope_terms = []
        for m, rhs in zip(self.slopes, self.rhs):
            if m == 1:
                slope_terms.append(f"{rhs}")
            elif m == -1:
                slope_terms.append(f"- {rhs}")
            elif m != 0:
                slope_terms.append(f"{m} * {rhs}")

        slope_str = " + ".join(slope_terms)

        if self.intercept > 0:
            result = f"{slope_str} + {self.intercept}"
        elif self.intercept < 0:
            result = f"{slope_str} - {abs(self.intercept)}"
        else:
            result = slope_str

        result = result.replace("+ -", "-").strip()
        return f"{self.lhs} {self.inequality} {result}"

    def __repr__(self):
        return self.__str__()

    def __call__(self, name, df):
        data = df.loc[df["name"] == f"{name}"]
        rhs_value = sum(m * data[r].values[0] for m, r in zip(self.slopes, self.rhs)) + self.intercept
        if self.inequality == "<=":
            return data[self.lhs].values[0] <= rhs_value
        elif self.inequality == ">=":
            return data[self.lhs].values[0] >= rhs_value
        else:
            data[self.lhs].values[0] == rhs_value

    def __eq__(self, other):
        return self.__str__() == other.__str__()

    def reversal(self):
        if self.inequality == "<=":
            return MultiLinearConclusion(self.lhs, ">=", self.slopes, self.rhs, self.intercept)
        elif self.inequality == ">=":
            return MultiLinearConclusion(self.lhs, "<=", self.slopes, self.rhs, self.intercept)

    def rhs_evaluate(self, x):
        return sum(m * x for m in self.slopes) + self.intercept


class LinearConjecture(Conjecture):
    """
    A class for linear graph conjectures.
    """
    def __repr__(self):
        hypothesis = f"If {self.symbol} is {self.hypothesis}"
        return f"{hypothesis}, then {self.conclusion}"

    def get_sharp_graphs(self, df):
        return df.loc[(df[self.hypothesis.statement] == True) &
                      (df[self.conclusion.lhs] == self.conclusion.slope * df[self.conclusion.rhs] + self.conclusion.intercept)]


class MultiLinearConjecture(Conjecture):
    """
    A class for multilinear graph conjectures.
    """
    def __repr__(self):
        hypothesis = f"If {self.symbol} is {self.hypothesis}"
        return f"{hypothesis}, then {self.conclusion}"

    def get_sharp_graphs(self, df):
        return df.loc[(df[self.hypothesis.statement] == True) &
                      (df[self.conclusion.lhs] == sum(self.conclusion.slopes[i] * df[self.conclusion.rhs[i]]
                                                      for i in range(len(self.conclusion.rhs))) + self.conclusion.intercept)]

    def __eq__(self, other):
        return self.hypothesis == other.hypothesis and self.conclusion == other.conclusion

    def false_graphs(self, df):
        if self.conclusion.inequality == "<=":
            return df.loc[(df[self.hypothesis.statement] == True) &
                          (df[self.conclusion.lhs] > sum(self.conclusion.slopes[i] * df[self.conclusion.rhs[i]]
                                                         for i in range(len(self.conclusion.rhs))) + self.conclusion.intercept)]
        else:
            return df.loc[(df[self.hypothesis.statement] == True) &
                          (df[self.conclusion.lhs] < sum(self.conclusion.slopes[i] * df[self.conclusion.rhs[i]]
                                                         for i in range(len(self.conclusion.rhs))) + self.conclusion.intercept)]



    def plot(self, df):
        import matplotlib.pyplot as plt
        import seaborn as sns
        sns.set_theme()

        if len(self.conclusion.slopes) == 1:
            # Filter dataframe where the hypothesis holds
            df = df[df[self.hypothesis.statement] == True]

            # Set up data for plotting
            y = df[self.conclusion.lhs]
            x = df[self.conclusion.rhs]
            rhs = self.conclusion.rhs_evaluate(x)

            # Create a figure and axis object
            fig, ax = plt.subplots(figsize=(10, 10))

            # Plot the data
            ax.set_title(f"{self.__repr__()}")
            ax.scatter(x, y, color='blue', label=f'Data')
            ax.plot(x, rhs, color='red', label=f'Prediction: {self.conclusion}')

            # Set labels and grid
            ax.set_xlabel(self.conclusion.rhs)
            ax.set_ylabel(self.conclusion.lhs)
            ax.grid(True)
            ax.legend()

            # Return the figure
            return fig
        else:
            print("Cannot plot multi-linear conjectures")
            return None


