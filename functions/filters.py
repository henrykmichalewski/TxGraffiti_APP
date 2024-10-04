from classes.conjecture import MultiLinearConclusion, Conjecture, MultiLinearConjecture, Hypothesis

__all__ = [
    "filter_by_inequalities",
    "filter_conjectures",
    "find_equalities",
    "remove_zero_slopes",
    "filter_false_conjectures",
    "make_more_general_conjectures",
]

def filter_false_conjectures(conjectures, df):
    new_conjectures = []
    for conj in conjectures:
        if conj.false_graphs(df).empty:
            new_conjectures.append(conj)
    return new_conjectures

def make_more_general_conjectures(conjectures, df):
    new_conjectures = []
    for conj in conjectures:
        hyp = Hypothesis("a connected graph")
        conclusion = conj.conclusion
        new_conj = MultiLinearConjecture(hyp, conclusion)
        if new_conj.false_graphs(df).empty:
            new_conjectures.append(new_conj)
        else:
            new_conjectures.append(conj)
    return new_conjectures

def filter_by_inequalities(conjectures, known_inequalities):
    new_conjectures = conjectures.copy()
    for conj in conjectures:
        if str(conj.conclusion) in known_inequalities:
            new_conjectures.remove(conj)

    return new_conjectures

def remove_zero_slopes(conjectures):
    new_conjectures = conjectures.copy()
    for conj in conjectures:
        if all(m == 0 for m in conj.conclusion.slopes):
            new_conjectures.remove(conj)

    return new_conjectures

def filter_conjectures(conjectures, known_conjectures):
    new_conjectures = conjectures.copy()
    for conj in conjectures:
        if any(str(conj) == other for other in known_conjectures):
            new_conjectures.remove(conj)

    return new_conjectures

def find_equalities(conjectures):
    equalities = []
    for conj in conjectures:
        for conj2 in conjectures:
            if conj.conclusion == conj2.conclusion.reversal and conj != conj2:
                hypothesis = conj2.hypothesis
                conclusion = MultiLinearConclusion(conj.conclusion.lhs, "=", conj.conclusion.slopes, conj.conclusion.rhs, conj.conclusion.intercept)
                equalities.append(Conjecture(hypothesis, conclusion))
    return equalities