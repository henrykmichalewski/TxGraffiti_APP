import os
import sys
from fractions import Fraction

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from classes.conjecture import Hypothesis, MultiLinearConclusion, MultiLinearConjecture

import importlib.util
import types

spec = importlib.util.spec_from_file_location(
    'formating', os.path.join(os.path.dirname(__file__), '..', 'functions', 'formating.py')
)
formating = importlib.util.module_from_spec(spec)
sys.modules['streamlit'] = types.SimpleNamespace()
spec.loader.exec_module(formating)
conjecture_to_lean = formating.conjecture_to_lean


def test_conjecture_to_lean():
    hyp = Hypothesis("a connected graph")
    concl = MultiLinearConclusion("order", "<=", [Fraction(1)], ["order"], Fraction(0))
    conj = MultiLinearConjecture(hyp, concl)
    lean = conjecture_to_lean(conj)
    assert "SimpleGraph" in lean
    assert "≤" in lean
