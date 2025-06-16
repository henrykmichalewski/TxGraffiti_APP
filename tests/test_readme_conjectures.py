import pathlib

def test_readme_contains_sample_conjectures():
    text = pathlib.Path('README.md').read_text()
    assert "Conjecture 21" in text
    assert "CEIL(2dist_avg(B,V))" in text
    assert "Conjecture 22" in text
    assert "CEIL(2dist(B,V)))" in text
    assert "Conjecture 23" in text
    assert "dist_avg(M)/2" in text
    assert "Conjecture 74" in text
    assert "CEIL(2dist_avg(B,V))" in text
    assert "Conjecture 105" in text
    assert "tree(G)*SQRT[domination(G)]" in text
    assert "Conjecture 214" in text
    assert "3*g_2 (G¯)" in text
    assert "Conjecture 429" in text
    assert "D_avg(P)*(α(G[N(M)]) + 1)" in text
