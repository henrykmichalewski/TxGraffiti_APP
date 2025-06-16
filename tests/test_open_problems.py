import subprocess
import sys
from pathlib import Path
import pytest

SCRIPT = Path(__file__).resolve().parents[1] / "utils" / "conjecture_generator.py"


def run_generator(lhs: str, k: int, rhs: str, c: int) -> str:
    args = [
        sys.executable, str(SCRIPT),
        "--lhs", lhs,
        "--rhs", rhs,
        "--k", f"{k}:{k}",
        "--c", f"{c}:{c}",
        "--limit", "1",
    ]
    result = subprocess.run(args, capture_output=True, text=True)
    assert result.returncode == 0
    lines = [ln for ln in result.stdout.splitlines() if ln.startswith("/-") or ln.startswith("conjecture")]
    return "\n".join(lines)


def expected_block(lhs: str, k: int, rhs: str, c: int) -> str:
    comment = f"/- Conjecture 1: For every finite simple graph G, {lhs.replace('_',' ')}(G) ≤ {k} * {rhs.replace('_',' ')}(G) + {c}. -/"
    ident = f"{lhs}_le_{k}_{rhs}" + ("" if c == 0 else f"_plus_{c}")
    conj = f"conjecture {ident} (G : SimpleGraph V) [Fintype V] :"
    return f"{comment}\n{conj}"

open_problems = [
    ("independence_number",1,"vertex_cover_number",1),
    ("chromatic_number",1,"vertex_cover_number",1),
    ("matching_number",1,"vertex_cover_number",1),
    ("clique_number",1,"chromatic_number",1),
    ("vertex_cover_number",2,"matching_number",0),
    ("min_edge_cover",1,"vertex_cover_number",1),
    ("diameter",2,"triameter",0),
    ("randic_index",1,"independence_number",1),
    ("harmonic_index",1,"independence_number",2),
    ("sum_connectivity_index",1,"independence_number",3),
    ("residue",1,"independence_number",0),
    ("annihilation_number",2,"independence_number",0),
    ("sub_total_domination_number",1,"independence_number",2),
    ("slater",1,"independence_number",1),
    ("wiener_index",2,"independence_number",3),
    ("independence_number",1,"annihilation_number",1),
    ("chromatic_number",1,"clique_number",1),
    ("matching_number",1,"min_edge_cover",1),
    ("triameter",3,"radius",0),
    ("randic_index",1,"wiener_index",1),
    ("harmonic_index",1,"wiener_index",2),
    ("sum_connectivity_index",1,"wiener_index",2),
    ("residue",1,"wiener_index",0),
    ("annihilation_number",1,"wiener_index",3),
    ("independence_number",1,"wiener_index",2),
]

@pytest.mark.parametrize("lhs,k,rhs,c", open_problems)
def test_open_problem_generation(lhs: str, k: int, rhs: str, c: int) -> None:
    assert run_generator(lhs, k, rhs, c) == expected_block(lhs, k, rhs, c)
