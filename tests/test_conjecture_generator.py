import subprocess
import sys
from pathlib import Path


def test_generator_emits_requested_number():
    script = Path(__file__).resolve().parents[1] / "utils" / "conjecture_generator.py"
    result = subprocess.run([sys.executable, str(script), "--limit", "3"], capture_output=True, text=True)
    assert result.returncode == 0
    # Check that we get the namespace and the right number of conjecture blocks (comment + signature)
    assert "namespace AutoGraffiti" in result.stdout
    assert result.stdout.count("/- Conjecture") == 3
    assert result.stdout.count("conjecture ") == 3


def run_conjecture_generator(args, expected_output):
    script = Path(__file__).resolve().parents[1] / "utils" / "conjecture_generator.py"
    cmd = [sys.executable, str(script)] + args
    result = subprocess.run(cmd, capture_output=True, text=True)
    assert result.returncode == 0
    # Filter for lines starting with "/-" or "conjecture"
    output_lines = result.stdout.strip().split('\n')
    conjecture_lines = [line for line in output_lines if line.startswith("conjecture") or line.startswith("/-")]
    actual_output = "\n".join(conjecture_lines)
    assert actual_output == expected_output.strip()

def test_wowii_gt_a1():
    args = [
        "--lhs", "gamma_t",
        "--rhs", "annihilation_number",
        "--k", "1:1",
        "--c", "1:1",
        "--limit", "1"
    ]
    expected_output = """
/- Conjecture 1: For every finite simple graph G, gamma t(G) ≤ 1 * annihilation number(G) + 1. -/
conjecture gamma_t_le_1_annihilation_number_plus_1 (G : SimpleGraph V) [Fintype V] :
""".strip()
    run_conjecture_generator(args, expected_output)

def test_wowii_g2_a1():
    args = [
        "--lhs", "gamma_2",
        "--rhs", "annihilation_number",
        "--k", "1:1",
        "--c", "1:1",
        "--limit", "1"
    ]
    expected_output = """
/- Conjecture 1: For every finite simple graph G, gamma 2(G) ≤ 1 * annihilation number(G) + 1. -/
conjecture gamma_2_le_1_annihilation_number_plus_1 (G : SimpleGraph V) [Fintype V] :
""".strip()
    run_conjecture_generator(args, expected_output)

def test_wowii_r_alpha():
    args = [
        "--lhs", "randic_index",
        "--rhs", "independence_number",
        "--k", "1:1",
        "--c", "0:0",
        "--limit", "1"
    ]
    expected_output = """
/- Conjecture 1: For every finite simple graph G, randic index(G) ≤ 1 * independence number(G) + 0. -/
conjecture randic_index_le_1_independence_number (G : SimpleGraph V) [Fintype V] :
""".strip()
    run_conjecture_generator(args, expected_output)

def test_wowii_r_small_alpha():
    args = [
        "--lhs", "radius",
        "--rhs", "independence_number",
        "--k", "1:1",
        "--c", "0:0",
        "--limit", "1"
    ]
    expected_output = """
/- Conjecture 1: For every finite simple graph G, radius(G) ≤ 1 * independence number(G) + 0. -/
conjecture radius_le_1_independence_number (G : SimpleGraph V) [Fintype V] :
""".strip()
    run_conjecture_generator(args, expected_output)

def test_wowii_dbar_alpha():
    args = [
        "--lhs", "average_distance",
        "--rhs", "independence_number",
        "--k", "1:1",
        "--c", "0:0",
        "--limit", "1"
    ]
    expected_output = """
/- Conjecture 1: For every finite simple graph G, average distance(G) ≤ 1 * independence number(G) + 0. -/
conjecture average_distance_le_1_independence_number (G : SimpleGraph V) [Fintype V] :
""".strip()
    run_conjecture_generator(args, expected_output)

def test_wowii_zf_alpha1():
    args = [
        "--lhs", "zero_forcing_number",
        "--rhs", "independence_number",
        "--k", "1:1",
        "--c", "1:1",
        "--limit", "1"
    ]
    expected_output = """
/- Conjecture 1: For every finite simple graph G, zero forcing number(G) ≤ 1 * independence number(G) + 1. -/
conjecture zero_forcing_number_le_1_independence_number_plus_1 (G : SimpleGraph V) [Fintype V] :
""".strip()
    run_conjecture_generator(args, expected_output)
