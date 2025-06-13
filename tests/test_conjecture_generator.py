import subprocess
import sys
from pathlib import Path


def test_generator_emits_requested_number():
    script = Path(__file__).resolve().parents[1] / "utils" / "conjecture_generator.py"
    result = subprocess.run([sys.executable, str(script), "3"], capture_output=True, text=True)
    assert result.returncode == 0
    assert result.stdout.count("conjecture ") == 3
    assert "namespace AutoGraffiti" in result.stdout
