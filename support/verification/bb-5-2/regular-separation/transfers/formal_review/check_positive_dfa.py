"""Compare Lean's compiled DFA for #4817065 with the published partial table."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess


HERE = Path(__file__).resolve().parent
PUBLISHED = HERE / "../../../../../../github/support/verification/bb-5-2/cubic-helix/dfa.json"
DIGEST = "123cdce7aaa1a27daa78cd2ee04c8c02de3dafe5043f4c2eef766a7fdd938b4d"

# Enumerate the actual Lean functions. No source-code parsing or shared table generator.
INSPECT = """
import PositiveDFA
import Lean.Data.Json.FromToJson.Basic
open PositiveDFA
#eval do
  let alphabet : List Helix.Sym := [.bit false, .bit true, .mark .A, .mark .B,
                                     .mark .C, .mark .D, .mark .E]
  let states := List.finRange 177
  let edges := states.map fun s => alphabet.map fun a => (move s a).val
  let accepting := (states.filter final).map Fin.val
  IO.println (Lean.toJson (start.val, sink.val, accepting, edges)).compress
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("json", type=Path, default=PUBLISHED, nargs="?")
    args = parser.parse_args()
    data = args.json.read_bytes()
    if sha256(data).hexdigest() != DIGEST:
        raise ValueError("Published JSON SHA-256 mismatch")
    dfa = json.loads(data)
    if dfa["alphabet"] != "01ABCDE" or dfa["missing"] != -1 or len(dfa["delta"]) != 176:
        raise ValueError("Unexpected published DFA format")
    subprocess.run(["lake", "build", "+PositiveDFA"], cwd=HERE, check=True)
    result = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=HERE, input=INSPECT,
                            text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    initial, rest = json.loads(result.stdout)
    sink, rest = rest
    accepting, edges = rest
    count = len(dfa["delta"])
    expected = [[count if t == -1 else t for t in row] for row in dfa["delta"]]
    expected.append([count] * len(dfa["alphabet"]))
    if (initial, sink, accepting, edges) != (dfa["initial"], count, dfa["final"], expected):
        raise ValueError("Lean transition function, initial state, sink, or finals differ")
    print(f"Verified {count} explicit states, all {count * 7} published transitions, "
          f"{len(accepting)} finals and the totalizing sink. SHA-256 {DIGEST}")


if __name__ == "__main__":
    main()
