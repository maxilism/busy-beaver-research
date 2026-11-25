"""Match the seventeen Lean machine tables to the six-line MITMWFAR records.

Source: Iijil1/MITMWFAR at 3937731f9e1d801d6f6d77cf44787f93fc1ffc76,
SolvedFullCerts.txt. Each record starts with its machine's ten instructions.
"""

import argparse
from hashlib import sha256
from pathlib import Path
import subprocess


HERE = Path(__file__).resolve().parent
DIGEST = "4f998d66d3a6b34bdb86176b6a5128ec6d8dd4168c981dae7ccfa0f567d89dba"

INSPECT = """
import ReviewedCases
open ReviewedCases

private def helixCode (tm : Helix.St → Bool → Option (Bool × Helix.Dir × Helix.St)) : String :=
  let letter : Helix.St → Char
    | .A => 'A' | .B => 'B' | .C => 'C' | .D => 'D' | .E => 'E'
  let action (q : Helix.St) (x : Bool) :=
    match tm q x with
    | none => "---"
    | some (w, d, p) => String.ofList [if w then '1' else '0',
        (match d with | .L => 'L' | .R => 'R'), letter p]
  String.intercalate "_" ([Helix.St.A, .B, .C, .D, .E].map
    (fun q => action q false ++ action q true))

private def table : Option OrdinaryCase → String
  | none => helixCode Helix.instruction
  | some (.inverter v) => helixCode (Inverter.instruction v)
  | some (.sibling v) => SiblingCatalog.catalogCode v
  -- catalogInstruction parses this string; catalog_roundtrip checks the inverse.
  | some (.balanced v d) => BalancedCatalog.code v d

#eval do
  for i in indices do
    IO.println s!"{catalogId i} {table i}"
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path, help="pinned SolvedFullCerts.txt")
    args = parser.parse_args()
    data = args.archive.read_bytes()
    if sha256(data).hexdigest() != DIGEST:
        raise SystemExit("SHA-256 mismatch for the published certificate archive")
    lines = data.decode("ascii").splitlines()
    if len(lines) != 6 * 17:
        raise SystemExit("expected seventeen six-line records")
    expected = lines[::6]

    subprocess.run(["lake", "build", "+ReviewedCases"], cwd=HERE, check=True)
    result = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=HERE,
                            input=INSPECT, text=True, capture_output=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    rows = [line.split() for line in result.stdout.splitlines()]
    if len(rows) != 17 or len({machine for machine, _ in rows}) != 17:
        raise SystemExit("Lean did not enumerate seventeen distinct catalog IDs")
    if sorted(table for _, table in rows) != sorted(expected) or len(set(expected)) != 17:
        raise SystemExit("the literal machine tables differ between Lean and the archive")
    ids = {table: machine for machine, table in rows}
    for record, table in enumerate(expected, start=1):
        print(f"Record {record:2d}  {('#' + ids[table]):>9}  {table}")
    print(f"All 17 literal tables match the pinned archive. SHA-256 {DIGEST}")


if __name__ == "__main__":
    main()
