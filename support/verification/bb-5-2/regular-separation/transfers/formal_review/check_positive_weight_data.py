"""Reconstruct the Lean reader and guard tables from the pinned WFAR record."""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path

DIRECTORY = Path(__file__).resolve().parent
RECORD = DIRECTORY.parents[1] / 'lower-bound' / 'cert-4817065.txt'
TARGET = DIRECTORY / 'PositiveWeightData.lean'
PIN = '5092986314c8bfe602183acd112ca5236114d968beb685cedabee4ff835550f9'


def vector(entries, per_line):
    rows = [', '.join(entries[i:i + per_line]) for i in range(0, len(entries), per_line)]
    return '#v[\n    ' + ',\n    '.join(rows) + ']'


def bit_mask(indices):
    return sum(1 << i for i in set(indices))


def source():
    record = RECORD.read_bytes()
    if sha256(record).hexdigest() != PIN:
        raise ValueError('the six-line WFAR certificate differs from its pinned bytes')
    tm, left, right, sign_left, sign_right, guards = record.decode('ascii').splitlines()
    if tm != '1RB0RC_1LC0LE_0LD0LB_1RA---_1LB0RD':
        raise ValueError('wrong machine table')
    out = ['''import Helix.Machine

/-! Published WFAR data for #4817065. Each table entry gives the next reader
state and signed charge when reading one unscanned bit toward the head.
For each head symbol and left endpoint, a pair of bit masks encodes the right
endpoints with a guard and those whose guard requires total charge one.
The other present guards require zero. The six-line certificate SHA-256 is
`''' + PIN + '''`.
Run `python3 -IB check_positive_weight_data.py` to compare with the record. -/
namespace PositiveWeight
open Helix
''']
    for side, n, trans, sign in [('L', 58, left, sign_left), ('R', 37, right, sign_right)]:
        rows = []
        for row in trans.split('_'):
            a, b = [tuple(map(int, edge.split(','))) for edge in row.split(';')]
            rows.append(f'(({a[0]}, {a[1]}), ({b[0]}, {b[1]}))')
        if len(rows) != n:
            raise ValueError('wrong number of reader states')
        out.append(f'private def rows{side} : Vector ((Fin {n} × Int) × (Fin {n} × Int)) {n} :=\n  '
                   + vector(rows, 3) + '\n')
        out.append(f'def edge{side} (i : Fin {n}) (b : Bool) : Fin {n} × Int :=\n'
                   + f'  let row := rows{side}[i]\n  if b then row.2 else row.1\n')
        for label, listed in zip(['nonneg', 'nonpos'], sign.split('_'), strict=True):
            mask = bit_mask(map(int, listed.split(',')))
            out.append(f'def {label}{side} (i : Fin {n}) : Bool := Nat.testBit {mask} i.val\n')

    masks = {(q, x): [[0, 0] for _ in range(58)] for q in 'ABCDE' for x in (0, 1)}
    for rule in guards.split('_'):
        q, xs, ls, rs, lo, hi = rule.split(',')
        x, l, r, val = map(int, (xs, ls, rs, lo))
        if not (lo == hi and val in (0, 1) and 0 <= r < 37 and 0 <= l < 58):
            raise ValueError('unexpected guard at ' + rule)
        entry = masks[q, x][l]
        if entry[0] & (1 << r):
            raise ValueError('duplicate guard at ' + rule)
        entry[0] |= 1 << r
        entry[1] |= val << r
    out.append('private def guardMasks : St → Bool → Vector (Nat × Nat) 58')
    for (q, x), rows in masks.items():
        bits = 'true' if x else 'false'
        out.append(f'  | .{q}, {bits} => ' + vector([f'({a}, {b})' for a, b in rows], 6))
    out.append('''
def guard (q : St) (b : Bool) (l : Fin 58) (r : Fin 37) : Option Int :=
  let masks := (guardMasks q b)[l]
  if masks.1.testBit r.val then
    some (if masks.2.testBit r.val then 1 else 0)
  else none

end PositiveWeight''')
    return '\n'.join(out) + '\n'


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='regenerate PositiveWeightData.lean')
    args = parser.parse_args()
    content = source()
    if args.write:
        TARGET.write_text(content)
    elif TARGET.read_text() != content:
        raise SystemExit('PositiveWeightData.lean differs from the published certificate')
    else:
        print('58 left and 37 right reader states, sign sets, and 163 singleton guards match.')
