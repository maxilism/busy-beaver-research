#!/usr/bin/env python3
"""Compile the right halves of the 17 published BB(5) weighted certificates.

Pass SolvedFullCerts.txt from Iijil1/MITMWFAR commit
3937731f9e1d801d6f6d77cf44787f93fc1ffc76. --machine selects one or more
bbchallenge IDs. The original verifier establishes that its guards are safe.
This check establishes that the same guards can be tested in one forward pass.
"""

import argparse
import hashlib
from collections import defaultdict, deque
from itertools import product
from pathlib import Path

DIGEST = '4f998d66d3a6b34bdb86176b6a5128ec6d8dd4168c981dae7ccfa0f567d89dba'
# Literal file order. These are counts of distinct normalized maps across all
# contexts of each record, not counts of states in a minimized acceptor.
EXPECTED_MAPS = {
    523280: 8, 321080: 8, 320969: 8, 472097: 8, 8210683: 8, 8210684: 8,
    8210685: 8, 10818491: 8, 8226493: 8, 572659: 8, 10818510: 15,
    1465912: 17, 12781955: 15, 12699987: 36, 4817065: 606,
    5377178: 881, 7138511: 1626,
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_automaton(line):
    return [tuple(tuple(map(int, edge.split(','))) for edge in row.split(';'))
            for row in line.split('_')]


def advance(right, summary, bit):
    # Appending an input bit prepends it to the word the original WFA reads.
    entries = []
    for row in right:
        dest, weight = row[bit]
        old = summary[dest]
        entries.append(None if old is None else (old[0], weight + old[1]))
    gain = min((entry[1] for entry in entries if entry is not None), default=0)
    normalized = tuple(None if e is None else (e[0], e[1] - gain) for e in entries)
    return normalized, gain


def raw_run(right, state, word):
    total = 0
    for bit in word:
        state, delta = right[state][bit]
        total += delta
    return state, total


def check_samples(right, seeds, transitions):
    # An independent raw scan checks orientation, endpoint and accumulated
    # absolute weight. Exhaustive closure below supplies the all-words result.
    for length in range(5):
        for bits in product((0, 1), repeat=length):
            actual = [raw_run(right, q, reversed(bits)) for q in range(len(right))]
            for seed in seeds:
                current, offset = seed, 0
                for bit in bits:
                    current, gain = transitions[current, bit]
                    offset += gain
                for q, (end, weight) in enumerate(actual):
                    expected = None if seed[end] is None else (end, weight - offset)
                    require(current[q] == expected, 'suffix direction or weight mismatch')


def verify(machine, record):
    tm, left_code, right_code, _, _, guard_code = record
    left, right = map(read_automaton, (left_code, right_code))
    require(left[0][0] == right[0][0] == (0, 0), 'exterior zero changes a start')
    left_weights = [weight for row in left for _, weight in row]
    right_weights = [weight for row in right for _, weight in row]
    sign = -1 if machine == 4817065 else 1
    require(all(sign*w >= 0 for w in left_weights) and all(sign*w <= 0 for w in right_weights),
            f'{machine}: raw weights violate the one-turn sign condition')
    targets = defaultdict(set)
    for guard in guard_code.split('_'):
        state, bit, left_end, right_end, low, high = guard.split(',')
        targets[state, int(bit), int(left_end)].add(int(right_end))
    seeds = {tuple((q, 0) if q in ends else None for q in range(len(right)))
             for ends in targets.values()}
    # A missing context always rejects. Keep the original context in finite
    # control for the exact guard lookup at the end, even when maps coincide.
    pending = deque(seeds)
    seen = set(seeds)
    transitions = {}
    max_spread = 0
    while pending:
        summary = pending.popleft()
        for bit in (0, 1):
            new, gain = advance(right, summary, bit)
            transitions[summary, bit] = new, gain
            spread = max((e[1] for e in new if e is not None), default=0)
            max_spread = max(spread, max_spread)
            require(spread <= 1 and abs(gain) <= 1, 'unexpected normalized weight')
            if new not in seen:
                seen.add(new)
                require(len(seen) <= EXPECTED_MAPS[machine], 'unexpected new map')
                pending.append(new)
    require(len(seen) == EXPECTED_MAPS[machine], 'wrong closure size')
    check_samples(right, seeds, transitions)
    print(f'{machine}: {len(targets)} nonempty guard contexts, {len(seeds)} masks, '
          f'{len(seen)} maps, maximum spread {max_spread}. Raw L/R weight ranges '
          f'[{min(left_weights)},{max(left_weights)}]/[{min(right_weights)},{max(right_weights)}].')

    # If the head-specific mask is omitted, these two records have unbounded
    # relative weights even on (000)^j. Both terminal states occur in guards.
    if machine in (5377178, 7138511):
        q = 4 if machine == 5377178 else 7
        all_targets = set.union(*targets.values())
        require({0, q} <= all_targets, 'cycle targets must be live')
        require(raw_run(right, 0, (0, 0, 0)) == (0, 0), 'wrong zero cycle at 0')
        require(raw_run(right, q, (0, 0, 0)) == (q, -1), 'wrong second cycle')
        print(f'  Unconditioned starts 0 and {q} return on 000 with weights 0 and -1.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate_file', type=Path)
    parser.add_argument('--machine', type=int, nargs='+', choices=EXPECTED_MAPS)
    args = parser.parse_args()
    blob = args.certificate_file.read_bytes()
    require(hashlib.sha256(blob).hexdigest() == DIGEST, 'certificate SHA-256 mismatch')
    lines = blob.decode('ascii').splitlines()
    require(len(lines) == 6 * len(EXPECTED_MAPS), 'unexpected record count')
    for index, machine in enumerate(EXPECTED_MAPS):
        if args.machine is None or machine in args.machine:
            verify(machine, lines[6*index:6*index+6])


if __name__ == '__main__':
    main()
