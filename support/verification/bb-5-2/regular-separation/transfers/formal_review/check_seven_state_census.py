"""Audit the finite census underlying the 494-row ordinary separation lower bound.

The argument assumes the restoring-detour transfer theorem and the individual
shadow and zero-scan obstruction proofs. The verifier checks the literal
helper rules, induced shadows, row identities, and disjoint count.
"""

import argparse
from collections import defaultdict
import csv
from hashlib import sha256
from io import StringIO
from pathlib import Path


TOGGLE_PIN = "a8424934d85ffe31513b7585aabd3a15b8a31dfc0f12aaea008ed9bea9b40945"
SCAN_PIN = "242a60bf78c73cd68a256633555c7d97846c65eb51ff939f892881af896e271c"
WEIGHTED_PIN = "4f998d66d3a6b34bdb86176b6a5128ec6d8dd4168c981dae7ccfa0f567d89dba"

# These five Finned shadows and Skelet #17 have independent obstruction proofs.
FINNED3 = "1RB1RE_1LC1RB_0RA0LD_1LB1LD_---0RA"
OTHER_FINNED = (
    "1RB0LE_1RC1RB_1RD1LC_0LE0RB_---1LA",
    "1RB1RA_1RC1LB_0LD0RA_1RA1LE_---0LD",
    "1RB1LA_0LC0RE_---1LD_1RA0LC_1RA1RE",
    "1RB1LA_0LC0RE_---1LD_1LA0LC_1RA1RE",
)
SKELET17 = "1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA"

# Delimiter proofs cover the two Finned #3 and one E-root helix zero scans.
# Separate literal Lean proofs cover the last three zero scans.
PROVED_ZERO = {
    14424496: ("finned3", "1RB1RE_1LC1RB_0RA0LD_1LB1LD_---0RF_1RF1LG_0RA0LG"),
    15538865: ("finned3", "1RB1RG_1LC1RB_0RE0LD_1LB1LD_1RE1LF_0RA0LF_---0RE"),
    3192869: ("helix_e", "1RB0LD_1RC0RF_0RD0RB_1LE---_1LB0LC_1RF1LG_0RA0LG"),
    9932146: ("inverters", "1RB1LC_1LB1RA_0LG0LD_0RE1RD_1RE1LF_0RA0LF_---0LC"),
    9994819: ("inverters", "1RB1LC_1LC1RA_0LG0LD_0RE1RD_1RE1LF_0RA0LF_---0LC"),
    12767546: ("balanced", "1RB1RA_1LC1LB_0RD0LC_1RE---_0RF1LA_1RF1LG_0RA0LG"),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pinned(path, digest):
    data = path.read_bytes()
    require(sha256(data).hexdigest() == digest, f"pinned digest mismatch for {path}")
    return data.decode("ascii")


def reduce_table(table, pair, scan_bit):
    """Check the ordered helper pair and redirect its core calls to the return state."""
    states = "ABCDEFG"
    raw = dict(zip(states, table.split("_"), strict=True))
    e, f = pair
    core = [q for q in states if q not in pair]
    calls = {row[i:i+3] for q, row in raw.items() if q in core
             for i in (0, 3) if row[i+2] in pair}
    require(len(calls) == 1 and "A" in core, f"invalid callers in {table}")
    call, = calls
    a, d, called = call
    b = "1" if a == "0" else "0"
    back = "L" if d == "R" else "R"
    require(called == e, f"wrong entry state in {pair}")

    def rules(q):
        row = raw[q]
        pos = 3 * int(a)
        return row[pos:pos+3], row[3-pos:6-pos]

    ea, eb = rules(e)
    fa, fb = rules(f)
    if scan_bit is None:
        g = fb[2]
        good = (ea[1:] == eb[1:] == back+f and {ea[0], eb[0]} == {"0", "1"}
                and (fa, fb) == (b+d+e, a+d+g))
    else:
        g = fa[2]
        good = (scan_bit == a and (ea, eb, fa, fb) ==
                (b+d+e, b+back+f, a+d+g, a+back+f))
    require(good and g in core, f"helper rule mismatch for {pair} in {table}")
    names = dict(zip(core, "ABCDE", strict=True))

    def shadow_action(action):
        if action == "---":
            return action
        target = g if action == call else action[2]
        return action[:2] + names[target]

    return "_".join(shadow_action(raw[q][:3]) + shadow_action(raw[q][3:]) for q in core)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("toggle_tsv", "scan_tsv", "weighted_archive"):
        parser.add_argument(name, type=Path)
    args = parser.parse_args()
    weighted = pinned(args.weighted_archive, WEIGHTED_PIN).splitlines()[::6]
    # Order in this pinned archive: 12 balanced, 2 inverters, and A/B/E helices.
    families = dict(zip(weighted, ["balanced"]*12 + ["inverters"]*2 +
                        ["helix_a", "helix_b", "helix_e"], strict=True))
    families.update({sh: "other_finned" for sh in OTHER_FINNED})
    families.update({FINNED3: "finned3", SKELET17: "skelet17"})
    modes = defaultdict(lambda: defaultdict(set))
    tables = {}
    for kind, path, digest in (("toggle", args.toggle_tsv, TOGGLE_PIN),
                               ("scan", args.scan_tsv, SCAN_PIN)):
        for row in csv.DictReader(StringIO(pinned(path, digest)), delimiter="\t"):
            number, table = int(row["row_15743264"]), row["seven_state_table"]
            require(number not in tables, f"row {number} occurs twice")
            tables[number] = table
            if kind == "toggle":
                choices = [(row["helper_pair"], None, row["five_state_shadow"])]
            else:
                choices = [(pair, bit, shadow) for helper, shadow in
                           zip(row["helper_pairs_and_scanned_bits"].split(","),
                               row["five_state_shadows_in_pair_order"].split(","), strict=True)
                           for pair, bit in [helper.split(":")]]
            for pair, bit, shadow in choices:
                require(reduce_table(table, pair, bit) == shadow, f"wrong shadow at row {number}")
                modes[families.get(shadow, "other")][bit or "toggle"].add(number)

    require(len(set(tables.values())) == len(tables) == 721, "census size mismatch")
    total = {f: rows["toggle"] | rows["1"] for f, rows in modes.items()}
    zero = defaultdict(set)
    for number, (family, table) in PROVED_ZERO.items():
        require(tables[number] == table and number in modes[family]["0"] - total[family],
                f"individual zero-scan proof mismatch at row {number}")
        zero[family].add(number)
    parts = [
        ("Finned #3 and Skelet #17", total["finned3"] | zero["finned3"] | total["skelet17"], 49),
        ("B- and E-root helices", total["helix_b"] | total["helix_e"] | zero["helix_e"], 41),
        ("Counter-balanced total-return rows", total["balanced"], 262),
        ("Counter-inverter total-return rows", total["inverters"], 41),
        ("Other Finned total-return rows", total["other_finned"], 98),
        ("Individually proved balanced and inverter zero scans", zero["balanced"] | zero["inverters"], 3),
    ]
    counted = set()
    for name, rows, expected in parts:
        require(len(rows) == expected and counted.isdisjoint(rows), f"inconsistent count for {name}")
        counted.update(rows)
        print(f"{len(rows):3}  {name}")
    mixed = modes["balanced"]["0"] & modes["balanced"]["1"]
    require(len(mixed) == 12, "dual scan decompositions mismatch")
    print(f"{len(mixed)} counter-balanced rows have both scan bits and are counted once.")
    print(f"Conditional on the cited transfer and obstruction proofs: {len(counted)} of {len(tables)} rows.")


if __name__ == "__main__":
    main()
