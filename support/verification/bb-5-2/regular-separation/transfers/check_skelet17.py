"""Replay the two smallest audited Skelet #17 checkpoint pairs on its literal table."""

TABLE = "1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA"
RULES = {
    (state, bit): row[3 * bit:3 * bit + 3]
    for state, row in zip("ABCDE", TABLE.split("_"), strict=True)
    for bit in (0, 1)
}


def checkpoint(k):
    """Xu's Zero(E'') in section 4, in savask's left-to-right tuple notation."""
    middle = (3 * 2**i - 2 * (i % 2) for i in range(1, 2 * k + 1))
    return (0, 0, 3, *middle, 2**(2 * k + 1) - 5)


def tape_for(blocks):
    word = "1".join("10" * n for n in blocks)
    # B faces right and scans the blank just after the last block.
    return {i - len(word) for i, bit in enumerate(word) if bit == "1"}


def simulate(initial_ones, state, expected_steps, target=None):
    ones = set(initial_ones)
    head = 0
    for step in range(expected_steps + 1):
        if state == "B" and target is not None and len(ones) == len(target):
            if all(head + offset in ones for offset in target):
                if step != expected_steps:
                    raise ValueError(f"checkpoint first reached at {step}")
                return
        rule = RULES[state, int(head in ones)]
        if rule == "---":
            if target is not None or step != expected_steps:
                raise ValueError(f"unexpected halt after {step} defined steps")
            return
        bit, direction, state = rule
        if bit == "1":
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction == "R" else -1
    raise ValueError("expected endpoint was not reached")


if __name__ == "__main__":
    for k, arrival, halting_time in [(1, 5558, 985), (2, 576105, 18219)]:
        diagonal = checkpoint(k)
        larger = checkpoint(k + 1)[-1]
        simulate(set(), "A", arrival, tape_for(diagonal))
        hybrid = (*diagonal[:-1], larger)
        simulate(tape_for(hybrid), "B", halting_time)
        print(f"k={k}, diagonal reached at {arrival:,}. Replacing {diagonal[-1]} "
              f"by {larger} halts after {halting_time:,} defined steps.")
