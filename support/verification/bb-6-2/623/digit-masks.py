"""Check the #623 grandparent sieve by enumerating all seven-trit words.

maxilism, November 24, 2026. CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
Run with Python 3.10 or later; no packages are required.
"""
from itertools import product

B, H = 243, 2187
powers = [3**i for i in range(7)]


def digit_table(cost):
    table = {
        sum(r*k for r, k in zip(word, powers)): sum(cost[r] for r in word)
        for word in product(cost, repeat=len(powers))
    }
    assert len(table) == H
    return table


def hit_masks(values, image):
    # At shift a, test values[i] in a+image. All other shifts give the empty mask.
    out = {0}
    for a in range(min(values)-max(image), max(values)-min(image)+1):
        out.add(sum(1 << i for i, v in enumerate(values) if v-a in image))
    return out


p = digit_table({-1: 2, 0: 0, 1: 1})
s = digit_table({0: 0, 1: 2, 2: 1})
P = {3*r + w for r, w in p.items()}
Q = {3*r - w for r, w in s.items()}
assert len(P) == len(Q) == H
minima = []
for c in range(4):
    offsets = [i for i in range(-(B//2), B//2+1) if (3*i+p[i]) % 4 == c]
    left = hit_masks([4*i+p[i]-1 for i in offsets], P)
    right = hit_masks([i+3 for i in offsets], Q)
    covered = max((a | b).bit_count() for a in left for b in right)
    minima.append(len(offsets)-covered)
    print(f'c={c}: eligible {len(offsets)}, maximum covered {covered}, minimum missed {minima[-1]}')
assert minima == [7, 9, 9, 5]
