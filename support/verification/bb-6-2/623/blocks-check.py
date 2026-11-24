"""Check the #623 grandparent sieve using arithmetic digit costs and omission masks.

maxilism, November 24, 2026. CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
Run with Python 3.10 or later; no packages are required.
"""


def p(v):  # balanced remainder r-1 has cost (r-1) mod 3, even for negative v
    total = 0
    while v:
        v, r = divmod(v+1, 3)
        total += (r-1) % 3
    return total


def s(v):
    total = 0
    while v:
        v, r = divmod(v, 3)
        total += (0, 2, 1)[r]
    return total


def masks(image, values):
    out = {0}
    for shift in range(min(image)-max(values), max(image)-min(values)+1):
        out.add(sum((v+shift in image) << i for i, v in enumerate(values)))
    return out


B, H = 243, 2187
rs = range(-(B//2), B//2+1)
P = {3*r+p(r) for r in range(-(H//2), H//2+1)}
Q = {3*r-s(r) for r in range(H)}
left = masks(P, [4*r+p(r)-1 for r in rs])
right = masks(Q, [r+3 for r in rs])
minima = []
for alpha in range(4):  # alpha = c+1 mod 4 in the paper's notation
    eligible = sum((((3*r+p(r)+1) % 4 == alpha) << i) for i, r in enumerate(rs))
    not_left = {eligible & ~m for m in left}
    not_right = {eligible & ~m for m in right}
    minima.append(min((a & b).bit_count() for a in not_left for b in not_right))
print('Minimum missed, in order alpha=0,1,2,3:', minima)
assert minima == [5, 7, 9, 9]
