"""Check the first level of BB(6) machine 66813. Python 3, no dependencies.

DigitMap.lean: level_start gives x = 22 and 6801 remaining words on
level 1; fd, dK and dCost give the update and its cost.  See the accompanying note on machine 66813.
"""
from math import gcd


def check_first_level():
    offset = (15, 27, 47, 35, 36)
    cost = (4, 5, 8, 3, 2)
    x, budget = 22, 6801
    previous_product = 1
    terms = 0
    while True:
        # Remove all prime factors of x that divide an earlier term, without
        # factoring x. Taking the remainder once makes the gcds small.
        r = previous_product % x
        fresh = x
        while (g := gcd(fresh, r)) > 1:
            fresh //= g
        if fresh == 1:
            raise ValueError(f"no new prime factor at index {terms}")
        previous_product *= x
        terms += 1
        a, d = divmod(x, 10)
        j = d // 2
        if budget < cost[j]:
            break
        budget -= cost[j]
        x = 31 * a + offset[j]
    if (terms, budget, j) != (1567, 0, 3):
        raise ValueError(f"unexpected endpoint: {(terms, budget, j)}")
    return terms, budget


if __name__ == "__main__":
    terms, budget = check_first_level()
    print(f"{terms-1} updates; {terms} terms each introduce a prime; "
          f"{budget} words left.")
