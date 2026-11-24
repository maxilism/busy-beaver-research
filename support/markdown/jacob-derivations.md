# Sweep times and finite checks for Jacobzheng’s machine

maxilism

24 November 2026

## Checkpoint sweep

[Jacobzheng’s original account](https://wiki.bbchallenge.org/w/index.php?title=Cryptids&diff=9600&oldid=9597) gives the parity recurrence from blank. Here is the tape calculation behind it. The [seven-state table](https://wiki.bbchallenge.org/wiki/BB(7)#Cryptids), with instructions for reads `0,1` in each state from `A` to `G`, is

```
1LG0LD_1RE1RA_1RB1RC_1RC1LD_---0LF_1LC1LF_1LF1LE
```

Write $C(n,m)=[\mathrm C0]1^n0\,1^m$ with blanks elsewhere. The bracket marks the scanned cell, $n,m\ge0$, and time counts defined transitions. From blank, `A0,G0,F0` reach $C(3,0)$ in three steps.

If two ones remain to the right, start at $1^l[\mathrm C0]11Y$. The three transitions `C0,B1,A1` leave $1^{l+2}0Y$ with `D` on the rightmost 1. `D` scans the $l+2$ ones leftward. `D0` adds one on the left and sends `C` back across those $l+2$ ones. The result is $1^{l+3}[\mathrm C0]Y$. This takes $2l+8$ steps. Starting with $l=0$, consuming $k$ pairs therefore costs $\sum_{i=0}^{k-1}(6i+8)=3k^2+5k$ and leaves $l=3k$.

* On odd input $n=2k+1$, the remainder is $1^l[\mathrm C0]1\,0\,1^m$. The five transitions `C0,B1,A0,G1,E1` fill the right delimiter and erase the cell where `C0` began. `F` crosses the $l$ left ones and `F0` adds one, placing the head at $C(l+1,m+2)$. Exit cost: $l+6$.
* On even input $n=2k$, the remainder is $1^l[\mathrm C0]0\,1^m$. `C0,B0` fill two ones and leave `E` scanning the first reserve cell. With $m=0$ the machine now faces its undefined `E0` instruction. With $m>0$, `E1` erases that reserve one. `F` crosses $l+2$ ones and `F0` adds one, producing $C(l+3,m-1)$. The exit costs 2 steps or $l+6$, respectively.

| Start | Result | Defined transitions |
|---|---|---:|
| $C(2k+1,m)$ | $C(3k+1,m+2)$ | $3k^2+8k+6$ |
| $C(2k,m)$, $m>0$ | $C(3k+3,m-1)$ | $3k^2+8k+6$ |
| $C(2k,0)$ | `E0` | $3k^2+5k+2$ |

With $y=n-1$ the size update on completed sweeps is $T(2k)=3k$, $T(2k+1)=3k+5$. It earns two reserve units on an even $y$ and spends one on an odd $y$. Continuing $T$ through an overdraft defines an arithmetic orbit only. The [literal-table checker](../verification/bb-7-2/jacobzheng/second-check.py) tests the transitions and clocks on finite examples, including the `E0` case.

## Neighbor counts

Keep `E0` undefined and replace exactly one of the other 13 entries by a *different* defined instruction. There are $2\cdot2\cdot7-1=27$ choices at each entry. **First read** is the time, in defined transitions on the original blank run, just *before* the entry is executed. Every modification shares this prefix. The third outcome column counts edits proved to halt if and only if the original does.

| Entry | First read | Halt | Run forever | Equivalent to original |
|---|---:|---:|---:|---:|
| `A0` | 0 | 22 | 5 | 0 |
| `A1` | 5 | 11 | 16 | 0 |
| `B0` | 43 | 1 | 26 | 0 |
| `B1` | 4 | 17 | 10 | 0 |
| `C0` | 3 | 5 | 22 | 0 |
| `C1` | 9 | 8 | 19 | 0 |
| `D0` | 8 | 5 | 22 | 0 |
| `D1` | 6 | 13 | 14 | 0 |
| `E1` | 15 | 23 | 4 | 0 |
| `F0` | 2 | 13 | 13 | 1 |
| `F1` | 16 | 19 | 8 | 0 |
| `G0` | 1 | 17 | 8 | 2 |
| `G1` | 14 | 22 | 5 | 0 |
| **Total** | | **176** | **172** | **3** |

Of the 176 halters, 175 reach `E0` within 740 defined steps by direct replay. The `G1` edit to `0LF` takes 2,610,370,830,869,531,054 defined steps by the sweep calculation for that edit. Of the 172 nonhalters, 171 have finite closed-window certificates and `B0` changed to `0RE` preserves an even reserve after startup. The three equivalences are `G0` changed to `0LC` or `1RF`, and `F0` changed to `0RA`. These counts refer to the 351 labeled replacements above.

## Companion check

At each of the first 6,000 blank sizes $y_t$, test the six possible phases of the signed gap cycle $1,-2,-3,-1,2,3$ against the actual parity bits. Only positive companion starts count. A gap $d$ updates by subtracting the two size recurrences: if $e=y\bmod2$, the companion parity is $e$ for even $d$ and $1-e$ for odd $d$. Among those tested, the longest match lasts **20 transitions**, starting at sweep 542 with $d=-1$. The next transition leaves the cycle. The following integer computation also checks that the blank reserve never went negative over the data used.

```python
y, m = 2, 0
sizes, bits = [], []
for _ in range(6250):
    e = y % 2
    sizes.append(y)
    bits.append(e)
    y = (3*y + 7*e)//2
    m += 2 - 3*e
    assert m >= 0

best = (-1,)
for t in range(6000):
    for start_gap in (-3, -2, -1, 1, 2, 3):
        if sizes[t] + start_gap <= 0:
            continue
        i, d = t, start_gap
        while abs(d) in (1, 2, 3):
            assert i < len(bits)
            e = bits[i]
            other = (1-e) if d % 2 else e
            d = (3*d + 7*(other-e))//2
            i += 1
        best = max(best, (i-t-1, t, start_gap))  # exclude the exit
assert best == (20, 542, -1)
```

The test rules out an infinite match for these starting times only.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
