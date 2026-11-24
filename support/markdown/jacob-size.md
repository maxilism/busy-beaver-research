# The least size orbit of Jacobzheng’s machine

maxilism

[Jacobzheng’s published table and parity rule](https://wiki.bbchallenge.org/w/index.php?title=Cryptids&diff=9600&oldid=9597) describe a BB(7) machine with a growing size and a reserve that can run out. Continue the size recurrence regardless of reserve. At each positive time its value from the blank seed is the **least size obtainable from any positive integer start** in that many iterations. From the fourth iteration on, the *second* least is the blank seed’s next size. A different comparison, with one other size that stays close forever, would give a sufficient condition for the reserve not to run out. No such companion is known for a reached blank checkpoint.

## The two smallest sizes

The table, written in state order `A` to `G` with one instruction for each bit, is

```
1LG0LD_1RE1RA_1RB1RC_1RC1LD_---0LF_1LC1LF_1LF1LE
```

At a checkpoint the head scans a zero in state `C`, with $1^n0\,1^m$ to its right and blanks elsewhere. Put $y=n-1$. The [checkpoint rules](jacob-derivations.md#checkpoint-sweep) start from $y_0=2,m_0=0$ after three steps from blank. An even $y$ earns two units of reserve. An odd $y$ spends one and halts if $m=0$. Continue the size calculation regardless of reserve:

$$
y_{t+1}=T(y_t),\qquad T(2k)=3k,\quad T(2k+1)=3k+5.
$$

We compare **positive integer** starting sizes. Let row $t$ contain $T^t(u)$ for every such start $u$. One way to draw the rows is to swap positions $1,2$, then $3,4$, and so on in disjoint pairs, and send the contents of position $s$ to position $\lfloor3s/2\rfloor+2$ of the next row. Follow a label at $2k$ or $2k+1$ through those two operations to get the formula for $T$. Empty positions take part in the swaps too.

| Row | Start 1 | Start 2 (blank) | Start 3 | Start 4 | Start 5 | Start 6 |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 5 | **3** | 8 | 6 | 11 | 9 |
| 2 | 11 | **8** | 12 | 9 | 20 | 17 |
| 3 | 20 | **12** | 18 | 17 | 30 | 29 |
| 4 | 30 | **18** | 27 | 29 | 45 | 47 |
| 5 | 45 | **27** | 44 | 47 | 71 | 74 |
| 6 | 71 | **44** | 66 | 74 | 110 | 111 |

Two estimates prove these rankings persist. First, $T^t(u)\ge (3/2)^t u$. Second, if one position leads another by at least four, it stays ahead by at least four: a gap of four becomes six, and a gap $d\ge5$ becomes at least $(3d-7)/2\ge4$. In row 3, label 2 is at 12 and all others are at least 17, by the table and the first estimate. Thus 2 stays first. In row 6, label 3 is at 66 and every label other than 2 and 3 is at least 71. Thus 3 stays second. The earlier rows give the stated starting times. Since $T(2)=3$, the two least positions for $t\ge4$ are $y_t$ and $y_{t+1}$.

There is an equivalent way to find the blank sizes. Give each positive integer its *depth*, the number of successive positive predecessors it has under $T$. A predecessor is unique when it exists: $3k$ comes from $2k$, and $3k+2$ comes from $2k-1$ if that is positive. The depth is finite since $T(u)>u$. Row $t$ consists exactly of the positions of depth at least $t$. The start 2 has depth zero, so $y_t$ has depth exactly $t$ and, for $t\ge1$, is the first integer of that depth. For $t\ge4$, every position strictly between $y_t$ and $y_{t+1}$ has depth less than $t$. These records identify the blank sizes, but the ranking does not count their odd terms.

## What a bounded companion would prove

Suppose the machine reaches size $y$ with at least four units of reserve. **If** some other positive integer $z$ satisfies $\sup_i|T^i(z)-T^i(y)|<\infty$, the machine runs forever from this checkpoint. Here the companion’s own reserve is irrelevant.

To prove this, let $d=z-y$ be the signed gap at a given step and $e=y\bmod 2$. An even gap becomes $3d/2$. An odd gap becomes $(3d+7(1-2e))/2$. The maps on even and odd inputs are separately injective and have disjoint images modulo 3, so the gap never becomes zero. For $|d|>7$, the excess $|d|-7$ grows by at least a factor of $3/2$ per step. Magnitude 7 could stay bounded only by retaining its value forever, forcing constant parity. That cannot happen: an infinite even tail would require $2^j\mid y$ for every $j$, an infinite odd tail $2^j\mid y+7$. Magnitudes 4 and 6 escape via $4\to6\to9$, and 5 goes to 4 or 11. The remaining bounded choices form just one cycle:

| Current $d$ | $1$ | $-2$ | $-3$ | $-1$ | $2$ | $3$ |
|---|---:|---:|---:|---:|---:|---:|
| Next $d$ | $-2$ | $-3$ | $-1$ | $2$ | $3$ | $1$ |
| Required parity of $y$ | odd | either | even | even | either | odd |

Every six consecutive steps earn at least twice and lose at most four times. Whole six-step blocks therefore have nonnegative net change, and a partial block needs at most four units. This proves the condition. No positive companion can work at time zero: the gap from the blank size to its nearest competitor eventually equals $y_{t+1}-y_t\ge y_t/2$, which tends to infinity. Later checkpoints can be compared with fresh positive seeds. A [reproducible check](jacob-derivations.md#companion-check) of the first 6,000 starts along the blank orbit found no cycle match longer than 20 transitions.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
