# Changing one instruction in Jacobzheng’s seven-state machine

maxilism

24 November 2026

Among the 351 ways to replace one defined instruction of [Jacobzheng’s machine](https://wiki.bbchallenge.org/wiki/BB(7)#Cryptids) with a different defined instruction, **176 halt from blank, 172 run forever, and three halt exactly when the original does**. One of the halters takes 2,610,370,830,869,531,054 steps. The original blank run remains undecided.

In state order `A` through `G`, with the zero instruction first, the table is

```
1LG0LD_1RE1RA_1RB1RC_1RC1LD_---0LF_1LC1LF_1LF1LE
```

Keep `E0` undefined. Each of the other 13 entries has 27 alternatives among the 28 choices of bit, direction and next state. This counts labeled tables without identifying symmetries. The original visits every defined entry within the first 44 steps, so every edit changes an instruction actually used from blank. We count *defined* transitions: a run of length $t$ is already facing its first undefined instruction at time $t$.

## How the 351 cases were checked

| Evidence | Number of edits | Result |
|---|---:|---|
| Direct replay to `E0` | 175 | Halt in at most 740 steps |
| Finite closed tape-window sets | 171 | Run forever |
| Sweep count for `G1` changed to `0LF` | 1 | Halt after 48 complete sweeps and one final partial sweep |
| Reserve invariant for `B0` changed to `0RE` | 1 | Run forever |
| Two startup changes and one shifted sweep | 3 | Same halting status as the original |

We use [Nathan Fenner’s $n$-gram closed position set method](https://github.com/Nathan-Fenner/bb-simple-n-gram-cps) on the binary tape. At window length $k$, reaching a fixed point from the all-zero initialization without encountering `E0` certifies nonhalting by [the bbchallenge Collaboration’s Algorithm 2 and Theorem 4.6](https://arxiv.org/pdf/2509.12337v2#page=22). Of the 171 certificates, 139 used $k=2$, 18 used $k=4$, 13 used $k=6$ and one used $k=10$.

The [classifier](../verification/bb-7-2/jacobzheng/jacob-sphere.py) enumerates the replacements and prints the evidence for each with `python3 jacob-sphere.py --list`. Run it in its source directory alongside `jacob-b0-star.py` and `jacob-turn-check.py`. The [per-entry counts](jacob-derivations.md#neighbor-counts) include the first time each entry is read. The following sweep calculations account for the five cases beyond replay and the closed-window checks.

## The long halter

Write $C(n,m)$ for a head in state `C` scanning zero with $1^n0\,1^m$ to its right and blanks elsewhere. Blank reaches $C(3,0)$ after three steps. The [checkpoint sweep](jacob-derivations.md#checkpoint-sweep) consumes $k$ pairs of ones in $3k^2+5k$ steps, leaving $l=3k$ ones to the left of the head. This part of the sweep never uses `G1`.

Change `G1` to `0LF`. On an odd remainder `C0,B1,A0` bring the head to `G1`. It now erases its 1 and sends `F` left across the filled `C0` cell and the $l$ preceding ones. `F0` adds one more. This gives $C(l+2,m+1)$ after $l+6$ exit steps. Even remainders never use `G1`: `C0,B0` fill two cells and leave `E` checking the reserve. If a 1 is present, `E1` erases it and `F` returns left to give $C(l+3,m-1)$. If no 1 is present, the machine halts at `E0`.

| Start | End | Defined steps |
|---|---|---:|
| $C(2k+1,m)$ | $C(3k+2,m+1)$ | $3k^2+8k+6$ |
| $C(2k,m)$, $m>0$ | $C(3k+3,m-1)$ | $3k^2+8k+6$ |
| $C(2k,0)$ | `E0` | $3k^2+5k+2$ |

Iterating the first two rows from $C(3,0)$ at time 3 reaches $C(1{,}390{,}542{,}348,0)$ after 48 sweeps, at time $1{,}160{,}164{,}811{,}207{,}160{,}354$. Substitution of $k=695{,}271{,}174$ in the last row gives the stated total. This is the longest of the 176 proved halters. There is no time bound here on the three edits equivalent to the original.

## The safe reserve test and the three equivalent edits

**`B0` changed to `0RE`.** The [original odd sweep](jacob-derivations.md#checkpoint-sweep) is unchanged: $C(2k+1,m)$ goes to $C(3k+1,m+2)$. On even input with positive even reserve $m=2h$, consume the $k$ pairs. The six instructions `C0,B0,E1,F0,C1,C1` then leave $1^{3k+2}[\mathrm{C}0]1^{2h-1}0$. There are $h-1$ more pairs and an odd exit, producing $C(3(k+h),2)$. The first blank sweep gives $C(4,2)$, so the reserve stays positive and even thereafter.

**`G0` changed to `0LC` or `1RF`.** The first edit goes through $C(0,1)$ and reaches $C(3,0)$ at time 8. The second reaches $C(3,0)$ at time 5. From that checkpoint the [original sweep rules](jacob-derivations.md#checkpoint-sweep) never call `G0`, even on a halting exit. Both machines therefore follow the original run from there.

**`F0` changed to `0RA`.** Write $P(n,m)$ for $C(n,m)$ with one extra 1 immediately left of the head. Consuming $k$ pairs now leaves $l=3k+1$ left ones. Just before `F0`, the tape to its right begins with $l$ ones on the odd exit or $l+2$ ones on the even exit with reserve. The edited `F0` steps right onto the first 1, `A1` erases it, and `D0` writes the new left 1 and returns `C` to the erased cell. Thus the odd exit gives $P(3k,m+2)$ and the even exit $P(3k+2,m-1)$. The even case with $m=0$ still reaches `E0`. From blank the first five steps give $P(1,0)$, followed by $P(0,2),P(2,1),P(5,0)$. From there identify $P(n,m)$ with the original $C(n-2,m)$. Subtracting two from each new size gives exactly the original odd and even rules, with the same reserve and the same halt test. This third machine changes the sweep itself while preserving the halting question.

If edits may also introduce or remove an undefined entry, there are 392 replacements. Deleting any of the 13 defined instructions halts at its first visit. Filling `E0` with any of the 28 defined instructions leaves no possible halt. The totals under that convention are 189 proved halters, 200 proved nonhalters and the same three equivalents.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
