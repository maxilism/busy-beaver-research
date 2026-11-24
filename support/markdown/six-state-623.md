# A logarithmic strip for the last return of BB(6) holdout #623

maxilism

24 November 2026

Machine #623 in [Dos Santos et al.'s classification](https://google-deepmind.github.io/cryptids/BusyBeaver/BB6/Hardness/) has table `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA` and reaches a family of tapes described by two run lengths, $a$ and $d$. Their [certified return map](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean#L1579-L1621) uses the checkpoint $D(a,d)$: on a blank background the head, in state D, faces the word $(10)^{a+1}0\,1^d$ from the left. The blank computation reaches $D(0,7)$ after 66 machine steps. Here *checkpoint* means this start or a successive output of the certified map `highLevelNext`. Its updates can pass over other raw occurrences of a $D$-shaped tape; the statements below concern only the sampled checkpoints.

An entire region has already been [proved to halt on that return](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/HardnessEvidence.lean#L392-L411): it suffices that $a$ be odd and $a<d+3$. We show that **every checkpoint reached from blank has even $a$**. For even $a$, a return can fail only in the strip

$$|a-d|\le 5+\ell_3(\min(a,d)+2),$$

where $\ell_3(n)$ counts the base-three digits of $n$ and $\ell_3(0)=0$. The blank orbit does enter this strip: $D(26,26)$ is its fourth checkpoint and returns safely to $D(2,83)$. Whether the machine ever halts remains open.

## Successful returns preserve even first counters

Two routines make up the published map. Only the first two arguments of each matter here; the omitted third argument does not affect decisions within the routines. The first routine, `evalA`, reads the low digit $r$ of its index $k=3j+r$. With budget $A$, its rules for the first two outputs are:

| Digit | Action |
|---|---|
| $r=0$ | Return $(A-1,j)$ if $A>0$; otherwise halt. |
| $r=1$ | Return $(0,j)$ if $A=0$; otherwise recur on $(A-1,j)$. |
| $r=2$ | Return $(A+1,j)$. |

A successful call outputs a pair whose sum is $A+k+1$ modulo 2. This follows directly on the returning rows, and the recursion preserves the claimed parity since $(A-1)+j\equiv A+k\pmod 2$ when $k=3j+1$.

The second routine, `drainB`, starts with $(A,B)$. It finishes with first counter $A$ when $B=0$. Otherwise it calls `evalA` with $(A,B-1)$ and repeats on the returned pair. The second output is at most $\lfloor(B-1)/3\rfloor<B$ by the digit rules, so the source's fallback for a nondecreasing $B$ cannot halt a drain. A successful drain finishes with first counter congruent to $A+B$ modulo 2.

Here are the possible calls at a checkpoint with even $a$, in order of precedence. A direct return for $a=0$ and even $d$ sets the next first counter to $d$.

| Condition | Call |
|---|---|
| $a=0$, $d$ odd | drain $(d+1,2)$ |
| $d$ odd, $a\ge d+5$ | drain $(a-d-5,d+3)$ |
| $d$ even, $a\ge d+3$ | drain $(a-d-2,d+2)$ |
| $a=d+2$ | drain $(0,a)$ |
| remaining $d$ odd | drain $(d+4-a,a-1)$ |
| remaining $d$ even | evaluate $(d+1-a,a)$, then drain its output |

Each direct drain starts with even sum. In the last row the sum plus one is even, so the evaluation hands an even sum to the drain. Every successful return from an even $a$ therefore gives another even $a$. Induction from $D(0,7)$ proves the parity assertion without assuming that all returns succeed.

## Ternary digit counts and the failure strip

A single digit decision spends at most one budget unit. If another decision follows, its index is at most $\lfloor k/3\rfloor$: recursion uses the quotient $j$, while a new drain uses $j-1$ if $j>0$. Reading $k=0$ finishes the calculation or halts. There are consequently at most $1+\ell_3(k)$ decisions from an initial index $k$, counting that last zero if it occurs. The only failure requires zero budget *before* a decision. Evaluation followed by a drain is thus safe for $A>\ell_3(k)$, and a drain with $B>0$ is safe for $A>\ell_3(B-1)$.

For $a\ge d+5$ the two large-$a$ rows now give, respectively, $a-d\le 5+\ell_3(d+2)$ or $a-d\le 2+\ell_3(d+1)$ on failure. When $d\ge a>0$, the two remaining rows require $d-a\le\ell_3(a-2)-4$ or $d-a\le\ell_3(a)-1$. The intermediate differences $0<a-d<5$ already satisfy the strip bound, and $a=0$ always returns: its only drain has at least two units and first index 1. This proves the bound for the **last checkpoint before a halt**, with no assertion that earlier checkpoints must be in the strip.

The logarithmic width is necessary across even-$a$ inputs. For each even $t\ge2$ choose

$$k=(3^t-1)/2+3^{t+1},\qquad d=k-1,\qquad a=d+2+t.$$

Here $a,d$ are even, and the large-$a$ drain starts with $t$ units and first index $k$. Its first $t$ low ternary digits are all 1 and the next is 0. The 1s consume exactly $t$ units; the 0 halts. These are concrete halting tapes with $a-d=t+2=\log_3 d+O(1)$, starting with $D(34,30)$. They establish the order of the strip's width across inputs, without placing any of those tapes on the blank orbit.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
