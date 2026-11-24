# Entry into a halting interval for BB(3,3) holdouts #758 and #153

maxilism

LegionMammal found, and dyuan confirmed, a long interval of configurations that lead to one halting trajectory of #758. We reproduce that interval by exact integer iteration. A further 3,732,721 consecutive starting values all pass through the **same configuration on first crossing** its lower edge. The computation starts each of those trajectories at a specified tape. It remains open whether the blank tape ever enters the interval. If it does, the number of ordinary machine steps to halt lies strictly between $1.0522\times10^{414}$ and $9.1341\times10^{416}$.

## Machines, checkpoints and returns

Machine numbers follow the [BB(3,3) holdout list](https://wiki.bbchallenge.org/wiki/BB(3,3)).

| Entry | Transition table, in state order $A,B,C$ and symbol order $0,1,2$ |
|---|:---|
| #758 | `1RB2LC1RC_2LC---2RB_2LA0LB0RA` |
| #153 | `1RB0LB0RC_2LC2LA1RA_1RA1LC---` |

For instance `1RB` writes 1, moves right and enters $B$. The undefined instruction `---` counts as a final step. For #758 the checkpoint $A(a,c)$ has tape $1\,2^a$ to the left of a boundary and $(20)^c$ to its right, on a blank background. State $C$ scans the cell just left of the boundary. The letter $A$ names the checkpoint family, not the scanned state.

We use [LegionMammal978's ten-rule, two-counter map](https://wiki.bbchallenge.org/wiki/1RB2LC1RC_2LC---2RB_2LA0LB0RA), obtained by contracting dyuan01's eleven-rule system on three counters. The [formalization for #758](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB33/M_1RB2LC1RC_2LCHHH2RB_2LA0LB0RA.lean) proves equivalence of blank halting to this map from $A(0,1)$, reached at raw step 2. The [#153 formalization](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB33/M_1RB0LB0RC_2LC2LA1RA_1RA1LCHHH.lean) gives the same counter map, with a different tape encoding, from $A(1,1)$ at raw step 4.

Put $S=a+2c$, so $a=S-2c$. The following rows suffice for both blank trajectories and the section starts tested below. On them $c\ge1$ and even $c$ occurs only at $a=1$: a reset (h) can give even $c$, then (i) restores odd $c$. The other nonhalting rows preserve odd $c$. Thus the full table's two further rows for even $c$ do not apply. Primes denote the values after a macro, which simulates many ordinary steps.

| Row | Condition | $S'-S$ | $c'$ or outcome |
|:---|:---|---:|:---|
| (b) | $c\equiv1\pmod4$, $a\ge c+2$ | 5 | $(3c+7)/2$ |
| (c) | $c\equiv3\pmod4$, $a\ge c+4$ | 9 | $(3c+13)/2$ |
| (d) | $c\equiv3\pmod4$, $a=c+3$ | | halt |
| (e) | $c\equiv3\pmod4$, $a=c+2$ | 8 | $1$ |
| (f) | $c$ odd, $a=c+1$ | | halt |
| (h) | $c\ge a$, $a$ even, $c$ odd | 5 | $a/2+c+2$, with $a'=1$ |
| (i) | $c\ge a$, $a$ odd, $c$ even | 8 | $c-a+4$ |
| (j) | $c\ge a$, $a,c$ odd | 4 | $c-a+1$ |

A **section return** means the output of the next (h). From $A(1,3)$, the first such return is $A(1,45)$, although the trajectory visits $A(1,23)$ along the way. This convention matters when summing several returns. Every nonhalting macro increases $S$. Hence the sequence of section values $c=(S-1)/2$ is strictly increasing.

## Exact finite entry calculation

Set
$$
H=\frac{3^{307}-8282708212}{13959275},\qquad N=8{,}000{,}000,\qquad L_0=1+2(H-N).
$$
The reported halting interval, often called a wall, comprises all $A(1,c)$ with $H-N\le c\le H-3{,}403{,}055$. Its 4,596,946 integer starting values reach $A(1,H)$ by section returns. Starting at $A(1,H)$ itself gives 306 nonhalting macros and then (d).

Here is the finite test. For $0\le d\le 2N$ start from $A(1,H-d)$, run to the next (h) or halt, and record in $v[d]$ the increase in $c$ at that return, or zero for a halt. One can accelerate a run of $k$ consecutive (j)'s using $a_k=3^k(a+1)-1$ and $S_k=S+4k$. A proposed $k\ge1$ is checked by the last guard $3^k(a+1)\le S+4k-1$ and failure of the next guard. All counter and guard calculations in the sweep used checked integer arithmetic. A 5,000-macro limit would abort a trial and no such abort occurred.

For $0\le d\le N$, label $g[0]$ true and, in increasing order of $d>0$, set $g[d]$ true precisely when $0<v[d]\le d$ and $g[d-v[d]]$ is true. Induction shows that $g[d]$ recognizes arrival at $A(1,H)$ as an (h) return, with $d=0$ counted as already there. It does not test incidental visits to $a=1$ inside an excursion. The greatest false index is $3{,}403{,}054$: its section returns skip the target, which says nothing about whether it halts later. A second halting input, $d=2$, also illustrates why a halt need not receive a true label.

For the additional band, write $d=N+i$ with $1\le i\le N$. All these increments satisfy $1\le v[N+i]\le1468$, so any first return to $d\le N$ lands in the verified interval. To locate the *last* section below $L_0$ before this happens, put $j=i-v[N+i]$ and compute
$$
p[i]=\begin{cases}i,&j\le0,\\ p[j],&j>0.\end{cases}
$$
The last index with $p[i]\ne105$ is $4{,}267{,}279$. Consequently for every $12{,}267{,}280\le d\le16{,}000{,}000$ that last section is $A(1,H-N-105)$. It takes (i) followed by 51 copies of (j) to cross $L_0$, reaching
$$
S=L_0+2,\qquad a=4\cdot3^{51}-1,\qquad c=(S-a)/2.
$$
No earlier crossing is possible because $S$ increases at each macro. Thus visiting even one of those 3,732,721 sections fixes the first crossing. Monotonicity *along* a trajectory does not order the returns of different inputs: #758 from blank reaches a section with $218\mapsto298$, whereas the larger seed $220\mapsto264$.

**Reproducible data.** The [enumerator](../verification/bb-3-3/ternary-entry/basin758.cpp) and [entry calculation](../verification/bb-3-3/ternary-entry/entry-audit.py) use the table above. The SHA-256 of $v[0],\ldots,v[16{,}000{,}000]$ as little-endian unsigned 16-bit integers is `5cd4ea394b6b99c475ca8dc233750df5a3bcc39c33f550614e6ba1130b958d57`. The hash of the corresponding 8,000,001 labels $p$, with $p[0]=0$, is `e32bc4b56f6397eb99562460668bb9832f75cac0b0e3f06d073ada4e54500b2a`. The range and both recurrences specify what these fingerprints check.

## Testing a possible crossing against its past

A long legal continuation can start from a checkpoint with no blank predecessor history. For example, take $S=L_0$ and $c=219261$. In the interior an odd/odd state can make a single (j), denoted $J$, or two successive lower moves from (b),(c), denoted $P$. The first lower move changes the parity of $a$, so it takes a second to return to odd/odd. Apart from these continuations, any reached odd/odd state must have started or just reset with $a=1$, $a=3$ (the (i) after an even-$c$ reset), or $c=1$ (row (e)).

This example admits 403 complete forward letters $J,P$. To search its past, invert $J$ by $a_{\rm old}=(a-2)/3$, $c_{\rm old}=c+a_{\rm old}-1$. For a pair $P$ invert $S_{\rm old}=S-D$, $c_{\rm old}=(4c-\beta)/9$, where $(D,\beta)$ in order bb, bc, cb, cc are $(10,35),(14,47),(14,53),(18,65)$. Keep only nonnegative integers satisfying both original guards in forward order. Exhausting the alternatives gives two states at depth 27, none at depth 28 and 92 state-depth pairs in total. All have $a>3,c>1$, excluding every possible reset or start. Thus this one candidate is unreachable from blank despite having a genuine 27-letter past on another tape. The [guarded search](../verification/bb-3-3/ternary-entry/back-wall.py) does not exhaust all crossing candidates.

## Raw clocks on capture

For #758 the expected magnitude $10^{414}$ to $10^{417}$ was [reported previously](https://discord.com/channels/960643023006490684/1259770474897080380/1568717661494448249). The [raw step bounds](ternary-capture-clock.md) give a deterministic bracket **conditional on the blank run reaching $A(1,H)$**:
$$
1.0522\times10^{414}<T_{758}<9.1341\times10^{416}.
$$
For the upper bound, the changes in the nonnegative potential $\Phi(S,c)=7Sc/3-4c^2$ telescope along the timed rows. For the lower bound, grouping each run with one small counter together with its costly entrance gives the stated bound already on arrival at $A(1,H)$.

A separate finite calculation transfers raw times between machines. LegionMammal [reported a merger](https://wiki.bbchallenge.org/wiki/1RB2LC1RC_2LC---2RB_2LA0LB0RA#Equivalence_to_1RB0LB0RC_2LC2LA1RA_1RA1LC---) after 1,790,901 raw steps of #153 and 1,841,608 of #758. [Direct simulation](../verification/bb-3-3/ternary-entry/twin758.py) reproduces the same 343 nonblank cells under $p\mapsto17-p$ and $1\leftrightarrow2$. State $A$ at position 5 in #153 corresponds to $C$ at 12 in #758. The renaming $(A,B,C)\mapsto(C,A,B)$, symbol exchange and reversal of direction conjugate all nine instructions, including halt, one step to one step. Thus if either blank run halts, $T_{153}=T_{758}-50{,}707$. This clock difference requires no assumption of wall entry.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
