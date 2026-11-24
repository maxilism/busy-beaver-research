# Conditional step bounds for BB(3,3) holdout #758

maxilism

24 November 2026

Start #758 (`1RB2LC1RC_2LC---2RB_2LA0LB0RA`) in its first state on a blank tape. Count the final undefined instruction as one raw step. Put
$$
H=(3^{307}-8282708212)/13959275.
$$
**Hypothesis.** The blank run reaches the specific checkpoint $A(1,H)$. The [entry calculation](ternary-entry.md) verifies a finite interval of starts from which that checkpoint is reached. It does not establish this hypothesis from blank. Here we deduce bounds on the raw halting time under the hypothesis.

## Timed rows

LegionMammal978's two-counter map contracts dyuan01's eleven-rule system. A checkpoint $A(a,c)$ has state $C$ scanning the last symbol of $1\,2^a$, followed on the right by $(20)^c$, on a blank background. In the [published table of rows and step counts](https://wiki.bbchallenge.org/wiki/1RB2LC1RC_2LC---2RB_2LA0LB0RA#A(a,_c)_Rules_and_Timings), let $S=a+2c$, $\Delta=S'-S$ on a nonhalting row, $m=\min(a,c)$ and $\tau$ be the raw step count. #758 reaches $A(0,1)$ at time 2. Throughout the subsequent trajectory $c\ge1$, and even $c$ occurs only at $a=1$: (h) can give even $c$, whereupon (i) restores odd $c$. The following eight rows suffice. The last column gives the part of $\tau$ left after subtracting the common term $3m^2$.

| Row | Guard | $\Delta$ | $c'$ or outcome | $\tau-3m^2$ |
|:---|:---|---:|:---|:---|
| (b) | $c\equiv1\pmod4$, $a\ge c+2$ | 5 | $(3c+7)/2$ | $(31c+37)/2$ |
| (c) | $c\equiv3\pmod4$, $a\ge c+4$ | 9 | $(3c+13)/2$ | $29c+65$ |
| (d) | $c\equiv3\pmod4$, $a=c+3$ | | halt | $(43c+75)/2$ |
| (e) | $c\equiv3\pmod4$, $a=c+2$ | 8 | $1$ | $(37c+63)/2$ |
| (f) | $c$ odd, $a=c+1$ | | halt | $8c+6$ |
| (h) | $c\ge a$, $a$ even, $c$ odd | 5 | $a/2+c+2$ | $3a+5c+11$ |
| (i) | $c\ge a$, $a$ odd, $c$ even | 8 | $c-a+4$ | $14c-9a+30$ |
| (j) | $c\ge a$, $a,c$ odd | 4 | $c-a+1$ | $5c+6$ |

In particular $3m^2\le\tau\le3m^2+29S+65$.

## <span id="upper-bound"></span>Upper bound from a telescoping potential

For an upper bound use $\Phi(S,c)=7Sc/3-4c^2\ge0$. Write $x=c/S$, $y=a/S$ and let $c^*$ be the leading homogeneous part of $c'$. The table bounds the frozen normalized cost $[3m^2+\Phi(S,c^*)-\Phi(S,c)]/S^2$, keeping $S$ fixed in the potential.

| Row | $c^*$ | Frozen normalized cost | Upper bound |
|:---|---:|---:|---:|
| (b), (c) | $3c/2$ | $7x/6-2x^2$ | $49/288$ |
| (i), (j) | $c-a$ | $5y/3-5y^2$ | $5/36$ |
| (h) | $S/2$ | $4y^2-5y/6$ | $1/6$ |
| (e) | $0$ | $7x(x-1/3)$ | $0$ |

Each upper bound is at most $5\Delta/144$. Restoring the omitted terms in the potential costs at most $27S+95$: indeed
$$
\Phi(S',c')-\Phi(S,c^*)=(7/3)\Delta c'+(c'-c^*)((7/3)S-4(c'+c^*)),
$$
with $0\le c'-c^*\le7$, $c'\le(S+9)/2$ and $\Delta\le9$. Hence $\tau+\Phi(S',c')-\Phi(S,c)\le(5/144)S^2\Delta+56S+160$. Sum over macros up to size $X$ using $\sum S^2(S'-S)\le X^3/3$ and at most $X/3$ terms. Even adding a terminal halting macro at $X$, elapsed time is below $5X^3/432+100(X+10)^2$.

## <span id="lower-bound"></span>Lower bound from small-counter runs and their entrances

Under the capture hypothesis the run reaches $A(1,H)$ at size $2H+1$. After 306 more nonhalting macros, it halts on row (d) at input size $2H+1258$. Partition the history backwards while $10^8+7200\le X\le 2H+1258$. A balanced input has $m\ge S/50$ and can be taken alone. If the last input is unbalanced, take its maximal run with the same small counter, together with its entrance from balanced inputs. The table gives the following bounds for a group starting at $z\ge10^8$, with total size increment $D$:

| Group | Maximum $D$ | Minimum raw cost |
|:---|---:|---:|
| $c<S/50$ and entrance | 7200 | $3(.315z)^2$ |
| $a<S/50$ and entrance | 2700 | $3(z/5)^2$ |
| Balanced singleton | 9 | $3(z/50)^2$ |

Indeed, small $c$ grows by more than a factor $3/2$ at each step and stays below $H+629$, giving at most 792 inputs. Entry must be by (e) near $a=c$, or by (i),(j) with $(S-3a)/2\le c'<(S+9)/50$. Either gives $m\ge.315S$ at entry. Small $a$ can reset once by (h), then triples or more each step, giving at most 294 inputs. A lower move entering this regime has $a'=S-3c-k$ with $k=2$ or 4, so $c\ge S/5$. For entry by (h), either its own $a\ge S/5$ or the lower move immediately preceding it had $c\ge S/5$ at its input (it had to produce that even $a$). Attach the one or two balanced inputs needed for this cost. The two unbalanced types cannot be consecutive: small $c$ leaves $a'=S-3c-k>S'/50$, and small $a$ leaves $c'\ge(S-3a)/2>S'/50$. Thus the groups are disjoint and the last 800 inputs, if needed, stay above $10^8$.

Each line pays at least $D(z+D)^2/25000$, checked at the maximum $D$ and minimum $z$. Since $3D(z+D)^2\ge(z+D)^3-z^3$, summing gives a lower bound $[X^3-(10^8+7200)^3]/75000$. Using the arrival size in the lower bound and the final input size in the upper bound gives
$$
1.0522\times10^{414}<T_{758}<9.1341\times10^{416}.
$$
The [clock check](../verification/bb-3-3/ternary-entry/clock758.py) verifies the integer inequalities and all 196 small raw timing cases with $0\le a,c<14$.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
