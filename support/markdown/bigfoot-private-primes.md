# Private prime factors of Bigfoot checkpoint sizes

maxilism · 25 November 2026

In Matthew House’s four-sweep map for ternary Bigfoot, write $x_i$ for the size at checkpoint $i$. With $p=256$ and $q=81$, the residue $r_i=x_i\bmod q$ selects a row, and $q x_{i+1}=p x_i+e_{r_i}$ with $126\le e_{r_i}\le518$. We adapt the fixed-word argument for odd Collatz trajectories to count starting sizes that follow the same rows. [House’s map](https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html#alternative-representation) · [Row offsets](bigfoot-complexity.md#row-offsets-as-sums-of-phase-labels) · [Collatz argument, §3](https://github.com/maxilism/collatz-multiplicative-rank/blob/e6b27ea934dff58d08903e6a8f5af73b0f1fb10f/private-primes.pdf)

**Proposition.** Let $m=\log X$ and fix $a>0$. For any prescribed word of $L$ rows, choose $x_0$ uniformly among the integers in $[X,2X)$ giving that word. There is a constant $C_a$ such that if

$$
X/81^L \ge \exp\!\bigl(C_a(\log m)^2\bigr),
$$

then, outside a fraction $O_a(m^{-a})$ as $X\to\infty$, every size $x_0,\ldots,x_L$ has a prime factor greater than $T=m^{a+4}$, and no prime above $T$ divides two of the sizes. In particular the sizes are multiplicatively independent. The estimate is uniform in the word and in $L$.

**Proof.** The word specifies one residue class modulo $q^L$. Indeed, shifting the start by $q^i$ preserves the first $i$ rows and shifts $x_i$ by $p^i$, a unit modulo $q$. Thus at each stage exactly one of the $q$ lifts gives the prescribed next row. On the resulting class there are $M=X/q^L+O(1)$ starts in the interval. As they run in increasing order, the values at date $i$ form an arithmetic progression of step $A_i=p^i q^{L-i}$.

For $j=i+d>i$, iteration gives

$$
q^d x_j-p^d x_i
=\sum_{t=0}^{d-1}p^{d-1-t}q^t e_{r_{i+t}}.
$$

As in Weaver’s common-divisor argument, a prime dividing both sizes must divide the right side. This is a positive integer fixed by the word and bounded by $O(p^d)$, so it has $O(d)$ distinct prime factors. For a candidate $\ell>T$, the step $A_i$ is invertible modulo $\ell$, so at most a fraction $1/\ell+1/M$ of starts have $\ell\mid x_i$. Summing over pairs bounds the fraction with a repeated large prime by $O(L^3(T^{-1}+M^{-1}))$. [Weaver, §2](https://rstation.ai/problems/collatz/papers/138)

It remains to bound the fraction for which some $x_i$ has only prime factors at most $T$. Fix $i$ and divide its progression by the common factor $g=\gcd(x_i,A_i)$, which is the same for every start in the class. The resulting values $z=x_i/g$ are coprime to the new step and satisfy $z\ge x_i/A_i\ge X/q^L$ by positivity of the offsets. Put $R=\sqrt M$. If $x_i$ has only prime factors at most $T$, so does $z$. Multiplying its prime factors until the product first reaches $R/T$ gives a divisor $d$ between $R/T$ and $R$. For each such divisor coprime to the new step, the fraction of hits is at most $1/d+1/M\le 2/d$.

With $w=1/\log m$, Rankin’s bound therefore gives an exceptional fraction at date $i$ of at most

$$
2(R/T)^{-w}\prod_{\ell\le T,\ \ell\ \mathrm{prime}}(1-\ell^{w-1})^{-1}.
$$

The logarithm of the product is $O_a(\log m)$, since $\ell^w\le T^w=e^{a+4}$ and $\sum_{n\le T}1/n=O(\log T)$. The displayed bound is $O_a(m^{-a-2})$ for $C_a$ sufficiently large. Summing over the $L+1=O(m)$ dates and adding the pair bound proves the estimate. In any multiplicative relation, the valuation at a prime unique to $x_i$ forces its exponent to vanish.

At fixed initial reserve, each row determines all four reserve changes. Survival through $L$ blocks therefore selects a union of whole row words, and averaging gives the same estimate among the starting sizes that survive, whenever this set is nonempty. [Four-sweep reserve criterion](../verification/bb-3-3/bigfoot/four-sweeps/)

© 2026 maxilism. Licensed under [CC BY 4.0](../../LICENSE).
