# Gaps between starting sizes for prescribed net reserve changes in Bigfoot

maxilism

At its 49th four-sweep checkpoint after initialization, Bigfoot has reserve 27 and size $y=3021335427802676475075229$. In the next 14 blocks it gains 11 units of reserve. Increase $y$ by $535992208665470815$, less than $1.775\times10^{-7}$ of its value, and leave the reserve at 27. The new configuration loses two units in every block until it attempts its 28th loss on sweep 56 and halts. Both configurations are legal. Only the first is known to occur on the blank run.

How large an interval of starting sizes can miss a prescribed word of gains and losses? Specifying $L$ exact rows of Matthew House's four-sweep map gives one congruence class modulo $81^L$. Specifying the reserve changes instead leaves choices of row. For six of the seven possible changes, these choices cut the maximum gap by more than any fixed power of $L$.

## The checkpoint and the gap bound

The BB(3,3) holdout Bigfoot has table `1RB2RA1LC_2LC1RB2RB_---2LA1LA`, with 7-state binary compilation `0RB1RB_1LC0RA_1RE1LF_1LF1RE_0RD1RD_1LG0LG_---1LB`. We use [S. Ligocki's sweep rules and House's four-sweep reduction](https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html#alternative-representation), with [House's even-size coordinate](https://github.com/sligocki/sligocki.github.io/issues/8#issuecomment-1773177231). The checkpoint is $C(h,y)=A(h,4y+1,2)$ for nonnegative integers $h,y$. Here $A(h,b,c)$ denotes the tape $(12)^h(11)^b$ to the left of the head boundary and $(11)^c$ to its right, on a blank background, with state $A$ scanning the cell immediately to the left of the boundary. The blank run first reaches $C(2,0)$ after 69 ternary steps. The same checkpoint calculation applies to other starting tapes in the [binary compilation](https://github.com/sligocki/sligocki.github.io/issues/8#issuecomment-2140920663).

Put $p=256$, $q=81$ and let $G$ take a size to the next size after four sweeps. On row $r=y\bmod q$ one has $qG(y)=py+e_r$. The row determines all four changes to $h$. We may record changes after the reserve becomes negative by continuing the arithmetic map. On the actual machine the first attempted loss from zero halts the run.

**Gap theorem.** For every $A>0$ there is a constant $C_A$ with the following property. For every $L\ge1$ and every word of length $L$ over $\{-2,-1,0,1,2,3\}$, every interval of $\lceil C_A q^L/L^A\rceil$ consecutive nonnegative starting sizes contains a size giving that word of net reserve changes in the arithmetic map. The same assertion holds if one asks for the indicated *four individual changes* at each letter. For each net change the table gives two selected rows as alternatives.

| Net change | Lower-offset choice $(r,e_r)$ | Higher-offset choice $(r,e_r)$ | Four changes in order |
|---:|:---|:---|:---|
| $-2$ | $(43,251)$ | $(5,259)$ | $0,0,-1,-1$ |
| $-1$ | $(40,209)$ | $(2,217)$ | $0,0,0,-1$ |
| $0$ | $(4,191)$ | $(47,199)$ | $0,0,-1,1$ |
| $1$ | $(1,149)$ | $(44,157)$ | $0,1,1,-1$ |
| $2$ | $(46,131)$ | $(8,139)$ | $0,1,0,1$ |
| $3$ | $(55,95)$ | $(17,103)$ | $0,1,1,1$ |

One can first prescribe any $m$ exact rows. If their initial sizes are $b+q^m t$ with $0\le b<q^m$, the theorem gives the same bound on gaps **in the index $t$** for the next $L$ changes, uniformly in $m$ and the prefix. The letter $+4$ has only one row. Repeating it $L$ times really does leave a single class modulo $q^L$.

## The addresses of the admissible sizes

Write $z=q/p$ and $\lambda=p/q$. Offsets $d_0,\ldots,d_{L-1}$ of specified rows prescribe precisely the class
$$
y\equiv-\sum_{t=0}^{L-1}(d_t/p)z^t \pmod {q^L},
$$
where division by $p$ uses its modular inverse. Modulo $q$ the congruence fixes the first row because $e_r\equiv-pr\pmod q$. Applying that row and dividing out $q$ gives the assertion for the remaining word by induction.

In each displayed pair the larger offset exceeds the smaller by **8**, independent of the letter. Choose either of the two rows with equal probability at each place. The resulting finite multiset of addresses is a translate of one binary subset-sum distribution for all prescribed words. To handle an exact prefix, observe that $G^m(b+q^m t)=G^m(b)+p^m t$. Solving for $t$ translates and multiplies the address set by a unit modulo $q^L$. We will bound its gaps after *every* such unit dilation $U$.

Divide the addresses by $q^L$ to put them on the circle $\mathbb R/\mathbb Z$. For $q^L\nmid k$, let $v=v_3(k)$, $e=v\bmod4$ and $n=L-\lfloor v/4\rfloor$. The magnitude of Fourier coefficient $k$ is the product of $|\cos(\pi\theta_t)|$, where
$$
\theta_t=\frac{8kUq^t p^{-t-1}\bmod q^L}{q^L},\qquad 0\le t<L.
$$
This follows by factoring the average over the independent binary choices. Terms with $t\ge n$ are 1 in the product. In reverse order, take the centered representative $u_s$ of $\theta_{n-s}$ for $1\le s\le n$. Its reduced denominator is exactly $q^s/3^e$ since $8,p,U$ are units at 3. Adjacent representatives satisfy $q u_{s+1}=p u_s+b_s$, with $b_s$ an integer of magnitude at most $(p+q)/2$. If both representatives have magnitude below $\eta=1/(p+q)$ then $b_s=0$.

## Decay of the finite Fourier product

Call a position large if $|u_s|\ge\eta$. Uniformly in the representatives, the number of large positions in $[j,5j]\subseteq[1,n]$ tends to infinity with $j$. Otherwise there would be arbitrarily late such windows with a bounded number of large positions, hence a bounded number of nonzero carries $b_s$. Iteration gives a sum with a bounded number of terms:
$$
u_j+\sum_{t=0}^{4j-1}(b_{j+t}/p)z^t=z^{4j}u_{5j}.
$$
The right side is too small, as we now show using [J.-H. Evertse, *On sums of S-units and linear recurrences*, Theorem 2, (14), p. 228](https://www.numdam.org/item/CM_1984__53_2_225_0.pdf#page=5).

Delete zero terms and vanishing subsums from the left. None of the vanishing subsums can contain $u_j$, since its reduced denominator is divisible by 3 and no other denominator is. Call the remaining terms $x_i$. Apply Evertse's inequality over $\mathbb Q$ at places $S=\{\infty,2,3\}$ with $T=\{\infty\}$. The tuple $M x$ is integral for $M=q^j p^{4j+1}$ and has no nonempty zero subsum. The product of the three local absolute values of $M$ is 1. Cancelling its archimedean scale in Evertse's inequality gives, for every $\varepsilon>0$,
$$
\left(\prod_i\prod_{v\in S}|x_i|_v\right)\left|\sum_i x_i\right|
\ \gg_{\varepsilon}\ \max_i|x_i|\,\|Mx\|_\infty^{-\varepsilon}.
$$
The implicit constant can also depend on the bound on the number of terms. The product in parentheses is $O(|u_j|q^j)$: each $z^t$ has local product 1, the nonzero digits $b/p$ belong to a fixed finite set, and $|u_j|_2\le1$, $|u_j|_3\le q^j$. The real maximum is at least $|u_j|$ and $\|Mx\|_\infty\le M$. Hence $|\sum x_i|\gg_\varepsilon q^{-j}M^{-\varepsilon}$. For sufficiently small fixed $\varepsilon$ this contradicts $|z^{4j}u_{5j}|\le z^{4j}/2$, because $qz^4<1$.

There are order $\log n$ geometric windows $[5^i,5^{i+1}]$ up to $n$, with at most double counting at endpoints. The uniform window bound implies that the total number of large positions divided by $\log n$ tends to infinity. Each contributes a factor at most $\cos(\pi\eta)<1$. Thus the coefficient is $O_D(n^{-D})$ for every fixed $D$. Apply [Erdős and Turán's interval discrepancy inequality, Theorem III](https://users.renyi.hu/~p_erdos/1948-02.pdf#page=5) to the finite multiset of angles. For a frequency cutoff $K=\lceil L^{A+1}\rceil$, all $1\le k\le K$ have $n\ge L/2$ for sufficiently large $L$. The error in the normalized count of any arc is
$$
O_A\bigl(K^{-1}+L^{-A-2}\textstyle\sum_{k\le K}1/k\bigr).
$$
An arc containing no addresses contributes its whole length as error. Rescaling to integer addresses and enlarging $C_A$ for small $L$ proves the theorem.

The proof for all $A$ supplies no effective onset. An elementary argument gives a small effective power. On a run of small positions $a,\ldots,b$, the recurrence has zero carries, so $q^{-a}\le|u_a|=\lambda^{a-b}|u_b|$. Thus $b\le Ba$ for $B=1+1/\log_q\lambda$. Each small run and the next large position take a starting index $a$ to at most $Ba+2$. Consequently there are at least $\log_B n-O(1)$ large positions, with effective constants. The product is $O(n^{-d})$ for $d=-\log(\cos(\pi\eta))/\log B>0$. Taking $K=L$ above gives, for example, the effective spacing exponent $d/2$.

## Consequence for a safety interval along the blank run

Suppose that at arbitrarily late reached blocks $i$ an argument asserts safety for **every** size in $[y_i,(1+\delta)y_i]$ at the actual reserve $h_i$, with fixed $\delta>0$. A word of $L=\lfloor h_i/2\rfloor+1$ worst blocks would halt one of these starts. Hence $\delta y_i=O_A(q^L/L^A)$. The offsets are between 63 and 259, so $y_i=\Theta(\lambda^i)$ by summing the affine recurrence from 0. Even the bound with $A=0$ gives $L\gg i$. Taking logarithms and then taking $A$ arbitrarily large yields the necessary condition
$$
\frac{h_i-2 i\log_{81}(256/81)}{\log i}\longrightarrow+\infty
$$
along the asserted intervals. If one keeps the last $m$ exact rows, then available block-$i$ sizes instead include $y_i+p^m t$, and the necessary inequality becomes $\delta y_i=O_A(p^m q^L/L^A)$. Neither statement bounds the reserve of the single blank run without the interval hypothesis.

[Arithmetic check](../verification/bb-3-3/bigfoot/bigfoot-spacing-check.py): the six primitive sweep rules reproduce the row pairs, the 49-block example and 1,728 exact three-block addresses.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
