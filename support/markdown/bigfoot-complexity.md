# Factor complexity of exact four-sweep rows on Bigfoot's arithmetic continuation from blank

maxilism

24 November 2026

Group the sweeps of Bigfoot in fours and record which of the 81 exact arithmetic rows each group uses. Several rows give the same net reserve change. How many different words of $m$ consecutive row identities occur in this one sequence? If the number is $P(m)$, then

$$\lim_{m\to\infty}\frac{P(m)}{m}=\infty.$$

The sequence here starts from the blank checkpoint and continues by the size recurrence even if the reserve would underflow. It agrees with the machine until that first underflow. The bound also holds when we count the four sweep phases **separately** and add their complexities. This is stronger: two sequences of linear complexity can have quadratic complexity when paired.

For comparison, [Dubickas, Theorem 3](https://doi.org/10.1017/S0017089508004655) gives a linear complexity floor for the digits of rational-base ceiling maps. In the $3/2$ case, [Stephan, Theorem C](https://arxiv.org/abs/2609.19007) gives a superlinear *limsup* conditional on rationality of the associated real growth constant. We need no arithmetic assumption on Bigfoot's growth constant. The proof uses integrality of the sizes at the prime 3 as well as their growth in the ordinary absolute value.

## Row offsets as sums of phase labels

Use [Ligocki's six sweep rules and Matthew House's four-sweep table](https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html#alternative-representation) for the BB(3,3) holdout Bigfoot. Its [7-state binary implementation](https://github.com/sligocki/sligocki.github.io/issues/8#issuecomment-2140920663) has table `0RB1RB_1LC0RA_1RE1LF_1LF1RE_0RD1RD_1LG0LG_---1LB`. The House checkpoint is $B(a,x)=A(a,2x+1,2)$, where $a$ counts the reserve. Blank reaches $B(2,0)$ in 69 ternary steps. Set $p=256$, $q=81$, $\lambda=p/q$, $z=q/p$. Write $x_0=0$ and

$$q x_{t+1}=p x_t+d_t.$$

The residue $x_t\bmod q$ specifies one of 81 rows. Its offset $d_t$ lies in $[126,518]$ and specifies the row in turn because $d_t\equiv-px_t\pmod q$. The positive bounded offsets give $x_t\asymp\lambda^t$ for $t\ge1$.

In the original sweep rule the tested residue is $b\bmod6$ at $A(a,b,c)$. At each block the first two phases test odd residues and the last two test even ones. Relabel the odd residues $(1,3,5)$ by $(0,5,4)$ and the even residues $(0,2,4)$ by $(1,2,0)$. With the four labels denoted by $A_0,A_1,B_2,B_3$, the offset of a row is

$$d=126+16A_0+12A_1+72B_2+54B_3. \tag{1}$$

This identity can be checked directly in the 81-row table: for row $r$ with output $pk+s_r$ on input $qk+r$, the entry to check is $qs_r-pr$. Equivalently, iterate the sweep rule $b'=(4/3)(b-r)+c+e_r$, $c'=C_r$ four times from $b=2x+1,c=2$, where $r=b\bmod6$, $e=(-1,-1,3,1,3,5)$ and $C=(2,3,2,5,2,3)$. Reading $b'=2x'+1$ after the fourth update gives (1).

Let $P_s(m;j,L)$ count the length-$m$ factors entirely in the $L$ consecutive letters of phase $s$ starting at block $j$. We prove the following finite-window statement. For every fixed $A\ge0$ and $C>0$ there are integers $T,m_0\ge1$ such that

$$\sum_{s=0}^3 P_s(m;j,Tm)>Cm \qquad(m\ge m_0,\ 0\le j\le Am). \tag{2}$$

Each phase is a projection of the exact row. Thus (2) at $j=0$, with $C$ arbitrarily large, implies the stated limit for $P(m)$. We do not obtain effective values of $T,m_0$.

## Window lengths and the sum of phase periods

Suppose the four phase words on an interval of length $L$ starting at $i$ follow periodic patterns with respective periods $b_s$. Extend those patterns periodically for comparison. At every position let $U$ be the weighted sum of future comparison offsets, with weights $z^k/p$ for offsets $k$ blocks ahead. A single periodic contribution with values $w_0,\ldots,w_{b-1}$ adds the rational number

$$A_W=\frac{\sum_{k<b}w_k z^k/p}{1-z^b}.$$

Its denominator divides $p^b-q^b$ at every cyclic phase. The constant in (1) contributes $126/(p-q)$. Consequently a common denominator $D$ of all the $U$ is the least common multiple of the four integers $p^{b_s}-q^{b_s}$. It is prime to 3 and at most $p^{\sum b_s}$. Also $126/175\le U\le518/175$ by (1), including for the extension. Write $U_0,U_L$ for the centers at the two ends. Telescoping the recurrence gives

$$p^L D(x_i+U_0)=q^L D(x_{i+L}+U_L).$$

The positive integer $D(x_i+U_0)$ is therefore divisible by $q^L$. Using $x_i=O(\lambda^i)$ gives $L\le i\log_q\lambda+(\sum b_s)\log_q p+O(1)$. The **sum** of the periods enters here. Using their least common multiple for the period of the joint row could give a much weaker bound.

## Power decompositions from Rauzy graphs

Suppose (2) fails, so there are counterexample windows with $m,T\to\infty$. Write $P_s(k)$ for counts within the current window. For $k<m$, $P_s(k)\le P_s(m)+m-k$, since every occurrence except possibly the last $m-k$ starts extends to length $m$. Also $P_s(k+1)-P_s(k)\ge-1$. By averaging the sum of the four differences, choose a common $h\in[\lfloor m/2\rfloor,m-1]$ where each difference is bounded above independently of $m$. Each $P_s(h)$ is $O(h)$.

For each phase form the Rauzy graph: vertices are its $h$-letter factors and an $(h+1)$-factor gives an edge from its prefix to its suffix, emitting its last letter. Mark the initial and final vertices and every vertex whose indegree or outdegree differs from one. Only the initial vertex can lack an incoming edge and only the final one can lack an outgoing edge. Since the edge count exceeds the vertex count by at most a constant, there are boundedly many marks and boundedly many directed paths from mark to next mark with unmarked interiors. Each such path has length $O(h)$. An unmarked cycle could not be entered from outside, and the entire graph is traversed by the window walk.

Let $R$ bound the number of marks in any phase. Call a path between marks short if its length is at most $h/(2R)$. In the graph of short paths every cyclic strongly connected component is a single cycle. Otherwise one mark has two distinct first edges within the component. Each returns to that mark using at most $R$ short paths in total. If the two return words are $V,W$, then $VW$ and $WV$ both return to the same $h$-word. Each must be its suffix of length $|V|+|W|\le h$, although their first letters differ.

Between successive nonshort paths, each short component is visited at most once. Collect its complete laps as one power of the cycle word read from its entry mark. Keep the remaining paths and each nonshort path individually. This decomposes each phase after its first $h$ letters into powers of words from a bounded list, each word of length $O(h)$. There are boundedly many pieces between nonshort paths, including in the initial and final stretches. Each nonshort path has length greater than $h/(2R)$, so a prefix of $u$ letters sees $O(1+u/h)$ boundaries.

Take the union of boundaries in the four tracks, including the end of the window. Write $u_0=0<u_1<\cdots$ relative to the common start $i=j+h$. Between successive union boundaries all tracks are periodic with periods $O(h)$. Since $i=O_A(h)$, the separate-period estimate gives $u_N=O_N(h)$ by induction, for every fixed $N$. Thus the number of pieces in the union tends to infinity, as the window has $Tm-h$ letters remaining. Counting boundaries the other way gives fixed $c>0,c'$ with $u_N/h\ge cN-c'$.

## Real and 3-adic bounds for the telescoping sum

At boundary $u_l$ let $U_l^-$ and $U_l^+$ be the incoming and outgoing total periodic centers, evaluated at that same position. Each includes the constant $126/(p-q)$ from (1). At the first and last boundaries we need only the indicated side. Telescoping over the intervals gives

$$
E_N:=x_i+U_0^++\sum_{1\le l<N}z^{u_l}(U_l^+-U_l^-)
=z^{u_N}(x_{i+u_N}+U_N^-). \tag{3}
$$

Only switching tracks contribute to a difference on the left. A track that switches has completed whole copies of its word, so its closing center equals its initial one. A track that continues has the same cyclic phase on both sides and cancels, even if its center has rotated. Thus only centers of the chosen underlying words remain on the left. The terminal centers on the right may be rotated, but are all nonnegative and 3-adically integral. Since $x_{i+u_N}\ge\lambda^{u_N}x_i$, (3) gives both bounds

$$|E_N|_3\le q^{-u_N},\qquad E_N\ge x_i\ge1.$$

Multiply $x_i$, the constant center and the centers of the bounded lists by their common denominator $D$ to obtain integers $b_1,\ldots,b_t$. Take $D$ to be the least common multiple of their denominators. It is prime to 3 and at most $\exp(O(h))$ by the period bounds. The number $t$ is bounded. With $F_N=DE_N$, each $b_a$ is nonnegative, at most $\exp(O(h))$ and $O(F_N)$ in real magnitude, uniformly in $N$. Also $|F_N|_3\le q^{-u_N}$.

## Applying the Subspace Theorem

Fix $N$ and pass to a subsequence on which $t$ and the switching labels at the first $N$ boundaries are fixed. By (3), $F_N$ is then a fixed rational linear combination of $b_a z^{u_l}$ with $0\le l<N$. This is the starting point of the argument following (3) in [maxilism, *Factor complexity of minimal words in rational bases*, pp. 2–3](https://github.com/maxilism/rational-base-words/blob/ed76a2fcc394442bbf6b823b6a7c3bf28d449d63/complexity.pdf). Here $z=81/256$, the small absolute value is at $\ell=3$, and $\rho=81$.

The bounds on $b_a$ and $|F_N|_3$ above give the same estimate for the product of the linear forms. Since $u_N/h\ge cN-c'$, taking $N$ sufficiently large makes that product exponentially small in $h$. For this fixed $N$, the upper bound $u_N=O_N(h)$ bounds the logarithmic height by $O_N(h)$. In dimension one this contradicts the product formula. In higher dimension the Subspace Theorem gives a rational dependence among coordinates chosen to remain independent on every infinite subsequence. This proves (2).

The result concerns distinct factors, not their frequencies. For example, in a hypothetical tail consisting entirely of the four maximally losing rows the even phases would be constant. The two remaining binary choices would have to have superlinear *sum* of factor complexities, since deleting a fixed prefix changes a factor count by at most the prefix length. Nothing in the proof excludes sufficiently complicated choices on such a tail or establishes that the blank reserve stays nonnegative.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
