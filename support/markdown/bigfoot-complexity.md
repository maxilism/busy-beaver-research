# Factor complexity of exact four-sweep rows on Bigfoot's arithmetic continuation from blank

maxilism

Group the sweeps of Bigfoot in fours and record which of the 81 exact arithmetic rows each group uses. Several rows give the same net reserve change. How many different words of $m$ consecutive row identities occur in this one sequence? If the number is $P(m)$, then

$$\lim_{m\to\infty}\frac{P(m)}{m}=\infty.$$

The sequence here starts from the blank checkpoint and continues by the size recurrence even if the reserve would underflow. It agrees with the machine until that first underflow. The bound also holds when we count the four sweep phases **separately** and add their complexities. This is stronger: two sequences of linear complexity can have quadratic complexity when paired.

For comparison, [Dubickas, Theorem 3](https://doi.org/10.1017/S0017089508004655) gives a linear complexity floor for the digits of rational-base ceiling maps. In the $3/2$ case, [Stephan, Theorem C](https://arxiv.org/abs/2609.19007) gives a superlinear *limsup* conditional on rationality of the associated real growth constant. We need no arithmetic assumption on Bigfoot's growth constant. The proof uses integrality of the sizes at the prime 3 as well as their growth in the ordinary absolute value.

## The four phase words

Use [Ligocki's six sweep rules and Matthew House's four-sweep table](https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html#alternative-representation) for the BB(3,3) holdout Bigfoot. Its [7-state binary implementation](https://github.com/sligocki/sligocki.github.io/issues/8#issuecomment-2140920663) has table `0RB1RB_1LC0RA_1RE1LF_1LF1RE_0RD1RD_1LG0LG_---1LB`. The House checkpoint is $B(a,x)=A(a,2x+1,2)$, where $a$ counts the reserve. Blank reaches $B(2,0)$ in 69 ternary steps. Set $p=256$, $q=81$, $\lambda=p/q$, $z=q/p$. Write $x_0=0$ and

$$q x_{t+1}=p x_t+d_t.$$

The residue $x_t\bmod q$ specifies one of 81 rows. Its offset $d_t$ lies in $[126,518]$ and specifies the row in turn because $d_t\equiv-px_t\pmod q$. The sizes begin $0,4,18,60$, so the two-letter words $(0,4)$ and $(4,18)$ already contribute two factors to $P(2)$. The positive bounded offsets give $x_t\asymp\lambda^t$ for $t\ge1$.

In the original sweep rule the tested residue is $b\bmod6$ at $A(a,b,c)$. At each block the first two phases test odd residues and the last two test even ones. Relabel the odd residues $(1,3,5)$ by $(0,5,4)$ and the even residues $(0,2,4)$ by $(1,2,0)$. With the four labels denoted by $A_0,A_1,B_2,B_3$, the offset of a row is

$$d=126+16A_0+12A_1+72B_2+54B_3. \tag{1}$$

This identity can be checked directly in the 81-row table: for row $r$ with output $pk+s_r$ on input $qk+r$, the entry to check is $qs_r-pr$. Equivalently, iterate the sweep rule $b'=(4/3)(b-r)+c+e_r$, $c'=C_r$ four times from $b=2x+1,c=2$, where $r=b\bmod6$, $e=(-1,-1,3,1,3,5)$ and $C=(2,3,2,5,2,3)$. Reading $b'=2x'+1$ after the fourth update gives (1).

Let $P_s(m;j,L)$ count the length-$m$ factors entirely in the $L$ consecutive letters of phase $s$ starting at block $j$. We prove the following finite-window statement. For every fixed $A\ge0$ and $C>0$ there are integers $T,m_0\ge1$ such that

$$\sum_{s=0}^3 P_s(m;j,Tm)>Cm \qquad(m\ge m_0,\ 0\le j\le Am). \tag{2}$$

Each phase is a projection of the exact row. Thus (2) at $j=0$, with $C$ arbitrarily large, implies the stated limit for $P(m)$. We do not obtain effective values of $T,m_0$.

## How long can four periodic words agree with the trajectory?

Suppose the four phase words on an interval of length $L$ starting at $i$ follow periodic patterns with respective periods $b_s$. Extend those patterns periodically for comparison. At every position let $U$ be the weighted sum of future comparison offsets, with weights $z^k/p$ for offsets $k$ blocks ahead. A single periodic contribution with values $w_0,\ldots,w_{b-1}$ adds the rational number

$$A_W=\frac{\sum_{k<b}w_k z^k/p}{1-z^b}.$$

Its denominator divides $p^b-q^b$ at every cyclic phase. The constant in (1) contributes $126/(p-q)$. Consequently a common denominator $D$ of all the $U$ is the least common multiple of the four integers $p^{b_s}-q^{b_s}$. It is prime to 3 and at most $p^{\sum b_s}$. Also $126/175\le U\le518/175$ by (1), including for the extension. Write $U_0,U_L$ for the centers at the two ends. Telescoping the recurrence gives

$$p^L D(x_i+U_0)=q^L D(x_{i+L}+U_L).$$

The positive integer $D(x_i+U_0)$ is therefore divisible by $q^L$. Using $x_i=O(\lambda^i)$ gives $L\le i\log_q\lambda+(\sum b_s)\log_q p+O(1)$. The **sum** of the periods enters here. Using their least common multiple for the period of the joint row could give a much weaker bound.

## What low factor counts would force

Suppose (2) fails, so there are counterexample windows with $m,T\to\infty$. Write $P_s(k)$ for counts within the current window. For $k<m$, $P_s(k)\le P_s(m)+m-k$, since every occurrence except possibly the last $m-k$ starts extends to length $m$. Also $P_s(k+1)-P_s(k)\ge-1$. By averaging the sum of the four differences, choose a common $h\in[\lfloor m/2\rfloor,m-1]$ where each difference is bounded above independently of $m$. Each $P_s(h)$ is $O(h)$.

For each phase form the Rauzy graph: vertices are its $h$-letter factors and an $(h+1)$-factor gives an edge from its prefix to its suffix, emitting its last letter. Mark the initial and final vertices and every vertex whose indegree or outdegree differs from one. Only the initial vertex can lack an incoming edge and only the final one can lack an outgoing edge. Since the edge count exceeds the vertex count by at most a constant, there are boundedly many marks and boundedly many directed paths from mark to next mark with unmarked interiors. Each such path has length $O(h)$. An unmarked cycle could not be entered from outside, and the entire graph is traversed by the window walk.

Pass to a subsequence with fixed incidence of these paths and convergent ratios of their lengths to $h$. Call a path *short* if this ratio tends to zero. In the directed graph on marks using only short paths, each strongly connected component with a cycle is a single cycle. Otherwise a vertex has two outgoing short paths within the component. Each can be extended back to that vertex with boundedly many short paths. The two return walks start with different letters and have lengths $a,b=o(h)$. The $h$-word at the vertex overlaps its copies at distances $a$ and $b$, so it has both periods. By the [Fine–Wilf periodicity theorem](https://doi.org/10.1090/S0002-9939-1965-0174934-9) it has period $\gcd(a,b)$ since $a+b\le h$. Its letters at indices $h-a$ and $h-b$ (numbered from zero) must agree. But these are exactly the first new letters of the two walks.

In the walk between successive nonshort paths, take all whole laps through a short cycle as a single power of its word. Take leftover paths and crossings between components individually. Components cannot be revisited after exit. Thus each phase word after its first $h$ letters splits into powers of words from a bounded list, each underlying word of length $O(h)$. There are only boundedly many pieces between nonshort paths, including in the initial or final stretches. Each nonshort path has length at least $\delta h$ for a fixed $\delta>0$. In particular a prefix of $u$ letters in this decomposition sees $O(1+u/h)$ piece boundaries, also when a terminal stretch consists of laps of a single short cycle.

Take the union of boundaries in the four tracks, writing $u_0=0<u_1<\cdots$ relative to the common start $i=j+h$. Between successive union boundaries all tracks are periodic with periods $O(h)$. Since $i=O_A(h)$, the separate-period estimate gives $u_N=O_N(h)$ by induction, for every fixed $N$. Thus the number of pieces in the union tends to infinity, as the window has $Tm-h$ letters remaining. Counting boundaries the other way gives fixed $c>0,c'$ with $u_N/h\ge cN-c'$.

## A sum that is small at 3 and large over the reals

At boundary $u_l$ let $U_l^-$ and $U_l^+$ be the incoming and outgoing total periodic centers, evaluated at that same position. Each includes the constant $126/(p-q)$ from (1). At the first and last boundaries we need only the indicated side. Telescoping over the intervals gives

$$
E_N:=x_i+U_0^++\sum_{1\le l<N}z^{u_l}(U_l^+-U_l^-)
=z^{u_N}(x_{i+u_N}+U_N^-). \tag{3}
$$

Only switching tracks contribute to a difference on the left. A track that switches has completed whole copies of its word, so its closing center equals its initial one. A track that continues has the same cyclic phase on both sides and cancels, even if its center has rotated. Thus only centers of the chosen underlying words remain on the left. The terminal centers on the right may be rotated, but are all nonnegative and 3-adically integral. Since $x_{i+u_N}\ge\lambda^{u_N}x_i$, (3) gives both bounds

$$|E_N|_3\le q^{-u_N},\qquad E_N\ge x_i\ge1.$$

Put $x_i$, the constant center and the centers of the bounded lists of underlying words into one tuple $b$. Its length is bounded and its entries have rational height at most $\exp(Kh)$ with a fixed $K$: an entry $A_W$ has denominator at most $p^{|W|}$ and bounded real magnitude. Height of a rational here means the larger of its absolute reduced numerator and denominator. Pass to a subsequence on which the tuple length is fixed and the label changes at each fixed boundary index stabilize. For each fixed $N$, $E_N$ is now a rational linear form in products $b_a z^{u_l}$, with constant coefficients. We show that these forms cannot satisfy both estimates from (3) for arbitrarily large $N$.

## The Subspace Theorem argument

We use [Schlickewei's $p$-adic Subspace Theorem](https://doi.org/10.1007/BF01220404) in the form stated by [Evertse, Theorem 4, equation (17), p. 231](https://www.numdam.org/item/CM_1984__53_2_225_0.pdf#page=8). Let $d\ge2$ and take $d$ linearly independent fixed rational linear forms in $d$ variables at each place $v\in S=\{\infty,2,3\}$. For every fixed $\varepsilon>0$, the nonzero integer vectors $X$ for which the product of all $3d$ absolute values is at most $\|X\|_\infty^{-\varepsilon}$ lie in finitely many proper rational subspaces. The difficulty is that a dependence among products $b_a z^{u_l}$ may merely repeat a relation already imposed by the centers. We first remove these existing relations, then translate (3) many times to force another.

**Remove existing relations.** Work with sequences indexed by the selected $h$, identifying eventually equal sequences. Let $U$ be the additive group generated by the integer sequences $u_l$, one for each fixed $l$. Each $e\in U$ is $O_e(h)$. By a diagonal subsequence we may impose all of the following countably many conditions. Each $e/h$ converges, and $e$ is eventually constant or tends to one of the two infinities. For each expression $\sum b_a P_a$ with $P_a$ a finite rational linear combination of powers $z^e$, its zero test is eventually constant.

Let $G$ be $U$ modulo its eventually constant exponents. Merge monomials from the same class by absorbing fixed powers of $z$ into their coefficients. In a nonempty reduced sum the smallest exponent dominates in the reals, since differences of exponents from distinct classes diverge with fixed sign. Its magnitude is at least $\exp(-O(h))$ and its rational height at most $\exp(O(h))$, with constants allowed to depend on the sum. These exponential polynomials therefore have a fraction field $F$ of sequences modulo eventual equality. Choose from $b$ a basis $b'_1,\ldots,b'_r$ of its span over $F$. Clear a common nonzero denominator $D$ so that every $D b_a$ is an exponential-polynomial linear combination of the $b'_a$. All of this is fixed **before** choosing $N$. Independence persists against any fixed relation holding on a further infinite subsequence, by the zero tests above.

Expand $D E_N$ as $\sum c_{a,e} b'_a z^e$ and merge classes within each coefficient. The real bound from (3) gives $|D E_N|\ge\exp(-K_0h)$ with $K_0$ independent of $N$. Hence some term has $\lim e/h\le K_2$ for a fixed $K_2$: every $|b'_a|\le\exp(Kh)$, so if all limits exceeded $(K_0+K+1)/\log\lambda$, the finite sum for this $N$ would be too small. Select such a row $a_*$ and its smallest exponent $e_*$. Meanwhile $|D E_N|_3\le\exp(K_3h)q^{-u_N}$, again with $K_3$ independent of $N$.

**Translate the small form.** Let $E\subset G$ be its finite set of remaining exponent classes. They generate a finitely generated torsion-free abelian group: a multiple of an exponent cannot be eventually constant unless that exponent is. In lattice coordinates take a finite box $B$ large enough that $|B+E|\le2|B|$, since the fixed translates enlarge its sides by only a fixed amount. Use a singleton in rank zero. Choose representatives of the finitely many classes involved. Take the vector with coordinates $b'_a z^v$ for $1\le a\le r$ and $v\in B+E$.

At infinity and 2 keep the coordinate forms. At 3 replace the coordinate at $(a_*,g+e_*)$, for each $g\in B$, by the translated form $z^g D E_N$. These have **fixed rational coefficients**: a change of exponent representative only adds an eventually constant integer. They are independent with the remaining coordinate forms. Within the chosen row the first nonzero term has exponent $g+e_*$, a different pivot for every $g$, and all other terms of that row come later in the translation-invariant eventual order.

Before replacement, each coordinate contributes at most $\exp(O(h))$ to the product over $S$, with a constant independent of $N,B$: the three norms of any power of $z$ multiply to one. The ratio of each replacement to its pivot in 3-adic absolute value is at most

$$C_{g,N}\exp(O(h))q^{-(u_N-e_*)}.$$

Indeed $z^g$ cancels, $D$ is fixed and the inverse of the nonzero rational $b'_{a_*}$ has height at most $\exp(Kh)$. The representative contributes only the fixed factor $C_{g,N}$. Clear all denominators of the tuple $b'$ by an integer of size $\exp(O(h))$, at that cost per coordinate in the product. Clear the remaining denominators with powers of 2 and 3, which leave the product unchanged. For fixed $N,B$ the integer vector now has norm at most $\exp(O_{N,B}(h))$ because each exponent is $O_{N,B}(h)$.

There are at most $2r|B|$ coordinates and $|B|$ replacements. Since $u_N/h\ge cN-c'$ and $\lim e_*/h\le K_2$, choose $N$ large enough that the replacements make the product exponentially small in $h$. The $O(h)$ costs per coordinate above are independent of $N$; after choosing $N,B$, the factors $C_{g,N}$ are constants. The Subspace Theorem now gives a fixed nonzero rational relation on infinitely many of the vectors. (In dimension one exponential smallness itself contradicts the product formula for a nonzero integer.) Group this relation by $a$. Within a coefficient the distinct classes $v\in B+E$ cannot cancel identically, so this is a nontrivial $F$-linear relation on the basis $b'_a$. That contradicts the stabilized independence. This proves (2).

The result concerns distinct factors, not their frequencies. For example, in a hypothetical tail consisting entirely of the four maximally losing rows the even phases would be constant. The two remaining binary choices would have to have superlinear *sum* of factor complexities, since deleting a fixed prefix changes a factor count by at most the prefix length. Nothing in the proof excludes sufficiently complicated choices on such a tail or establishes that the blank reserve stays nonnegative.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
