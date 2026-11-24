# Parents and grandparents of fatal checkpoints in BB(6) #623

maxilism

24 November 2026

For each even $t\ge2$, set $y_t=(7\cdot3^t-3)/2$ and $x_t=y_t+t+2$. The checkpoint $D(x_t,y_t)$ of machine #623 halts on its next return. How many of these targets can be the output of an earlier return? Exactly one third of the even parameters, in natural density, have a parent, and that parent is unique. Among the parented targets, a positive fraction have no grandparent.

**Theorem.** Write $A(T)$ for the number of even $2\le t\le T$ whose target has a parent and $J(T)$ for the number of those targets without a grandparent. Then

$$\liminf_{T\to\infty}\frac{J(T)}{A(T)}\ge\frac{70}{729}>9.60\%.$$

The targets counted by $J$ have bounded gaps in the **ordered list of parented targets**. We do not assert a natural density for $J$, or bounded gaps in the numerical values of $t$.

The machine is `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`, #623 in the [classification](https://google-deepmind.github.io/cryptids/BusyBeaver/BB6/Hardness/) of [Dos Santos et al.](https://arxiv.org/abs/2610.22603) At $D(a,d)$ the head in state D faces $(10)^{a+1}0\,1^d$ on a blank background. We use their [certified `highLevelNext` map](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean#L1579-L1621) and its [machine correspondence](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean#L1700-L1744). The linked Lean development is © 2026 Google LLC and is provided under the [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0). A parent means **any** $D(a,d)$ sent to the target by one successful application of this map; a grandparent is a parent of a parent. These are sampled returns, not all raw occurrences of a $D$-shaped tape. The [logarithmic-strip result](six-state-623.md) gives the fatal family above: the first digit index is $y_t+1=(3^t-1)/2+3^{t+1}$, whose $t$ low ternary ones exhaust a budget of $t$ before a zero halts. The results below are deductions from the certified map, not additional Lean theorems.

## Inverting a drain with large first output

In the map's `drainB` routine let $A$ be the budget, $b$ the block count and $m$ the third counter. At $b=0$ the drain returns $(A,m)$. For $b>0$ write $b=3q+e$ with $e\in\{3,1,-1\}$. Provided $A>0$, one reduction takes $b$ to $q$ with the following changes:

| $e$ | change in $A$ | change in $m$ | change in $m+3b$ |
|---:|---:|---:|---:|
| $3$ | $+1$ | $2b+3$ | $0$ |
| $1$ | $-1$ | $2b+5$ | $4$ |
| $-1$ | $-1$ | $2b+1$ | $2$ |

Indeed the drain calls `evalA` at index $b-1$. For $e=3,1$ its low digit is 2 or 0 and it returns immediately. For $e=-1$ the digit is 1; the recursive evaluation is exactly the first evaluation of a drain at $(A-1,q,m+2b+1)$. At $A=0$ the $e=3$ row is unchanged, the $e=1$ row halts, and the $e=-1$ row goes instead to $(0,q-1,m+2b+3)$, increasing $m+3b$ by one.

Fix an output $(x,y)$ with $x,y$ even and $x>y>14$. In every successful drain the quantity $m+3b$ never decreases, so its initial block count satisfies $3b\le y$. Each reduction strictly decreases the block count and gains at most one budget unit. If the budget ever reached zero, the final budget would therefore be at most $b<x$. Only the positive-budget rows can contribute. Write the output in those rows as $(A+g(b),m+F(b))$, where $F(b)=3b+2h(b)$. With $g(0)=h(0)=0$, the table gives the recursion

$$ (g(b),h(b))=(g(q),h(q))+
\begin{cases}(1,0)&e=3,\\(-1,2)&e=1,\\(-1,1)&e=-1.\end{cases} $$

In particular $g(b)\equiv b\pmod2$, and $F$ increases strictly on each parity of $b$. For the latter claim it suffices that $h(b+2)-h(b)\ge-2$. This is direct for $b=0$; for $b=3q-1,3q+1,3q+3$ the difference is respectively $1,-2,1+h(q+2)-h(q)$, proving the bound by induction.

At the outer return the $a=0$ branches give second output 7 or 14, and the $a=d+2$ branch starts a zero-budget drain. An odd $a$ that can return must take one of the two large-$a$ rows, whose launch sum $A+b$ is $a$ or $a-2$; it would output odd $x$. For even $a>0$ the remaining launches are as follows, in source order after these exclusions. The last row is a virtual drain: its initial evaluation has precisely the arguments of the source's direct `evalA` call.

| Input condition | $A$ | $b$ | $m$ |
|---|---:|---:|---:|
| odd $d$, $a\ge d+5$ | $a-d-5$ | $d+3$ | 5 |
| even $d$, $a\ge d+3$ | $a-d-2$ | $d+2$ | 2 |
| remaining odd $d$ | $d+4-a$ | $a-1$ | 3 |
| remaining even $d$ | $d+1-a$ | $a+1$ | 0 |

As $F(b)\equiv b\pmod2$, even $y$ leaves only $m_b=2+(b\bmod2)$: the second row for even $b\ge2$ and the third for odd $b\ge1$. Each solution of $y=m_b+F(b)$ in those ranges yields exactly one parent. Fit $A=x-g(b)$. Since $|g(b)|\le b$ and $x>y\ge3b$, this budget exceeds the maximum possible loss of $b$. The input pair is $(A+b,b-2)$ for even $b$ and $(b+1,A+b-3)$ for odd $b$. In the first case $A$ is positive even, so $a-d=A+2\ge4$; in the second $A$ is odd and $A>b$, so $d$ is odd and $a-d=4-A<5$. These satisfy the required branch tests.

## Two ternary windows for the inverse

For a signed integer $v$, let $p(v)$ sum the weights $0,1,2$ on its balanced ternary digits $0,+1,-1$. For $v\ge0$, let $s(v)$ sum the weights $0,2,1$ on its ordinary ternary digits $0,1,2$. Put $P(v)=3v+p(v)$ and $Q(v)=3v-s(v)$. Both increase strictly on their respective domains: on incrementing a balanced integer, each trailing $+1$ changes to $-1$ and the next digit lowers the cost by at most two; on incrementing an ordinary integer, each trailing 2 loses one and the next digit increases the cost by at most two.

Write $S_n=(7\cdot3^n-1)/2$. Suppose $y=3S_n-C$, with $n\ge1$, $0\le C<3^n$, and $x>y$ both even. Write $L=3^n$, $U=(L-1)/2$, and $m=2+(S_n\bmod2)$. In these two windows the discrepancy between a proposed output and $y$ is

| Block count $b$ | Range of $v$ | $m_b+F(b)-y$ |
|---|---|---|
| $S_n-2v$ | $0\le v\le U$ | $C+m+4n-2P(v)$ |
| $S_n-2v-1$ | $0\le v\le L-1$ | $C+8-m-2Q(v)$ |

To see this, use $S_j=3S_{j-1}+1$. When $b=S_j-c=3q+1+2z$ with $z\in\{-1,0,1\}$, the next offset is $(c+2z)/3$ from $S_{j-1}$. For $c=2v$ this strips the balanced digit $-z$ of $v$; the increment to $h$ is two minus its weight in $p$. For $c=2v+1$ it strips the ordinary digit $1-z$; the increment is its weight in $s$. The indicated windows allow exactly $n$ digit positions with zero padding. With $i$ positions left the remaining offset is at most $2\cdot3^i-1<S_i$, so the reduction does not stop early. The final blocks are $S_0=3$ and $S_0-1=2$, with $h(3)=0$, $h(2)=3$. Substitution in $F(b)=3b+2h(b)$ gives the table.

These windows bracket every possible solution. At $v=0$ each discrepancy is positive; at the far endpoints they are nonpositive. Indeed $P(U)=3U+n\ge(C+m+4n)/2$ and $Q(L-1)=3(L-1)-n\ge(C+8-m)/2$, using $C+m$ even, $C+m\le L+1$ and $L=3^n\ge n+2$. All block counts in the windows exceed 1, and $y>14$ even for $n=1$. By strict increase of $F$ on each parity no block outside the windows can fit. Hence the two inverse branches are exactly the tests

$$ (C+m+4n)/2\in P(\mathbb N_0),\qquad (C+8-m)/2\in Q(\mathbb N_0). $$

Each passing test gives one parent. Strict increase of $P,Q$ and the same endpoint bounds ensure any root is in the indicated window.

## Parent eligibility and grandparent images

For the fatal target use $n=t-1$, $C=0$, $m=2$. The tests become $P(u)=2t-1$ and $Q(v)=3$. The latter never holds since $Q(1)=1<3<5=Q(2)$. Thus a parent exists precisely when $2t=P(u)+1$, and it is unique. This includes $t=2$, which has no parent since $P(0)=0<3<4=P(1)$.

For an admitted $u$, the parent's second counter is $Y=S_{t-1}-2u-2=3S_{t-2}-(2u+1)$; its first counter is even and exceeds $Y$ by $A+2$. Here $t\ge4$, $Y$ is even, and $2u+1\le(4t+1)/3<3^{t-2}$. Use the same inverse with $n=t-2$, $C=2u+1$, $m=3$. The target has a grandparent if and only if at least one of

$$ W(u):=4u+p(u)-1\in P(\mathbb N_0),\qquad u+3\in Q(\mathbb N_0) $$

holds. The sampled blank start is $D(0,7)$: it is neither a target ($y_t\ge30$) nor an admitted parent ($Y>14$). Thus the targets without a parent or without a grandparent cannot occur among the `highLevelNext` checkpoints sampled from blank. This does not exclude unsampled occurrences of $D$-shaped tapes or decide blank halting.

The eligible nonnegative $u$ are those with $P(u)\equiv3\pmod4$. In fact all four residues of $P$ have frequency $1/4$. In a complete centered block of $3^k$ consecutive inputs the low $k$ balanced trits vary freely and the high digits are fixed. The contribution of a trit $r$ in position $i$ to $P$ is $3^{i+1}r+p(r)$. At each position the three options include zero and an odd residue (from $r=-1$). For any nontrivial character of $\mathbb Z/4\mathbb Z$, the three character values therefore have a mean whose absolute value is at most a common $\rho<1$: they are not all equal and only two position types occur. The character mean on a full block is at most $\rho^k$ in absolute value by multiplication. Fourier inversion gives limiting frequency $1/4$ in each class, first letting the length of the initial segment tend to infinity with at most two partial endpoint blocks, then letting $k\to\infty$. As $P(u)=3u+O(\log(u+2))$, this gives $A(T)=T/6+o(T)$, or natural density $1/3$ among even $t$.

## A finite sieve for both grandparent images

For odd $b$ put $R_b=[-(b-1)/2,(b-1)/2]\cap\mathbb Z$. Partition inputs into centered blocks $Bh+R_B$, $B=243=3^5$. Partition inverse arguments into centered blocks $Hj+R_H$ for $P$, ordinary blocks $Hj+[0,H-1]$ for $Q$, where $H=2187=9B$; intersect them with the nonnegative integers. Call a complete input block *good* if, for each test, all its hits come from at most one inverse block. Zero hits is allowed.

For $u=Bh+i$, eligibility picks out $E_c=\{i\in R_B:P(i)\equiv c\pmod4\}$, where $c=3-3Bh-p(h)\pmod4$, since $p(Bh+i)=p(h)+p(i)$. On a good block the two sets of hits among these offsets are contained respectively in

$$ \{i\in E_c:4i+p(i)\in a+P(R_H)\},\qquad \{i\in E_c:i\in b+Q([0,H-1])\} $$

for some integer translations $a,b$. Splitting off the high digits of $v$ only adds constants, as do the $-1,+3$ in the targets. Truncating an inverse block can only delete hits.

| Offset class $c$ | 0 | 1 | 2 | 3 |
|---|---:|---:|---:|---:|
| Eligible offsets | 60 | 66 | 62 | 55 |
| Minimum missed by both | 7 | 9 | 9 | 5 |

The minima are over **all pairs of integer translations**, not just translations known to occur. For each test and shift, form the bit mask of offsets hitting the shifted image. For finite sets of target and image values the only shifts that can hit run from the smallest target minus the largest image value to the largest target minus the smallest image value. Include the empty mask for all remaining shifts. For every pair of masks count the eligible offsets left outside their union and take the minimum. This is an exhaustive finite calculation, not a sample of parameters. Run `python3 digit-masks.py` using the [seven-trit word checker](../verification/bb-6-2/623/digit-masks.py), or `python3 blocks-check.py` using the [arithmetic digit checker](../verification/bb-6-2/623/blocks-check.py). The second uses class labels $P(i)+1$, so its minima in label order are $(5,7,9,9)$.

## Averaging the misses and bounding rank gaps

Write $m_c$ for the tabulated minimum. The block class satisfies $c\equiv3-P(3h)\pmod4$ since $3B\equiv9\pmod4$ and $p(3h)=p(h)$. For $N_j=\#\{1\le h\le n:P(3h)\equiv j\pmod4\}$, appending a balanced trit $-1,0,+1$ gives residues $P(3h)+(-1,0,0)$ on $3h-1,3h,3h+1$. These triples cover $[2,3n+1]$. By equidistribution of $P$ on all nonnegative inputs, $2N_j+N_{j+1}=3n/4+o(n)$, with subscripts modulo four. For $D_j=N_j-n/4$, we have $\max_j|D_j|\le\max_j|2D_j+D_{j+1}|=o(n)$. Thus the mean of $m_c$ over all input blocks tends to $30/4$.

On a bad block discard its entire credit, at most 9. For $u\le U$, first-test hits use $v\le4U/3+O(\log(U+2))$ and second-test hits use $v\le U/3+O(\log(U+2))$. Indeed $P(v)\ge3v$, and $Q(v)\ge v$ first gives $v\le U+3$ before using $Q(v)=3v-O(\log(v+2))$. If hits at $v_1<v_2$ use different inverse blocks, the first argument $v_*$ in the later block satisfies $v_1<v_*\le v_2$. Its image lies between the hits. No other input block can charge this boundary for that test, since distinct input blocks have disjoint target intervals by strict increase of $W$ or $u+3$. There are at most $5U/(3H)+O(\log(U+2))$ such boundaries, counting the two tests separately. Among $U/B+O(1)$ complete blocks the limsup of the fraction discarded is therefore at most $5/27$. Dividing the mean credit left per block by the mean number $B/4$ of eligible offsets proves the claimed lower bound:

$$\frac{30/4-9\cdot(5/27)}{B/4}=\frac{70}{729}.$$

No independence between badness and block class was used. Since $P$ is strictly increasing, each initial segment of parented $t$ corresponds to an initial segment of eligible $u$. Among **all** even parameters the resulting lower density is at least $70/2187$.

Finally, nine consecutive $B$-blocks make up each aligned centered $H$-block. The span of $W$ on that block is at most $4(H-1)+14$, since the high balanced digits cancel and seven low trits cost at most 14. The span of $u+3$ is $H-1$. Starts of successive full inverse-block images are spaced by at least $3H-2$: their differences are $3H+p(j+1)-p(j)$ and $3H-s(j+1)+s(j)$, respectively. Thus at most two first-test and one second-test boundaries fall in those target intervals; the initial truncated block is irrelevant sufficiently far out. At least six small blocks in each sufficiently late aligned $H$-block are good. Each supplies at least five eligible parameters missing both tests. Gaps in $u$ are bounded, hence so are gaps in the ordered list of parented parameters.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
