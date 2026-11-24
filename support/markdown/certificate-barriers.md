# Two seven-state machines with no context-free tape separator

maxilism

24 November 2026

From blank, Bigfoot reaches a checkpoint with reserve 2 and size 0. If we change only the size to 2916, the reserve still follows the same sequence over the first four sweeps, from 2 through 3, 4, 3, 3. The altered run then attempts four losses without a gain and halts. Whether the blank run halts remains open.

For binary Bigfoot and Jacobzheng’s machine, no context-free language of ordinary marked tapes can contain the blank run and exclude all configurations that eventually halt. The reason is visible at checkpoints described by two integers. Every arithmetic progression of sizes at fixed reserve contains a halting input, yet the size on a surviving blank run grows exponentially in the number of checkpoints. We also give a restriction on **inductive** certificates with arbitrary interval endpoints: if extra reserve is always admitted, the number of size intervals needed at reserve $h$ grows at least linearly in $h$.

## Checkpoints and reserve changes

Write $h$ for the reserve and $y$ for the size, both nonnegative integers. On each machine the input residue $r=y\bmod q$ selects a row. In size alone each row sends $qk+r$ to $pk+s_r$, where $p,q$ are coprime. Write $F(y)$ for the resulting map and $\lambda=p/q$. The size calculation can continue through a formal overdraft. The physical machine instead halts on the first attempted loss from zero, possibly **inside** a row.

| machine | $p/q$ | blank checkpoint $(h_0,y_0)$ | greatest reserve gain per row $g$ |
|:--|--:|:--:|--:|
| Bigfoot, four sweeps | $256/81$ | $(2,0)$ | 4 |
| Jacobzheng, one sweep | $3/2$ | $(0,2)$ | 2 |

For Bigfoot we use the **original House size**: $B(h,y)=A(h,2y+1,2)$ in [Ligocki's sweep rules and Matthew House's table](https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html#alternative-representation). In [House's even-size refinement](https://github.com/sligocki/sligocki.github.io/issues/8#issuecomment-1773177231), the same tape is $C_{\rm B}(h,u)=B(h,2u)$, so the comparison input $B(2,2916)$ is $C_{\rm B}(2,1458)$. We keep $y$ in the original coordinate. On the ternary tape the checkpoint is $(12)^h1^{4y+1}[A1]1^4$, with the bracket marking the scanned cell. Blank reaches the first checkpoint in 69 ternary steps. Rows 0, 5 and 67 have $s_r=4,22,218$, respectively. Row 0 gives changes $(+1,+1,-1,0)$ while 5 and 67 both give $(0,0,-1,-1)$. Thus size 2916 takes rows $0,67,67$, explaining the opening example. We will also use the nets $+1,-1,0$ of rows $0,4,8$. Across the full table, $126\le qF(y)-py\le518$ and a row has at most two losses.

Jacobzheng's table is `1LG0LD_1RE1RA_1RB1RC_1RC1LD_---0LF_1LC1LF_1LF1LE`. At $C(n,h)$ the head scans zero in state C with $1^n01^h$ to its right. Blank reaches $C(3,0)$ in three steps. With $y=n-1$, [Jacobzheng’s recurrence](https://wiki.bbchallenge.org/w/index.php?title=Cryptids&diff=9600&oldid=9597) is $2F(y)=3y+7(y\bmod2)$. The [tape calculation](jacob-derivations.md#checkpoint-sweep) applies on every such tape. An even $y$ earns two units, and an odd $y$ spends one if $h>0$ or reaches the undefined `E0` instruction if $h=0$.

For either machine $F(y)=\lambda y+O(1)$. On the blank size orbit $y_t$ we have $\log y_t=t\log\lambda+O(1)$ for $t\ge1$: the nonnegative additive errors have bounded geometric sum after scaling by $\lambda^{-t}$, and the first positive size gives a positive lower bound on that scale. Consecutive large sizes have gaps $\gg\lambda^t$. A surviving reserve satisfies $h_t\le h_0+gt$.

## Halting subprogressions at fixed reserve

A word of $n$ rows selects exactly one class of initial sizes modulo $q^n$. Indeed, on the class for a given prefix of length $j$, shifting the input by $q^j u$ shifts the output by $p^j u$. Since $p^j$ is a unit modulo $q$, the $q$ lifts of the input class give each next row once. Induction starts with the empty prefix. This coding is also a case of [Kingsbery, Levin, Preygel and Silva, Theorem 4.8](https://arxiv.org/pdf/0903.4226#page=11): on each row the size map is locally scaling on the 3-adic or 2-adic integers.

Fix a size residue modulo $M\ge1$. Let $f$ be the least exponent such that the part of $M$ supported on the prime dividing $q$ divides $q^f$. Prescribe the first $f$ rows of a representative of the residue. Any continuation of this prefix is compatible with the original residue by the Chinese remainder theorem: the moduli $M$ and $q^n$ have greatest common divisor dividing $q^f$ whenever $n\ge f$.

At fixed $h$, append sufficiently many copies of Bigfoot row 5 or the odd Jacobzheng row. Every input in the resulting subprogression halts, either in the prescribed prefix or when the losses consume what remains. Thus **every infinite progression at fixed reserve meets the halting basin**.

## No semilinear checkpoint or context-free tape separator

A separator must contain all checkpoints reached from blank and avoid all checkpoints leading to a halt. There is no semilinear separator, even without closure under successors. Indeed, in a linear set $b+\sum_i\mathbb N v_i\subseteq\mathbb N^2$ of safe pairs $(h,y)$, any generator $(0,d)$ with $d>0$ gives a forbidden progression. The other nonzero generators have positive first coordinate and finitely many slopes. Taking a finite union yields $y\le A+Bh$ throughout any safe semilinear set. If blank survives, its exponentially growing sizes and at most linearly growing reserves violate this inequality. If blank halts, its first checkpoint already belongs to the halting basin. This also excludes Presburger separators by [Ginsburg and Spanier, Theorem 1.3](https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-p.pdf#page=5).

Use binary tape words with a marked head cell and no exterior blank padding. Bigfoot's 7-state table is `0RB1RB_1LC0RA_1RE1LF_1LF1RE_0RD1RD_1LG0LG_---1LB`. [Iijil's compiler and Ligocki's local simulation check](https://github.com/sligocki/sligocki.github.io/issues/8#issuecomment-2140920663) encode $0,1,2$ as `00,11,10` on every well-formed tape. The checkpoint words in the two machines are therefore

* Bigfoot: $(1110)^h1^{8y+3}[B1]1^8$.
* Jacobzheng: $[C0]1^{y+1}01^h$ for $h>0$, and $[C0]1^{y+1}$ for $h=0$. Only the **unscanned** final delimiter is trimmed.

Restrict a putative context-free separator to these regular forms. A finite-state transduction counts the two runs in distinct letters, one letter per repeated block, removing fixed markers and the fixed length offsets. By [Parikh's theorem](https://doi.org/10.1145/321356.321364) the resulting exponent pairs are semilinear. For a backward certificate containing the halting basin and excluding the blank run, complement the *semilinear slice*, which is again semilinear. This argument does not require context-free languages to be closed under complement. It excludes regular closed tape languages and the additive scalar WFAR of the [BB(5) proof, §§4.2, 4.7](https://arxiv.org/pdf/2509.12337#page=32): on either checkpoint form, a finite automaton scanning repetitions of a fixed block eventually cycles and adds a constant weight per cycle. Splitting exponents by transient and cycle residues makes each of its terminal-state interval tests Presburger. Irregularity arguments for other machines, including [Finned #3](https://discuss.bbchallenge.org/t/10756090-is-irregular/137), already use reached and halting configurations to exclude regular separators.

## Reserve-neutral returns and interval counts

Now let $I$ be a forward-inductive safe set of checkpoints: all sweeps from each member are safe and its next checkpoint belongs to $I$. At a given height $h$, suppose each of the $M$ size residue classes contains at most $K\ge1$ interval components of $I_h$. An interval means consecutive terms of that progression. Every component is finite by the halting-progression result. Let $D$ be the greatest numerical distance between two endpoints of one component, over all the residue classes at that height. An empty fiber needs no bound.

Assume $h\ge2f+2$. Choose the least multiple $n$ of 3 with $n\ge5f+3$ and $\lambda^n\ge2K$. Prescribe the $f$ rows of a representative of the longest component's residue as before. This time choose a continuation that ends at **exactly** $h$. For Bigfoot the prefix changes reserve by some $s\in[-2f,4f]$. Undo it with $|s|$ rows of opposite unit change and pad with net-zero rows. The two-unit margin covers losses within a row. For Jacobzheng choose $n/3$ even and $2n/3$ odd rows in total, putting all the remaining earnings before the remaining losses. The length condition permits either completion whatever the prefix.

Let $a$ be the least nonnegative representative of one compatible subprogression of stride $Mq^n$. On it the neutral word acts by

$$
(h,\ a+tMq^n)\ \xrightarrow{\ n\text{ rows}\ }\ (h,\ F^n(a)+tMp^n),\qquad t\ge0\text{ an integer}.
$$

The longest component contains at least $D/(Mq^n)-1$ of these inputs. By induction their outputs belong to $I_h$ and share one residue modulo $M$, which may differ from the input residue. Each output component has span at most $D$. Hence

$$
\frac{D}{Mq^n}-1\ \le\ K\left(1+\frac{D}{Mp^n}\right),\qquad
D\ \le\ 2M(K+1)q^n=O_M\bigl((K+1)^{1+\log_\lambda q}\bigr).
$$

Returning to the same reserve allows the **same $D$** on both sides. No definability of the endpoints was used.

Suppose now that $I$ contains the blank checkpoint and is upward closed in reserve at fixed size. At height $h$ it must contain all blank sizes with $t\le(h-h_0)/g$. Write $K_h$ for the **total** number of components in its $M$ residue classes. If $K_h\le h+1$, the span estimate makes all component widths polynomial in $h$. Beyond the first $O_M(\log(h+2))$ indices the gaps between the indicated sizes exceed that polynomial, so they require separate components. If $K_h>h+1$, the same lower bound is immediate. Thus

$$K_h\ \ge\ (h-h_0)/g-O_M(\log(h+2)).$$

In particular, boundedly many interval components cannot give an upward-closed certificate. Without upward closure, uniformly bounded component counts still bound fiber cardinalities by the span estimate; the finitely many small heights have finite fibers too. Such a certificate with arbitrary endpoints exists precisely if blank survives and its reserve visits each height a uniformly bounded number of times. For sufficiency take the reached pairs as singleton components; this gives no method for computing their endpoints.

## O-minimal endpoints force rational reserve speed

Suppose, without assuming upward closure, that on each pair of fixed residues $h,y\bmod M$, $I$ is the integer trace of a set definable in a fixed o-minimal expansion of the ordered real field. Here o-minimality means in particular that every definable subset of the line is a finite union of points and intervals. [Cell decomposition and monotonicity](https://doi.org/10.1017/CBO9780511525919) give uniformly bounded component counts and a finite list of definable endpoint functions at large heights. If $I$ contains blank, its finite fibers and strictly increasing sizes force $h_t\to\infty$. Each late $y_t$ is within $O(1)$ of an endpoint $f_i(h_t)$: the interval's integer span is bounded, and rounding its real endpoints to the size progression costs at most $M$ each. Unbounded intervals in the nonnegative size direction are excluded by the fatal progression.

Retain the endpoint labels used infinitely often and the transitions $i\to j$ with height change $k$ that occur infinitely often. These transitions form a finite strongly connected graph: along the late path one can go from each recurrent label to any other without using a discarded edge. Each retained function tends to infinity and is eventually increasing by o-minimality. On an edge, $F(y)=\lambda y+O(1)$ gives $f_j(h+k)-\lambda f_i(h)=O(1)$ at the unbounded sequence of heights witnessing it. This definable difference is eventually monotone, so it is bounded on the entire real tail.

Take one cycle of length $b>0$ and total height change $d$ based at $i$. Composing its edge estimates gives $f_i(h+d)=\lambda^b f_i(h)+O(1)$. Eventual increase and divergence imply $d>0$. If the error is bounded by $L$, start on each integer class modulo $d$ where $f_i>L/(\lambda^b-1)+1$. Iterating the upper and lower inequalities and summing the geometric error bounds gives $f_i(h)\asymp\lambda^{bh/d}$ on all large integer heights. A fixed path to each other recurrent label transports both bounds, with only a fixed shift in height. Comparing $\log y_t=(b/d)h_t\log\lambda+O(1)$ with the independent size growth proves

$$h_t=vt+O(1),\qquad v=d/b\in\mathbb Q_{>0}.$$

For Jacobzheng, $h_t=2t-3O_t$ where $O_t$ counts odd sizes before time $t$. Such an invariant would force $O_t=(2-v)t/3+O(1)$. We do not know whether either blank reserve obeys the required speed. The argument excludes the upward-closed tame invariants outright and imposes a necessary condition on the others.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
