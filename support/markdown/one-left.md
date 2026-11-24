# Blank running time with one left instruction

maxilism

24 November 2026

For a deterministic binary Turing machine let $S_1(n)$ be the maximum blank-tape running time of a halter with $n$ working states and **at most one nonhalting instruction that moves left**. The tape is infinite in both directions. Each ordinary instruction writes a bit and moves one cell, and the attempted undefined instruction counts as one step. Then

$$
 \log_2(S_1(n)+1)=O(n^2\log(n+2)),\qquad S_1(7)<2^{251}.
$$

Reflection gives the same bound for at most one right instruction. The number of *executions* of the exceptional instruction is unrestricted.

The minimum of the numbers of left and right instructions is called the *laterality number*. [Pavlotskaya (1973), Theorem 4, pp. 905–907](https://www.mathnet.ru/links/8452a9624b6dd1542daf38b98d9461f7/mzm7195.pdf#page=7) ([translation](https://doi.org/10.1007/BF01163965)), proved finite-input halting decidable for a fixed binary machine of laterality one. The reduction to a marking left loop and the distinction between transient and periodic writes on a rightward scan already appear there. See also [Margenstern (1997), pp. 162, 165](https://www.numdam.org/item/ITA_1997__31_2_159_0.pdf). We give explicit running-time estimates uniform over the tables at each state count, on **blank** input.

## The tape at a left turn

We can assume the exceptional instruction has the form $q0\to1Lq$: on zero in state $q$, write one, move left and remain in $q$. Here are the other possibilities.

* With no left row, or with a left row reading one, the run on blank sees only fresh zeros before any halt. A halter takes at most $n$ steps.
* If the left row in state $q$ enters $t\ne q$, the coordinate $x+\mathbf1_{\mathrm{state}=t}$ never decreases, where $x$ is the head position. The head stays in the two cells ending at that coordinate. Cells entering the window from the right are blank, and cells dropped on the left cannot be read again. The state and the two bits thus determine the next such signature or halt. There are $4n$ signatures.
* If $q0\to0Lq$, a left scan through unchanged zeros escapes or finds the global rightmost one. From that cell the rightward pass always begins in $q$ on one with an all-zero suffix. The outcome of this pass, up to halt, infinite right scan or the next left turn, is fixed. A halter must halt on the initial right scan or the first such pass. The initial scan and returning left scan each cost at most $n$, the fixed pass at most $n+1$.

With the marking loop $q0\to1Lq$, a left scan paints ones until it escapes or encounters an existing one at $x$. At this **return** the cells $[x,E]$ are all ones and the tape beyond $E$ is blank. The age of a position $u$ is $E-u+1$. Store the ones at or left of $x$ as pending markers, ordered from left to right. The active marker $x$ is the rightmost and has age $k=E-x+1\ge2$. The initial scan takes at most $n$ steps to halt, detect escape, or turn. Its first return takes at most $n$ more. From blank the initial $E\le n-1$ and there are at most $n-1$ pending markers, the initial fresh-zero writes that made ones.

One macro pops $x$ and scans the $k$ ones rightward from $q$. It halts, escapes right, or reads another $z\le n-1$ zeros rightward before the next $q0$. The bound on $z$ holds because a repeated state on fresh zeros would escape forever. On continuation push the positions of all one-outputs in these $k+z$ writes, in increasing order. The turning $q0$ paints a new right edge at $E+\Delta$, where $\Delta=z+1$. The left scan reaches the rightmost pending marker, or escapes left if there is none. The intervening painted cells become the implicit block of ones, not new pending markers.

The descendants of a popped marker all lie at that position or to its right. A set of top markers, called a forest here, can therefore be processed independently of what is below: it halts, runs forever, or **exhausts safely**, leaving the next lower marker to be processed. Safe exhaustion specifies how much the right edge advanced. The distance of the last physical left scan to the next lower marker still depends on the lower tape. With no lower marker, exhaustion means escape. A finite exhausting family processes all its children, rightmost first. We shall exclude safe exhaustion in two cases by finding, inside a putative finite family, a child that activates at least as old as its parent. Repeating this choice would give an infinite descending chain. This argument leaves open whether the family halts.

We count macros first. All pending positions are nonnegative and after $j$ continuing macros $E\le n(j+1)$. A right pass costs at most $E+n+2$ on a halter, and a returning left scan at most $E+n$. Hence if a blank halter makes at most $M$ macro attempts, including its terminal attempt, its raw time including initialization is at most

$$
 R_n(M)=4(n+1)(M+2)^2. \tag{1}
$$

## The scan on ones

Run the rightward pass hypothetically on an infinite string of ones. If it halts, it does so within $n$ reads. A marker of age $\ge n+2$ then halts at once in macro time. Store a mask of smaller ages plus one bit for the existence of older markers. While the active age is small its writes, new ages, and shifts into the older set are exact. With no small marker left the bit decides between halt and exhaustion. At most $2^{n+2}$ signatures suffice; a halter cannot repeat one.

Otherwise the unary state orbit has transient length plus period at most $n$. Write $p$ for the period. For $k\ge n$, the state entering the zero tail and everything it does there depend only on $k\bmod p$.

**A periodic one-output.** Put $N=n^2+2n$. From a marker of age $k\ge N$, the first one-output in the block has offset less than $n$ from $x$. It has at least $n$ one-outputs to its right, since each complete $n$-cell stretch after the first $n$ cells has one. If the family were to exhaust, each of these right siblings would make at least one continuing macro, advancing the edge by at least $n$ in total before the first child activates. That child would be at least as old as the parent. By descent, a marker of age $\ge N$ prevents access to any marker to its left, even if it first waits for younger markers.

Store the mask of ages below $N$ and only the nearest marker of age $\ge N$, if present. With $B=N+3n$ keep its age exact below $B$, otherwise just its residue mod $p$ and the fact that it is at least $B$. Exact active ages can be simulated directly. For active $k\ge B$, the positions of new ages $N,\ldots,N+n-1$ lie in the periodic part of the block just scanned: their offsets from $x$ are $k+\Delta-(N+i)$, $0\le i<n$, between $n$ and $k-1$. This window contains a new old marker. The rightmost old marker and every younger marker are determined by the output from this window rightward, known from the residue and zero tail. Thus halt, escape and successors are exact. With at most $2^{N-1}(1+3n+p)$ signatures, this number also bounds $M$.

## Transient one-outputs

It remains that the period writes only zeros. Let $F$ be the zero-based offsets of one-outputs in the transient. The children of a continuing marker are of two kinds:

| children | positions | information needed |
|---|---|---|
| near the parent | $x+d$, $d\in F,\ d<k$ | all of $F$ occur for $k\ge n$ |
| on the fresh edge | among $E+1,\ldots,E+z$ | the state entering the zero tail fixes all their ages after the turn |

The edge children form a forest $V$ with initial ages in $\{2,\ldots,n\}$, processed before any near child. We call its set of initial ages its *template*. Entry state $q$ turns at once with empty $V$, so at most $n-1$ nonempty templates occur for a given table.

We use the following elementary estimate twice. Suppose that at or above an age threshold the residue modulo $p$ determines whether the rule ends the episode (terminal outcome or reset) or makes an addition, and in the latter case determines the increment, of magnitude at most $H$. In an evaluation that eventually halts or exhausts, a consecutive episode of such additive steps rises at most $2pH$ above its entry age. Before a residue repeats, at most $p$ additions occur. On completing a whole residue cycle above threshold with nonnegative sum, the same cycle can be traversed forever since its minimum will not decrease. With negative sum no later cycle peak exceeds the first. The bound allows both the initial path and the first tour; a terminal outcome or a reset ends the episode.

### Zero or one near child

Take $n\ge2$, and put $d$ equal to the offset of the sole transient one-output, or zero if absent. Then $d\le n-2$. For one original marker, follow the successive near children, processing their edge forests as side calls. Call this sequence a spine. If the edge forest exhausts with gain $D$ and the near child exists, the next spine age is

$$
 k'=k+\Delta+D-d . \tag{2}
$$

If there is no such child the spine ends. A halt, including a halt inside the side forest, also ends it. At $k\ge n+2$, the edge template, $\Delta$, and the presence of the near child depend only on the residue. Relative ages determine every side outcome and exhausting gain because a forest is independent of lower markers.

Charge work $\Delta$ for a continuing macro and one for a terminal attempt. This bounds the number of macros and equals the edge gain on a safely exhausted forest. Fix a finite forest evaluation, ending either in exhaustion or in halt. Let $A$ be the largest actual work of a **direct** side call on its original markers' spines, or zero if none; put $H=n+A$. Each spine iteration costs at most $H$, including one whose side forest halts. A continuing spine iteration costs exactly $k'-k+d$ by (2), and its shift has magnitude at most $H$.

For a spine starting at $k_0$, every episode above threshold starts at most at $\max(k_0,n+2+H)$. Its peak is therefore at most $P=\max(k_0,n+2+H)+2pH$. An exact age cannot repeat on a finite spine: it would start the same continuation before this spine could finish. Hence at most $P$ iterations continue. Telescoping (2), then allowing $H$ for the last iteration, gives work at most

$$
 (k_{\rm last}-k_0)+dP+H
 \ \le\ d k_0+(1+d)[n+2+(1+2p)H]+H.
$$

In the blank forest and in every edge forest, the original markers have initial ages at most $n$. If earlier siblings exhaust with total work $W$, the edge advances by $W$, so the next sibling starts at age $k_0\le n+W$. Write $W'$ for total work through this sibling, possibly the last one because of a halt. With $a=\max(2,n-1)$, $c=2n^2+n$, we get the single recurrence

$$
 W'\le(1+d)W+dn+(1+d)[n+2+(1+2p)H]+H\le aW+cH. \tag{3}
$$

Indeed $dn+(1+d)(n+2)\le(2n-1)H$, since $d\le n-2$ and $H\ge n$; the remaining coefficient of $H$ is at most $(n-1)(1+2n)+1=2n^2-n$. If the forest begins with $b$ siblings, (3) from zero bounds its total work $A_{\rm parent}$ by a geometric sum, even when only a prefix is processed:

$$
 A_{\rm parent}+n\le \frac{c}{a-1}a^b(A+n).
$$

Follow one largest-work nonempty direct call at each nesting level until there is none. A strictly nested template repetition would start the *same* finite evaluation inside itself after real macro progress, which is impossible. The path thus uses at most $n-1$ distinct zero-tail entry states plus the outer blank forest. For an entry state $s$, its sibling count is at most its positive zero-tail distance $z(s)$ to $q$. When the positive distances of **all** states reaching $q$ are sorted, the $j$th is at most $j$, since a path of length $r$ uses every smaller positive distance. Including at most $n-1$ original siblings from blank, the sum of all $b$ on our path is at most $J=(n-1)+n(n-1)/2$. Multiplication yields

$$
 A_{\rm root}+n\le n\left(\frac{c}{a-1}\right)^n a^J . \tag{4}
$$

### At least two near children

Let $K=n^2+n+2$. A marker activated at age $k\ge K$ cannot exhaust safely. In a putative exhausting family choose a right near sibling of its leftmost child, then follow near children down from that sibling. Offsets are less than $n$ and the edge never retreats. The activation age at depth $j$ (sibling at depth 1) satisfies $k_j\ge k-jn\ge k-n^2\ge n+2$ for $1\le j\le n$, so the next near child exists whenever needed. All $n$ continuing macros precede activation of the leftmost child at offset $d<n$. Writing $G$ for the total edge gain from the parent's activation to that child's activation gives

$$
 k_{\rm left}= k+G-d \ \ge\ k+n-d >k.
$$

Descent inside this child rules out exhaustion. From the first activation at age $\ge K$ the lower tape can therefore be discarded when deciding between halt and an infinite run.

For a bounded starting forest use a mask of ages below $K$ and a bit for older markers. While a small marker is active its exact writes and shifts determine the next mask and bit. Stop at halt, escape, empty forest or first activation at age $\ge K$. A repeated signature means it stays in the small ages forever. Thus $L=2^K+1$ macro attempts suffice for this test. If the test reports a high activation, replay its bounded prefix with exact positions to recover that age. With initial ages at most $b$ the age is at most $b+nL$: the edge advances at most $n$ per macro and children never lie left of their parents. Safe exhaustion yields a gain $D\le nL$. When the test concerns a side forest, emptiness returns this gain to the caller.

Set $B=K+n$ and $H=B+n+nL$. The following rules now need only one high active age.

* For $K\le k<B$, process its macro and test **all** children, of initial ages at most $B+n$. Safe exhaustion is impossible. The result is terminal, infinite, or a reset to an exact high age at most $H$.
* For $k\ge B$, process its macro and test **only the edge forest**. Its outcome is terminal, infinite, a bounded high reset, or safe exhaustion with gain $D$. In the last case the rightmost near child activates at $k'=k+\Delta+D-\max F\ge K$. This is a residue-dependent addition of magnitude at most $H$. In each case with a new high age, its ancestors are dispensable by the no-exhaustion result.

Start by applying the small-age test to the blank forest. Each subsequent episode of additive steps above $B$ starts at most at $H$, at initialization or after a reset. The residue estimate gives a peak at most $(2p+1)H$. No exact high age repeats on a halter, since its future no longer uses the discarded ancestors. There are at most $(2p+1)H+1$ high activations in this reduced procedure, costing at most $L+1$ macros each. With initialization a convenient bound is

$$
 M=(L+1)[(2p+1)H+3]+1. \tag{5}
$$

## Substitution of the state count

For seven states the terminating unary case uses $M\le2^9$. The periodic one-output case uses $M\le29\cdot2^{62}$. In (4), $(a,c/(a-1),J)=(6,21,27)$, so (1) is at most $32(7\cdot21^7\cdot6^{27})^2<2^{212}$. In (5), $K=58$, $L=2^{58}+1$, $H=72+7L$. Substituting $p=7$ in (5) gives $32(M+2)^2<2^{251}$. The periodic one-output bound gives less than $2^{139}$ by (1), and the easy rows are smaller.

For varying $n\ge2$, the logarithm of (4) is $O(n^2\log(n+2))$, while (5) and the finite signature counts are $2^{O(n^2)}$. Squaring in (1) does not change the asserted logarithmic order. The single-state case has only finitely many tables and does not affect the asymptotic statement.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
