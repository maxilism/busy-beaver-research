# Regular separation at bounded span for the two cubic helices

25 November 2026

For each of #5377178 and #7138511, the minimum number of states needed to separate the blank orbit from the eventually halting configurations on inputs of span at most $W$ is $\Theta(W)$, for DFAs and for NFAs. The same bound holds if every configuration on the blank orbit, of any span, must be accepted. The upper bound gives a DFA that recognizes the **exact orbit** on inputs of span at most $W$.

A canonical word displays the smallest tape interval containing the head and all the ones, with the state just before its scanned bit. Its span counts tape cells. Let $\mathcal O$ be the blank orbit, $\mathcal H$ the eventually halting configurations, and $U_W$ the canonical words of span at most $W$. We consider two requirements on an automaton language $L$. Both require $L\cap\mathcal H\cap U_W=\varnothing$. The first requires $\mathcal O\cap U_W\subseteq L$, and the second requires $\mathcal O\subseteq L$. The parameter $W$ is a positive integer. The sibling proof shows that requiring separation of both sets at every span at once is impossible. [Sibling proof](siblings.md)

## Lower bound from the two equal blocks

Use the transition table of #4817065 with blank state B or E. These are #5377178 and #7138511 after tape reflection and renaming. Put $w=\varepsilon$ for B and $w=10$ for E. For every positive multiple $k$ of three the orbit visits the canonical word $w1\,0^k\,\mathrm D00\,1^k$. Replacing the left exponent by any larger multiple of three gives an eventually halting word. [Return and halting calculations](siblings.md)

Choose $k=3,6,\ldots,3N$, where $N=\max(0,\lfloor(W-|w|-3)/6\rfloor)$. A word with left and right exponents $a,b$ has span $|w|+3+a+b$. Thus every diagonal and every splice used below lies in $U_W$. Choose an accepting NFA run on each diagonal and record the state just before the transition reading D. If two runs share this state, join the longer left block to the shorter right block. The spliced run accepts an eventually halting word in $U_W$, a contradiction. This gives at least $N$ states. On the literal reflected tables, combine the state and its scanned bit into one cell before reflecting. The words then read $1^k0\,[q{:}0]0^k\operatorname{rev}(w1)$, with $q$ the renamed D. Cut after the head cell (after both letters in the split encoding) and join the shorter prefix to the longer suffix. This gives the same count directly in the literal tables.

## Orbit checkpoints and tape charge

Write $\chi(x)$ for the number of zero cells minus the number of one cells in a canonical word $x$. Recall the checkpoints

$$
 P(f,b,c)=f\,\mathrm D0\,(10)^b0\,1^c,\qquad
 Q(f,b,c)=f\,\mathrm D00\,(10)^b1^c.
$$

The two right-edge $T$ families of the return calculation are regular. The other endpoints come from the following rows, where $k$ ranges over positive multiples of three, all exponents are nonnegative, and each row has $f=v0^a$, $c=a$. The down sweeps visit the admissible $a$'s in steps of one and the up sweeps in steps of three. [Checkpoint enumeration](siblings.md)

| Shape | $v$ | Conditions |
|---|---|---|
| $P$ | $w1$ | $a\ge1,\ a+b=k$ |
| $Q$ | $w1$ | $a\equiv b\equiv0\pmod3,\ a+b=k$ |
| $P$ | $w$ | $a\ge1,\ a+b=k+1$ |
| $Q$ | $w$ | $a\ge1,\ a\equiv1,\ b\equiv0\pmod3,\ a+b=k+1$ |

Two cases give regular canonical words directly. In the second row, $a=0$ leaves a regular family after trimming the final unscanned zero. In the last two rows for the B-start, $v=\varepsilon$ and trimming removes all $a$ leading zeros. The number of terminal ones then supplies $a$ in every residue and lower-bound test on $a+b$. After eliminating $k$, these tests are finite-state. Include these cases and both $T$ families in a regular set $R$.

In every remaining row $v$ starts with one and $a\ge1$. Allow any positive $c$ as the final exponent in place of $a$, keeping the row conditions on $a,b$. For each $v$ let $A_v$ be the union of the resulting shapes with that prefix. Each $A_v$ is regular. Both ends are ones, so all displayed tape cells count toward charge. The alternating block contributes zero and the two zeros next to it contribute two. Hence

$$
 \chi(x)=t_v+a-c,\qquad t_v=\chi(v)+2,\qquad x\in A_v.
$$

Here $\chi(v)$ counts the bits of the prefix. The possible $t_v$ are 1 and 2. The actual checkpoints in each relaxed row are exactly its words of charge $t_v$.

## Recovering the orbit between checkpoints

Let $F$ be the union of identity, one genuine machine step, and repetitions of each of the three individual scan tiles from the first paper. These are rational relations on canonical words. Put $\Phi=F^{18}$, where the exponent denotes composition, and let $I$ be the finite blank run through the first $T$ checkpoint. Every word in $\Phi$ applied to an orbit checkpoint is reachable. Conversely, every subsequent run position is within $18$ factors of a checkpoint. The published sweep bound covers the usual rows. The special E-start entry uses three single steps, one repeated two-step scan and fourteen single steps. A prefix that stops inside its scan uses at most five factors. Thus $\mathcal O$ consists exactly of $I$ and the $\Phi$-images of the actual checkpoints above. [Single sweeps and scans, Lemma 2 and §4](https://github.com/maxilism/busy-beaver-research/blob/ee693aa3127ca2aaa09a37f22e8b846fa6048914/results/bb-5-2/cubic-helix.pdf) · [Special entry](siblings.md)

Every $(x,y)\in\Phi$ satisfies $|\chi(x)-\chi(y)|\le D=72$. For a single step the interval ends move at most one cell each and at most one bit changes. Each repeated scan preserves the number of ones and changes the span by at most four. Thus each factor changes charge by at most four. [Tape charge and the deterministic upper bound](https://github.com/maxilism/busy-beaver-research/blob/ee693aa3127ca2aaa09a37f22e8b846fa6048914/results/bb-5-2/cubic-helix-state-complexity.pdf)

Define fixed regular languages

$$
 V=I\cup\Phi(R),\qquad
 B_v=\Phi\bigl(A_v\cap\{x:\chi(x)\equiv t_v\pmod{145}\}\bigr).
$$

The congruence is finite-state, and images of regular languages under a rational relation are regular. The exact orbit satisfies

$$
 \mathcal O=V\ \cup\ \bigcup_v\{y\in B_v:|\chi(y)-t_v|\le72\}.
$$

An actual checkpoint of charge $t_v$ witnesses membership in the corresponding term for all of its images. Conversely, let $x$ witness $y\in B_v$ in that term. Then $|\chi(x)-t_v|\le 144$. The congruence modulo 145 forces $\chi(x)=t_v$. The checkpoint is therefore on the orbit, as is its image $y$. Every word of $V$ is reachable by construction.

A DFA can run the fixed recognizers for $V$ and the $B_v$'s in parallel, accumulating charge modulo $M=W+75$. For each $B_v$ it accepts residues represented by an integer in $[t_v-72,t_v+72]$. It also accepts every word of $V$. All orbit words pass this test. For any word of span at most $W$, its charge differs from any tested integer by at most $W+74<M$, so agreement modulo $M$ is equality. This proves exactness on $U_W$. Only the residue contributes a growing factor to the state count. Reflection preserves charge, the fixed regular languages on atomic head cells remain regular under reversal and relabeling, and separating the state from its scanned bit costs fixed finite control. The same DFA construction thus applies in either literal table, proving the upper bound for both types of automata.
