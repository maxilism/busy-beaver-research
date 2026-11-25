# Two counter phases for the five Finned machines

25 November 2026

For each of the five Finned machines, no linear context-free language contains the blank orbit and excludes every eventually halting configuration. For each machine a nondeterministic one-counter automaton recognizes the exact blank orbit in **two successive push–pop phases**, giving a successor-closed separator. One phase increases the counter from zero and then decreases it back to zero. Thus two phases suffice, and even a one-phase pushdown automaton with an arbitrary stack alphabet cannot suffice. The two phases can have three reversals of counter direction.

Blanchard identified these five tables as CTL holdouts and published links to their nonhalting proofs. Iijil gave the ordinary regular obstruction for #3. An earlier project note extended #3 to linear context-free languages. Below the analogous calculation works on all four remaining literal tables. [Family and machine identities](https://discuss.bbchallenge.org/t/bb5s-finned-machines-summary/234/1) · [Iijil's proof](https://discuss.bbchallenge.org/t/10756090-is-irregular/137/1) · [Earlier #3 derivation](finned.md)

## Four tables with the same sweep

A state letter immediately precedes the scanned bit. The tape is two-way with zero exteriors, represented up to translation. Exterior unscanned zeros may be omitted. For the state $q$ in the following table put

$$
P(a,b)=1^a0\,1^bq0,\qquad U(x,y,d)=1^xq0\,1^y(01)^d.
$$

All parameters are nonnegative integers, with $y\ge1$. Each row gives the initial $P$, its return when $b$ has the indicated parity, and the equation characterizing the reachable $U$ words. The opposite parity reaches the machine's missing instruction.

| Machine | $q$ | Initial $P$ | Admissible $b$ | Returned $P$ | Reachable $U$ |
|---|---|---|---|---|---|
| #1, 7763480 | C | $(0,2)$ | $2m$ | $(m,a+m+3)$ | $y=2x+d+4$ |
| #2, 8120967 | B | $(0,1)$ | $2m+1$ | $(m+1,a+m+3)$ | $y=2x+d+3$ |
| #4, 11017998 | A | $(0,0)$ | $2m$ | $(m+1,a+m+2)$ | $y=2x+d+2$ |
| #5, 11018487 | A | $(0,0)$ | $2m$ | $(m+1,a+m+2)$ | $y=2x+d+2$ |

The $U$ sweep is shared exactly. Denote the sweep states by $(q,s,z)$, respectively $(C,D,B)$ for #1, $(B,C,A)$ for #2, and $(A,B,E)$ for #4 and #5. In these roles the rules are $q0\to1Rs$, $s1\to0Rz$, $z1\to1Rz$, $z0\to1Rq$, $q1\to1Lq$. Starting at $U(x,y,d)$, the first two moves shift the zero between the banks one cell right. State $z$ crosses the remaining $y-1$ ones. If $d>0$, it fills the zero of the first $01$ pair. State $q$ then crosses the ones leftwards to the shifted zero, giving $U(x+1,y+1,d-1)$. If $d=0$, state $z$ fills an exterior blank and puts $q$ on the next blank, giving $P(x+1,y)$. In general,

$$
U(x,y,d)\Longrightarrow P(x+d+1,y+d).
$$

Here are the entries into that sweep, directly from the rules. A list such as $A0,B0,C1$ names the successive state and scanned-bit pairs.

- **#4 and #5.** Starting at $P(a,b)$, $A0,B0,C1$ put D immediately left of the new rightmost one. Each $D1,C1$ pair crosses two old ones leftward, leaving $10$ in their place. Odd $b$ leaves C scanning the separating zero and halts. At $b=2m$, D scans that zero with $(10)^m1$ to its right. D writes one and enters A. Its two possible directions, one for each table, lead A to the same exterior zero after scanning left across ones. This gives $U(0,a+2,m)$, also when $a=0$ or $m=0$.
- **#2.** From $P(a,b)$ the three moves $B0,C0,D1$ put E just left of the new rightmost one. The leftward pairs are $E1,D1$. Even $b$ leaves the machine at its missing $E0$ instruction. At $b=2m+1$, D scans the separating zero with $(01)^{m+1}$ to its right. The moves $D0,A0$ fill two zeros and B scans left across the resulting run of ones, giving $U(0,a+3,m)$. One $A0$ step from blank gives $P(0,1)$.
- **#1.** The moves $C0,D0,E1$ put A just left of the new rightmost one. Pairs $A1,E1$ cross old ones leftwards. Odd $b$ reaches the missing $E0$. At $b=2m$, A scans the separating zero with $(10)^m1$ to its right. A fills the zero and starts B moving right. If $m\ge1$, B fills the first interior zero and C scans left, giving $U(0,a+4,m-1)$. For $m=0$, B instead fills the first exterior zero and reaches $P(0,a+3)$ directly. From blank $A0,B0$ give $P(0,2)$.

Write $c=2,1,0,0$ in the four rows respectively and put $e=b-2a-c$. The table gives $e'=-e/2$ whenever $e$ is even, and an odd $e$ halts. Starting at $e=0$ visits every $P(a,2a+c)$ at successive values $a=0,1,\ldots$. Every nonzero $e$ becomes odd after finitely many halvings. In each row the entry on the diagonal at $a=x+d$ has left bank zero, right-bank length $x+d+c+2$ and $x+d$ remaining pairs in $U$. After $x$ sweeps this gives every $U(x,2x+d+c+2,d)$. Conversely $U(x,y,d)$ reaches a $P$ with discrepancy $y-2x-d-c-2$. Every $U$ that violates the displayed equality therefore halts.

## The linear-language obstruction

Intersect a putative linear context-free separator with the regular shape $1^+q0\,1^+(01)^+$. The resulting language is linear context-free. For a sufficiently long word in such a language, the linear pumping lemma allows two pieces near its two ends to be duplicated together. More precisely the factorization is $uvwst$ with $|uvst|\le p$, $|vs|>0$, and $uv^iws^it$ still in the language. To obtain this form, follow a shortest linear derivation until a nonterminal repeats. A repetition occurs among a bounded initial number of productions, the terminals added on its two sides are bounded, and a zero-length addition would contradict minimality.

Choose $U(N,3N+c+2,N)$ with $N>p$. Duplicating the two pieces leaves the middle $1$-block fixed. Since the result must still have the regular shape, it can only increase the left exponent $x$, the number $d$ of final pairs, or both. At least one increases. The resulting $U$ halts, contradicting separation. For #3 the earlier proof uses $(10)^dB1^{b+1}01^a$, with the reached equation $b=d+2a$ and the same pumping at the two ends. Single push–pop phase pushdown languages are linear context-free. [#3 proof](finned.md) · [Ginsburg and Spanier, *Finite-Turn Pushdown Automata*](https://doi.org/10.1137/0304034)

## Two push–pop phases suffice

The five published BusyCoq proofs each give ten shapes. Their union contains blank, excludes configurations at the missing instruction and is closed under each machine step. Hence it excludes every eventually halting configuration. Each shape specifies fixed literals and repeated blocks, and imposes one affine equation on the block counts. In the printed orientation the exponents occur in the order $a,b,c,d$ with unused parameters omitted. [#1](https://github.com/meithecatte/busycoq/blob/912afa5230408fb8fc52d67e51855ea0a82a89c7/verify/Finned1.v) · [#2](https://github.com/meithecatte/busycoq/blob/912afa5230408fb8fc52d67e51855ea0a82a89c7/verify/Finned2.v) · [#3](https://github.com/meithecatte/busycoq/blob/912afa5230408fb8fc52d67e51855ea0a82a89c7/verify/Finned3.v) · [#4](https://github.com/meithecatte/busycoq/blob/912afa5230408fb8fc52d67e51855ea0a82a89c7/verify/Finned4.v) · [#5](https://github.com/meithecatte/busycoq/blob/912afa5230408fb8fc52d67e51855ea0a82a89c7/verify/Finned5.v) · [One-step proof tactic](https://github.com/meithecatte/busycoq/blob/912afa5230408fb8fc52d67e51855ea0a82a89c7/verify/Finned.v#L96-L99)

After moving the constants to either side and choosing the sign of the equation, each row has an initial positive term, a contiguous group of negative terms, and an optional final positive term. For example the four-block equation is $2a-b-c+d=K$ and a three-block equation has the form $2a-b-2d=K$. Absorb fixed offsets into the initial load or the middle subtraction, so the equation says $I+F=M$, with $I,M,F$ nonnegative charges read in that order. Guess the row and its block boundaries using finite control. Load $I$ from zero and decrement while reading $M$. After reaching zero, accumulate the excess of $M$ above $I$ as nonnegative units. Require that the initial load has been fully consumed by the end of $M$. Finally decrement its excess while reading $F$, disallow underflow, and require zero at the end. An accepting run has at most the two push–pop phases stated above. For $F=0$ the second phase can be empty. Bounded coefficients and constant charges use finitely many $\varepsilon$-moves.

Canonical trimming preserves this construction: guess the finite-state normalization transducer's input while reading its output. For #3 the file reflects the public table. Pack the scanned state and bit into one cell before reversing. In reversed order the charges read $F,M,I$, giving the same recognizer after exchanging the two outer terms. Reverse the finite literals and block words as well, then unpack the head. This completes the two-phase upper bound for the literal public tables.

## The exact blank orbits

The exact orbit of each of the five tables also has a two-phase one-counter recognizer. For #1, #2, #4 and #5 take as starting words only the reached $P(a,2a+c)$ and $U(x,2x+d+c+2,d)$ displayed above. The $P$ equality needs one push–pop phase. On a $U$ word load $2x+c+2$ in the first phase and cancel it against the first ones of the middle run. Accumulate its remaining ones in the second phase, and pop one unit for each final $01$ pair. Acceptance at zero enforces the equality. Fixed literals, canonical trimming, and guessing the $P$ or $U$ case use finite control.

It suffices to cover all prefixes of **one entry or one sweep** from these words. A $P$ entry begins with three fixed moves and a leftward repetition of a two-instruction tile crossing pairs of ones. The ending for #4 and #5 is one $D0$ and a left scan on ones. For #2 it is $D0,A0$ and a left scan on ones. For #1 it is $A0$, a right scan on ones, $B0$, and, when $m\ge1$, a left scan on ones. The $m=0$ ending reaches the next $P$ directly. From any $U$ the next segment uses two fixed moves, a right scan on ones, the move $z0$, and an optional left scan on ones. Repetition here is within a single monotone scan. The varying number of complete $U$ sweeps has already been accounted for by the exact $U$ family.

A finite-state transducer checks a monotone scan by keeping the unchanged exterior context and checking the read and written bits and the head displacement on the swept interval. For a two-move tile, finite control tracks its parity; a prefix may stop after the first move. A union over the finitely many stopping stages gives the prefixes of an entire entry or sweep. Every accepted prefix follows actual steps from a reached word, and each configuration after startup belongs to an entry or sweep of this form. Taking these rational images of the $P,U$ families and adjoining the finite startup therefore gives the exact orbit. Simulating a transducer while running the input recognizer leaves its counter phases unchanged.

For #3 an earlier analysis describes three families of actual checkpoints. In the public orientation these are $(10)^n[A0]1^n$, $[C0]1^{2n+2}0\,1^{n+1}$ and $(10)^l1^m[C1]1^s$ with $l,m\ge0$, $s\ge1$ and $l+2s-m=2$. The first two require one push–pop phase. For the third, $l+2s=m+2$ has its two positive groups at opposite ends and its negative group in the middle, giving the two-phase recognizer just used. The cited entry, repair and exit each use a fixed number of monotone scans or local steps. Their guarded prefixes cover the full blank orbit by the same transducer argument. The lower bound above applies to the exact orbit, since that orbit is itself a separator. [Published checkpoint and scan proof](https://github.com/maxilism/busy-beaver-research/blob/ee693aa3127ca2aaa09a37f22e8b846fa6048914/support/markdown/restoring-detours.md#regular-inseparability-and-one-counter-recognition)
