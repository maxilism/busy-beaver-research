# Two-counter safety tests for BB(6) holdouts #184 and #724

maxilism

24 November 2026

For #724, the blank run reaches a checkpoint with counters $(2,4)$. If we start the same return map at $(542,4)$, the second counter grows through $4,13,40,121,364$ while the first decreases at each update by the old value of the second. After four updates the counters are $(364,364)$ and the machine halts. The two starts agree in both counters modulo 6. More generally, fix a checkpoint $(u,v)$ on the blank run with $u,v>0$. For every modulus $m\ge1$ there are halting starts $(u',v')\equiv(u,v)\pmod m$ with $u'/(u'+v')$ arbitrarily close to $u/(u+v)$.

The machines are **#184 and #724** in [Dos Santos et al.'s classification, Problem 4](https://google-deepmind.github.io/cryptids/BusyBeaver/BB6/Hardness/). A *checkpoint* is a tape configuration in the two-counter family at which the published calculation resumes. A *separator* contains every checkpoint visited from blank and no checkpoint from which the machine eventually halts. An inductive invariant certifying blank nonhalting would give such a separator; we do not require the separator itself to be closed under updates.

A set of counter pairs is *semilinear* if it is a finite union of sets $b+\mathbb N v_1+\cdots+\mathbb N v_k$ with $b,v_i\in\mathbb N^2$. Equivalently, it is definable in Presburger arithmetic.

**Theorem.** For either machine there is no separator on the two counters given by a finite Boolean combination of real polynomial sign tests and congruence tests to fixed moduli. In particular, neither machine admits a semilinear counter separator. For #184 there is no semilinear separator even if one samples the blank orbit only at changes of comparison sign. On tape words with the scanned cell marked and all unmarked exterior blanks trimmed, no finite Boolean combination of context-free languages separates the blank orbit from the halting basin. The blank halting status of both machines remains open.

## Normalized two-counter return maps

The [published accelerations](https://arxiv.org/pdf/2610.22603) (Appendices A.8 and A.3) describe the machines from blank; the linked Lean definitions below give their return rules and halting equivalences. With the following changes of coordinates, both halt on $u-v\in\{0,1\}$. Call the branch for $u<v$ left ($L$), and the one for $u\ge v+2$ right ($R$).

| Machine | Blank start $(u,v)$ | Left update | Right update |
|---|---|---|---|
| #184 | $(5,0)$ | $(3u+2,v-u)$ | $(u-v+4,3v+1)$ |
| #724 | $(2,4)$ | $(3u,v-u)$ | $(u-v,3v+1)$ |

* [#184, `1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA`](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA.lean#L1254-L1291): blank reaches the physical $C(0,9)$ after 74 steps. The Lean constructor `.C a b` stores the physical second counter **minus six**. In physical coordinates set $C(a,2k+1)\mapsto(k+1,a)$ and $C(a,2k+6)\mapsto(a+5,k+1)$. Substitution gives the first row. The exceptional even state $C(0,2k+6)$ goes first to $C(k+1,9)$ with unchanged normalized pair, after which the odd rule applies.
* [#724, `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE`](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE.lean#L868-L902): after 76 steps blank reaches $D_0(2,0)=C(6,2,2)$. Set $D_0(a,b)\mapsto(b+2,a+2)$ and $D_1(a,b)\mapsto(a+3,b+2)$. The published halting test $b\in\{a,a+1\}$ becomes the same two differences for either flag. At $v=u+1$ one published update contracts **two** steps of the table: $(u,u+1)\to(3u,1)\to(3u-1,4)$. Here $u\ge2$, so the inserted point $(3u,1)$ is not an immediate halt.

The two tables appear on lines 136 and 548 of the [30 October 2026 BB(6) holdout list](https://wiki.bbchallenge.org/w/images/5/5e/BB6_holdouts_608.txt). The [certified halting families](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/HardnessEvidence.lean#L180-L230) establish that the traps are real. Our question concerns the geometry of their preimages.

## Halting points in every sector and residue class

**Lemma.** Fix $m\ge1$, a pair of residues modulo $m$, and an open interval $I\subset(0,1)$. There are halting starts in that class with $u/(u+v)\in I$ and both coordinates arbitrarily large.

First prescribe just the residues. For #184 fix $u\ge5$. For $N\ge1$ and $d\in\{0,1\}$ take

$$v=A_N-d,\qquad A_N=(u+1)(3^N-1)/2-N.$$

Here $A_N$ is the sum of the first $N$ values $3^j(u+1)-1$ of the growing counter on the left branch. The first $N-1$ are subtracted; at the last the difference is $d$. For #724 fix $v\ge2$ and take

$$u=B_N+d,\qquad B_N=((2v+1)(3^N-1)-2N)/4.$$

This is the corresponding sum on the right branch: its growing counter is $((2v+1)3^j-1)/2$. In both constructions the sum still contains at least two terms before the final test, so every earlier branch is legal.

We check that the free coordinate takes every residue modulo $m$ for arbitrarily large $N$. Both sums have form $[c(3^N-1)-2N]/D$, with $D=2$ or 4. The term linear in $N$ allows a digit to change while the exponential term is fixed to the required precision.

* For the 2-part of $m$, use $v_2(3^{2^j}-1)=j+2$ for $j\ge1$, by successive squaring from $3^2-1=8$. For $A_N$ start with $N$ even, so $A_N$ is even, and choose $d$ for the required parity. Adding $2^j$ to $N$ changes $A_N$ by $-2^j$ modulo $2^{j+1}$. For $B_N$ take $d=0$: adding $2^{j+1}$ changes $B_N$ by $-2^j$ modulo $2^{j+1}$ for $j\ge0$. This fixes the required bits on a progression of exponents with power-of-two step.
* If $3^a\mid m$ is its full 3-part, take $N\ge a$. The sum is now $(-c-2N)/D\pmod{3^a}$, whose slope is a unit. Fix these digits and multiply the step by $3^a$.
* Treat the other prime divisors $p$ in increasing order. Enlarge the current step to its least common multiple $H$ with the order of 3 modulo $p$. All prime factors of $H$ are smaller than $p$, since that order divides $p-1$. Adding $Hp^j$ to $N$ leaves $3^N$ fixed modulo $p^{j+1}$, by binomial expansion, and changes the sum by $-2Hp^j/D$ modulo $p^{j+1}$. Its unit coefficient lets us select the next digit without altering the earlier primes. The witnesses again fill a progression of exponents.

To prescribe the direction as well, use the common linear parts of the two branches,

$$A_L=\begin{pmatrix}3&0\\-1&1\end{pmatrix},\qquad A_R=\begin{pmatrix}1&-1\\0&3\end{pmatrix}.$$

On the direction coordinate $t=u/(u+v)$ their inverses act as $t/(3-t)$ and $(1+2t)/(2+t)$. Their images cover the two halves of $[0,1]$ and both derivatives are at most $3/4$. A sufficiently deep subdivision interval containing the midpoint of $I$ therefore lies strictly inside $I$. Let $w$ be the word producing this inverse interval. Write its forward affine formula as $X\mapsto AX+b$, temporarily ignoring the branch tests; $\det A=3^{|w|}$.

Choose an integer representative $r$ of the desired residue pair. The construction above gives a halting endpoint $Y$ in the class $Ar+b$ modulo $m3^{|w|}$, with the fixed coordinate large and then the free one large. The determinant factor in this modulus makes the inverse integral:

$$Y=Ar+b+m3^{|w|}z\quad\Longrightarrow\quad X=A^{-1}(Y-b)=r+m\,\operatorname{adj}(A)z,\qquad z\in\mathbb Z^2.$$

Thus $X\equiv r\pmod m$. All intermediate backward coordinates tend to infinity with the two coordinates of $Y$, since the inverse matrices are nonnegative with positive diagonal. Undoing $L$ gives $v-u$ equal to the next $v$; undoing $R$ gives $u-v$ equal to the next $u$ minus at most 4. Thus the prescribed branches really do occur. Their fixed additive translations change the initial direction by $o(1)$ relative to the homogeneous inverse. For large enough $Y$ we obtain $u/(u+v)\in I$, as asserted.

## Limiting directions rule out polynomial separators

Suppose the blank computation continues forever. Its mass $u+v$ tends to infinity: on #184 a step gains $u+2$ or $v+5$, and on #724 it gains $u$ or $v+1$. Both coordinates are positive after the first update. Neither branch can run forever on its own: the smaller counter grows at least threefold while successive updates subtract it, up to a fixed additive correction, from the other one.

Nor can a mixed word repeat forever. If it did, let $X\mapsto AX+b$ be the period map, of length $k$. The matrix $P=3^k A^{-1}$ is a product of

$$P_L=\begin{pmatrix}1&0\\1&3\end{pmatrix},\qquad P_R=\begin{pmatrix}3&1\\0&1\end{pmatrix}.$$

A mixed product is strictly positive. On its positive eigenvector the larger eigenvalue $\lambda$ lies strictly between $2^k$ and $3^k$, since each factor multiplies the sum of two positive coordinates by a number in $(2,3)$. The second eigenvalue $\mu=3^k/\lambda$ also exceeds 1. Modulo 3 both factors have form $(1,1)^T f$ for a coordinate row $f$, and so does their product. Its trace is therefore $1\pmod3$. Rational eigenvalues would both be integers greater than 1 dividing $3^k$, which contradicts that trace. In particular the positive eigenline contains no nonzero rational vector.

For the **forward** matrix $A$, the positive eigenline has eigenvalue $\mu$ and the sign-changing eigenline has eigenvalue $\lambda>\mu$. The period map has the rational fixed point $Z=(I-A)^{-1}b$. A nonzero rational displacement $X-Z$ has a component on the sign-changing line, so $Z+A^j(X-Z)$ eventually leaves the positive quadrant. The alternative $X=Z$ contradicts mass growth.

It follows that the orbit has **infinitely many limiting directions**. Indeed, if the limit set were finite, label each late direction by its nearest limit. After a finite prefix, the successive labels follow a finite strongly connected graph of recurring transitions. At any limit other than $1/2$, the next limit is uniquely determined by the homogeneous forward branch: the translation divided by the mass tends to zero. At $1/2$ the only possible next limits are 0 and 1. The only possible successor of 0 is 0, and the only possible successor of 1 is 1. By strong connectivity the presence of either endpoint would force a constant branch tail. This also excludes $1/2$. Every remaining vertex then has one successor, forcing a periodic cycle of labels and hence branches. We have just excluded such a cycle.

Now suppose a polynomial-and-congruence separator existed. Some single residue class modulo a common modulus contains blank points with infinitely many limiting directions. For each nonzero polynomial test choose its top-degree homogeneous part $Q$. The polynomial $Q(t,1-t)$ has only finitely many zeros. Take an interior limiting direction avoiding all these zeros. On a small closed interval about it, every tested sign is constant for all sufficiently large masses: after division by the leading power of the mass the lower terms tend uniformly to zero. Membership in the separator must therefore be true throughout a whole truncated sector in the chosen class. The lemma puts a halting checkpoint there. If instead blank halts, the first checkpoint itself prevents separation.

This argument also covers the literal phase-labelled return maps. The coordinate changes are finite affine recodings on residue slices, invertible on each slice. Their images preserve the stated class of tests, after fixing any denominator residues. For #724 a separator on the published checkpoints would extend to the normalized ones by adjoining $(3u,1)$ for each retained $(u,u+1)$. Those inserted points are safe whenever their predecessors are safe, and the extension is again a finite affine recoding on a line.

The two variable blocks in a physical checkpoint tape are $(11)^a,1^b$ for #184 and $(11)^{a+1},(11)^{b+1}$ for #724. In each phase a finite-state transducer can therefore write the marked tape word from $X^aY^b$. The inverse image of a context-free language under this encoding is context-free, and its set of exponent pairs is semilinear by Parikh's theorem. Since each pair specifies a unique word in $X^*Y^*$, finite Boolean combinations of tape tests still give semilinear sets of pairs in each phase. A tape separator of this kind would give the checkpoint separator just excluded. [Parikh's theorem](https://doi.org/10.1145/321356.321364)

## No semilinear separator at #184 branch switches

An *era* consists of consecutive updates on one branch until the comparison changes or the machine halts. Here a separator must contain every era start on the blank run and exclude every checkpoint that leads to a halt.

Use the even and odd widths $e=2u+2$ and $o=2v+1$. The halt differences are $e-o=1,3$. During a run, let $M$ initially be the larger width and $m$ the smaller; after $h$ updates their values in those original roles are

$$Y=M-\tfrac12 m3^h+ch+\tfrac12 m,\qquad X=m3^h,$$

with $c=9$ if $e$ was larger and $c=2$ if $o$ was larger. Indeed each step triples the smaller width and changes the larger by the constant $c$ minus the current smaller width. At a switch $X>Y$.

Any linear component of a safe semilinear set must be collinear. Otherwise, for some independent nonnegative period vectors $v_1,v_2$ the component contains $z+\mathbb N v_1+\mathbb N v_2$. Sufficiently far out in a cone strictly between their directions, every point congruent to $z$ modulo $|\det(v_1,v_2)|$ is in that grid: the two coefficients are integral by the adjugate formula and positive by the cone condition. The lemma contradicts safety. One can apply it in $(u,v)$, or after the affine recoding in the corresponding even/odd lattice. Starting an era at any admissible point simply groups finitely many updates; it does not change whether that point eventually halts.

Suppose, then, that the era starts on an infinite blank orbit eventually lay on finitely many rational affine lines. Away from horizontal and vertical lines their limiting directions are interior and rational. On these lines the ratios $M/m$ are uniformly bounded at large mass, so the displayed formula bounds the run lengths uniformly. There is also a uniform bound on how many consecutive such starts can occur: otherwise the finite graph of recurring interior directions and bounded run words would contain a cycle. Along each recurring edge, dividing by the mass gives the corresponding homogeneous trajectory. A cycle would give a rational positive eigenline for a mixed product, excluded above (the changes of sign ensure both letters occur). A trajectory through the homogeneous diagonal would next reach an axis and could not return to an interior direction.

Thus horizontal or vertical lines occur infinitely often. There the smaller width $m$ takes one of finitely many fixed values, and the run length $h$ tends to infinity as $M\to\infty$. From one such start to the next, that long run is followed by a word of bounded length. Fix the two line orientations, the old and new small widths $m,m'$, and this suffix word; there are finitely many possible types. Its affine formula after the long run gives

$$m'=pX+qY+s,\qquad M'=p'X+q'Y+s'.$$

The coefficient matrix is invertible. On a recurring type $q\ne0$, since otherwise $pX+s$ would diverge. Solving for $Y$ gives constants of this type with

$$M=A3^h-ch+C,\qquad M'=B3^h+D,\qquad A,B>0.$$

Positivity follows since $M,M'\to\infty$ and $c>0$. On two consecutive passages the second expression must match the next first expression. Pass to a subsequence fixing both types. Then

$$B3^h+D=A'3^{h'}-c'h'+C'.$$

Dividing by $3^{h'}$ gives $3^{h-h'}\to A'/B>0$. An integer power of 3 converging to a positive finite limit is eventually constant. The exponential terms then cancel exactly, leaving $c'h'=C'-D$, impossible as $h'\to\infty$. This proves the era-start assertion. The nonzero linear correction on **both** arms is essential here; the proof does not give the same era-only conclusion for #724.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
