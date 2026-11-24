# Two tape-restoring detours in 721 seven-state machines

maxilism

Two instruction patterns reduce 721 machines in a [historical BB(7) holdout list](https://drive.google.com/file/d/16gPFf6O5oz-JVFiDq43Hxe2AVTqX4VqX/view) to 33 five-state machines. In the first pattern a pair of helper states repaints a run of arbitrary length and retraces it. In the second, the helpers visit two adjacent cells twice. Deleting the helpers works because the head, tape and state on return agree with those after a single instruction in the reduced machine. All 33 reduced machines run forever from blank. Of the 721 machines, 49 also inherit known obstructions to a regular-language proof of this fact.

## Deleting two helper states

Use a two-way binary tape, initially all zeros; count the final halt instruction as a step. Call two non-start states $E,F$ and the other five states the core. Fix a bit $a$, its complement $b=1-a$, a direction $d\in\{-1,+1\}$, and a core state $G$. Every core instruction entering a helper must write $a$ at its cell $x$, move to $y=x+d$ and enter $E$. Form the **shadow** by redirecting each such *call* to $G$ without changing its write or move, then deleting $E,F$. The following table gives two sufficient helper patterns; each entry lists (write, direction, next state). In the toggle pattern $\sigma$ is either the identity or bit complement.

| Pattern | $E$ on $a$ | $E$ on $b$ | $F$ on $a$ | $F$ on $b$ |
|---|---|---|---|---|
| Restoring scan | $(b,d,E)$ | $(b,-d,F)$ | $(a,d,G)$ | $(a,-d,F)$ |
| Two-cell toggle | $(\sigma(a),-d,F)$ | $(\sigma(b),-d,F)$ | $(b,d,E)$ | $(a,d,G)$ |

For the scan, suppose the tape from $y$ in direction $d$ begins $a^k b$. State $E$ repaints all $k$ copies of $a$ with $b$, turns on the original $b$ without changing it, and sends $F$ back across the repainted cells. State $F$ restores them to $a$ until it meets the caller's $a$ at $x$. It then enters $G$ at $y$. This works when $k=0$, and the total cost including the call is $2k+3$. If no $b$ occurs, $E$ never turns. In the toggle pattern the successive cells visited after the call are $y,x,y,x$. The second visit to $y$ restores its bit because $\sigma^2$ is the identity. On its second visit to $x$, $F$ finds the flipped marker, restores $a$, and enters $G$ at $y$. This call always returns and costs five steps.

Consequently each returning call has the effect of one shadow step. A halting seven-state run cannot have a nonreturning call, so it projects to a halting shadow run. For the toggle the converse also holds. For a scan of zeros a missing one ahead can make the converse false.

Let $T$ be the number of shadow steps in a projected blank halter. Before step $j$, numbered from one, the shadow has written at most $j-1$ ones. Thus a scan of ones costs at most $2j+1$. For a returning scan of zeros, the delimiter is a previously written one; it and $x$ lie in the shadow's visited interval of at most $j$ cells. Again $k\le j-1$ suffices. Summing over $j$ gives at most $T(T+2)$ steps. The toggle clock is $T+4c\le5T$, where $c$ counts calls. By the [fifth Busy Beaver theorem](https://arxiv.org/abs/2509.12337), $T\le B=47{,}176{,}870$. The two blank-halting cutoffs are therefore $B(B+2)=2{,}225{,}657{,}157{,}350{,}640$ and $5B=235{,}884{,}350$ respectively.

## Finite check on the shadows

For example, row 14,424,682 of `7x2_holdouts_15743264.txt` has table

```
1RB1RE_1LC1RB_0RA0LD_1LB1LD_0LF0RE_1LF1RG_---0RA
```

Groups are states `A` through `G`, with the zero instruction first. The call `A1:1RE` invokes a scan; at primitive steps 7, 29 and 77 the run invokes lengths 1, 3 and 5. Redirect the call to `G`, remove `E,F` and rename the old `G` to `E`. The shadow is `1RB1RE_1LC1RB_0RA0LD_1LB1LD_---0RA`. After $B$ nonhalting steps its state is `D`, the head is at $+20$ from the start, and the tape contains 870 ones. The bound $B$ makes that finite check conclusive for the shadow and hence for the original machine.

The [scan manifest](../data/bb-7-2/restoring-detours/restoring-shadow-crosswalk.tsv) and [toggle manifest](../data/bb-7-2/restoring-detours/toggle-crosswalk.tsv) give the input rows, helper pairs and reduced tables. To reproduce the tests, enumerate ordered pairs of non-start helpers; require at least one core call, and test every entry from the core to either helper and all four helper instructions against the pattern. Relabel the remaining states consecutively in their original order and simulate each distinct resulting table for $B$ steps on blank. All 33 complete that many nonhalting steps. Within the 15,743,264-row snapshot (uncompressed SHA-256 `f9bc059b9851e512790714040b88d0aac99133d07e36929198da1ee97a0eba9c`), the two patterns select disjoint sets of literal seven-state tables and give exactly the same set of 33 literal shadows.

| Pattern | Passing helper pairs | Distinct seven-state tables | Also on the later solved-infinite list |
|---|---:|---:|---:|
| Scan | 215 | 203 | 50 |
| Toggle | 518 | 518 | 139 |
| Combined | 733 | 721 | 189 |

The last column compares exact table strings with [one later public file of 3,050,135 machines](https://drive.google.com/file/d/13D8EkcpcfBjVc_M47KAycUhdIIxbrDIZ/view). The other 532 are absent from that file. The comparison does not establish when each machine was first decided.

## What the reduction transfers to tape languages

Write a tape as a finite word trimmed of exterior zeros, up to translation, with the scanned cell marked by its state. A *separator* contains every word reached from blank and excludes every word from which the machine eventually halts. If all helper calls return on all finite-support tapes, the reached and halting inputs at core boundaries include, respectively, the renamed reached and halting inputs of the shadow. A regular separator of the seven-state machine would restrict to a regular separator of the shadow: intersect with the words marked by core states, then rename those states. A toggle and a scan of ones both satisfy the return hypothesis. A scan of zeros needs a separate argument.

Two shadows have no regular separator. On [Iijil’s witness slice for Finned #3](https://discuss.bbchallenge.org/t/10756090-finned-3-is-irregular/137), $C(n,m)=(10)^n[A0]1^m$, blank reaches every $C(n,n)$ and every off-diagonal pair halts. For [Skelet #17](https://wiki.bbchallenge.org/wiki/Skelet_17#Irregularity), [Daniel Yuan and Justin Blanchard’s irregularity result](https://arxiv.org/pdf/2509.12337v2#page=43) uses infinitely many reached words $L_nR_n$ such that $L_mR_n$ leads to halt whenever $m<n$. [Yuan’s construction](https://discord.com/channels/960643023006490684/1082035052961091705/1269022847502647357)

| Shadow | Toggle | Scan ones | Scan zeros | Copies with no regular separator |
|---|---:|---:|---:|---:|
| Finned #3 | 20 | 7 | 2 | 29 |
| Skelet #17 | 16 | 4 | 0 | 20 |

The two zero scans are rows 14,424,496 and 15,538,865. They detour `E1`, and both `C0` and `E1`, respectively, in Finned's five-state labeling. It suffices for these calls to return on the slice $C(n,m)$. Here `B` crosses the right run of ones and `B0` leaves an extra one at its right end. In each of the following $n$ repairs `C1` makes a temporary zero, `D` runs left to fill the next zero of a left pair, and `B` runs right to fill the temporary zero. The final left pass fills two cells beyond the old pairs and brings `C` to a blank. Its `C0` call has a one immediately to the right, just written by `B0`. After `C0` the tape consists of $n+m+2$ ones, a gap, and $n+1$ ones. The `A,E` sweep reaches the gap before the extra rightmost one, which therefore delimits every `E1` detour. This covers $n=0$ or $m=0$ and proves return throughout the witness slice; it need not hold on every input.

For the 29 Finned copies one can go further: the **exact language of blank-reached words is context-free**. Here are the three sets of checkpoints that generate it in the shadow. At the diagonal start use $C(n,n)$. During its $i$th repair, $0\le i\le n$, the unprocessed pairs, filled run, and cells to the right of the head give

$$(10)^{n-i}1^{n+i}[C1]1^{i+1}
 = \underbrace{(10)^l1^l}_{\text{first factor}}\;\underbrace{1^{2r}[C1]1^{r+1}}_{\text{second factor}},
 \qquad l=n-i,\quad r=i.$$

Every $l,r\ge0$ occurs: take $i=r$ and $n=l+r$. The two factors are context-free separately, by matching one pair to one bit in the first, and two bits to one (plus the final one) in the second. Independence of $l$ and $r$ makes the repair language their concatenation. The third checkpoint is $[C0]1^{2n+2}0\,1^{n+1}$. Its two run lengths are in ratio two to one, so it too is context-free.

Between these checkpoints take guarded prefixes of the actual instructions: `A0 B1* B0` from the diagonal; `C1 D1* D0 B1* B0` from each repair; `C0` followed by the rightward alternating `A1,E1` sweep from the final checkpoint. For a monotone scan, the relation between input and output words is finite-state: align the cells with zero padding, check unchanged cells outside the scanned interval, and verify the successive reads, writes and endpoint states inside. This also works for a prefix, and for a leftward scan by reversal. Context-free languages are closed under rational transductions [by Nivat’s Theorem 1, p. 413](https://www.numdam.org/article/AIF_1968__18_1_339_0.pdf#page=76). The parameterized middle checkpoint handles all repairs, so no unbounded number of compositions is needed. Every accepted prefix starts at a visited checkpoint and follows a real run, giving exact reachability. In each seven-state copy add the prefixes of helper calls from the appropriate marked core words. A scan has only the outward and return sweeps; a toggle has bounded length. These relations again preserve context-freeness. No corresponding context-free upper bound is asserted for the 20 Skelet copies.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
