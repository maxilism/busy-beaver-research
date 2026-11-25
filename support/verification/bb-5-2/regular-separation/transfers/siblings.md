# Two other blank roots of the cubic helix

**Claim.** Neither [5377178](https://api.bbchallenge.org/machine/5377178) nor [7138511](https://api.bbchallenge.org/machine/7138511) admits an ordinary regular separator. For both, the exact blank orbit is nevertheless a nonregular language recognized by a one-turn nondeterministic one-counter automaton (ε-moves allowed).

## Same transition graph, different initial configuration

| ID | Table, in A–E order, reading 0 then 1 | Image of base `(A,B,C,D,E)` after reflecting the tape | New blank, in base coordinates |
|---|---|---|---|
| 4817065 | `1RB0RC_1LC0LE_0LD0LB_1RA---_1LB0RD` | identity, no reflection | `A0` |
| 5377178 | `1RB0RE_0RC0RA_1LD---_1LA0LB_1RA0LC` | `(D,A,B,C,E)` | `B0` |
| 7138511 | `1RB0LD_1RC0RA_0RD0RB_1LE---_1LB0LC` | `(E,B,C,D,A)` | `E0` |

The substitutions agree on **all ten** instructions, including the missing transition. They preserve halting and span, not the start state. To reflect a canonical word, combine the state and scanned bit into one cell, reverse the cells, rename the state and expand the cell again. This preserves regularity in both directions. Below we work entirely in the base table.

Use the notation and genuine sweep rules of [the regular-separation paper, Lemma 2 and Table 1](https://github.com/maxilism/busy-beaver-research/blob/9d1ff0d58585fe536c9b876e71307bf06f68bfb3/results/bb-5-2/cubic-helix.pdf):

```
T(f,m)   = f (10)^m 1 A0
P(f,b,c) = f D0 (10)^b 0 1^c
Q(f,b,c) = f D00 (10)^b 1^c
```

Exterior blank padding is harmless. A lower-case `b` used **as a marker** means B scans the preceding bit. Write `⇒` for a finite machine path.

## Which diagonal is visited?

Put `w` equal to the empty word for start B and to `10` for start E. At step 7 from B or step 21 from E the machine reaches `T(w0,1)`. Suppose `m≥1`, `m≡1 (mod 3)`, and put `k=m+2`. Entry takes `T(w0,m)` to `P(w10,m+1,1)`. For B this is the published blank-margin entry. For E the common entry row of Table 1 leaves `1001b (10)^m 01`. Pad three zeros on the left and rewrite the marked prefix:

```
0001001b ⇒ 00010 b10 ⇒ 000 b0110 ⇒ D0010110 ⇒ 10D00110 ⇒ 1010D010.
```

These use `01b⇒b10` (B1,E0), `10b⇒b01` (B0,C1), `000b⇒D001` (B0,C0), and twice `D001⇒10D0` (D0,A0,B1,E1). The suffix stays `(10)^m01`, giving the asserted P. The rest uses only the published rules:

```
P(w10,m+1,1) ⇒ Q(w1 0^k,0,k)                  m+1 down sweeps
             ⇒ Q(w1,k,0) ⇒ T(w1,k)              k/3 up sweeps; exit at 0
             ⇒ P(w0,k,1) ⇒ Q(w 0^(k+1),0,k+1)   entry at final 1; k downs
             ⇒ Q(w0,k,1) ⇒ T(w0,m+3)            k/3 ups; exit at 1.
```

Thus each blank orbit visits `Q(w1 0^k,0,k)` for **every positive multiple of three**. The published A-blank diagonal instead has residue one. That change decides what happens when the banks cease to match.

## Why one splice is fatal

Keep the right bank `k` and add `p>0` zeros on the left, with both `k,p` multiples of three. The resulting `Q(w1 0^(k+p),0,k)` runs through `k/3` ordinary up sweeps and the zero exit to `T(w1 0^p,k)`. If `p=3`, Table 1's common entry row leaves `w10001b` on the left. B1,E0,B0,C0 move left to D scanning the first one after `w`, a halt.

Otherwise `p≥6`. Put `h=w1 0^(p−4)`. The four-zero entry and `k+1` downs give `Q(h1 0^(k+2),0,k+2)`. Now `k/3` ups leave **`Q(h100,k,2)`**, not a checkpoint to which the published exit at zero or one applies.

To handle it, put `f=h100` and `j=f(10)^(k+1)`. D0 and `k+1` copies of `A01⇒01A` leave `j1A1`; the right exterior is blank. A1,C0,D0 give `j11A0=T(j1,0)`. Ending-one entry gives `P(j0,0,1)=Q(j0,0,1)` and exit gives `T(j0,1)`. The common entry row now leaves `j01b (10)01`. Apply `01b⇒b10` once and `10b⇒b01` exactly `k+1` times. The marker is now `h100b`. B0,C0 take D to the one of `h100`. Thus **every** left-heavy hybrid of these diagonal words halts, independently of the size of the excess.

An NFA accepting the diagonals must repeat a state at the cut immediately before the transition reading D. Splice the prefix from the larger index to the suffix from the smaller one: the hybrid just proved halting would be accepted. No closure assumption was used. Consequently the state minima of the bounded-induction paper, which *retain global separation*, do not exist for either sibling, at any `W`. If separation is instead required only on inputs of span ≤`W`, the first `floor((W−|w|−3)/6)` diagonals already require that many distinct NFA cut states; every hybrid used has span at most `W`. This is a different predicate.

## What does transfer: the one-turn orbit description

The two T families in the return above are regular. The P/Q sweep endpoints are exactly the following families, with `k` ranging over `3,6,9,…`:

| Endpoint | Conditions |
|---|---|
| `P(w1 0^a,b,a)` | `a≥1, b≥0, a+b=k` |
| `Q(w1 0^a,b,a)` | `a,b≥0` both divisible by 3, `a+b=k` |
| `P(w 0^a,b,a)` | `a≥1, b≥0, a+b=k+1` |
| `Q(w 0^a,b,a)` | `a≥1, b≥0, a≡1, b≡0 (mod 3)`, `a+b=k+1` |

This is a list of *actual* endpoints, not merely safe starting points: the down sweeps enumerate the P rows one unit at a time and the ups the Q rows three units at a time. Eliminating `k` leaves a lower bound and residue test on `a+b`. Guess a row and count up on the `a` zeros and down on the `a` ones; all other tests are finite-state. Canonical trimming, including invisible leading zeros for empty `w`, is a rational image. As in [the state-cost paper, Theorem 3](https://github.com/maxilism/busy-beaver-research/blob/ca93284968d77df7b9ee70d5a5a3c008fcb07c4f/results/bb-5-2/cubic-helix-state-complexity.pdf), one sweep uses boundedly many single steps and homogeneous scans. Even the special entry adds only a constant ending. A prefix within a scan takes the completed copies and at most three further steps. A fixed finite composition of the genuine rational step/scan relations with identity therefore covers every intermediate point from those endpoints and cannot leave the orbit. Add finite startup. Rational images preserve this one-turn nondeterministic counter construction. In the reflected orientation, compare the two banks in the opposite order; reversing *both tracks* of each transducer is accomplished by reversing its paths on atomic cells. Finally, regularity of an orbit would make it an ordinary regular separator, which the splice has ruled out.

**Provenance and checks.** The three [Blanchard weighted certificates, lines 85–102](https://github.com/Iijil1/MITMWFAR/blob/3937731f9e1d801d6f6d77cf44787f93fc1ffc76/SolvedFullCerts.txt#L85-L102) and their [Coq table encodings](https://github.com/ccz181078/Coq-BB5/blob/9142e219229baf2245d3f70851947230ea28a318/CoqBB5/BB5/BB5_Deciders_Hardcoded_Parameters/Verifier_WFAR_Hardcoded_Certificates.v#L83-L96) establish prior nonhalting work; they are not proofs about ordinary separators. [Georgiev's 3N list](https://skelet.ludost.net/bb/nreg.html) has the historical machines; [Blanchard's holdout discussion](https://discuss.bbchallenge.org/t/the-30-to-34-ctl-holdouts-from-bb-5/141/1) describes an *expected* obstacle. No prior ordinary classification of the two siblings was found in the sources checked. The guard and halt proof above were independently rederived and checked against the literal table. `python3 -IB check-siblings.py` additionally checks 24 ordered checkpoints and 91 left-heavy halts **per sibling** directly in the two named tables. Those finite tests are corroboration, not the proof for all lengths.
