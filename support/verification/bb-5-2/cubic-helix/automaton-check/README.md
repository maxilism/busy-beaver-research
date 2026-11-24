# All-length check of the shipped 176-state automaton

From this directory, run:

```sh
python3 -B check.py
```

This Python 3 checker uses only the standard library and the adjacent [published DFA](../dfa.json). It reads that file relative to the script, not the working directory. To specify a copy, supply its path as the only argument; its SHA-256 must still match. Leave assertions enabled (no `-O`). The checker uses its own [finite-automata engine](fa.py), not the extractor that generated the published DFA.

**Result.** The DFA `D` in the file with SHA-256 `123cdce7aaa1a27daa78cd2ee04c8c02de3dafe5043f4c2eef766a7fdd938b4d` accepts exactly the independently specified language `H` below. The two language inclusions exhaust the reachable comparison graph in each direction, **over all words over `01ABCDE`**, not just valid configurations, and not just up to a cutoff. Each graph has 176 reachable pairs in the one-sided (left live) search. Four domain checks and four synchronous two-track inclusion checks establish the complete input/output relations required to cover the blank cycle. The ordinary separator property follows from these checks, the short trajectory argument below and safety of the broad checkpoints (the mathematical lemma identified below). No assertion of forward closure.

## What the shipped language is compared to

Represent every cell by one symbol, plain `0`, `1`, or decorated `[q:x]`. One step rewrites a pair of adjacent cells synchronously. Read `[q:x]` as `qx` when returning to the JSON's alphabet. In the formulas below `A` precedes the scanned bit; the shorthand `b` follows the bit scanned by B. The programs operate on windows including **seven physical blank cells on each side of the source**; no stage pads or trims mid-program. The head always remains inside. On a fresh macro invocation recenter with fresh padding; the underlying infinite tape is unchanged by this re-windowing.

Use the following three source families (exponents nonnegative, residues mod 3).

```
R(m)       = (10)^m 1 A0                 m = 2 mod 3
K(a,b,c)   = 1 0^a 1 A(10)^b 0 1^c      a,c>=1, a+b = c+b = 1 mod 3
U(a,b,c)   = 1 0^a 1 A(01)^b 0 1^c      a ≡ c ≡ 1, b ≡ 0 (mod 3)
```

These K and U are **one real `D0` step after** the corresponding `P(10^a,b,c)` and `Q(10^a,b,c)` of the [regular-separation paper, eq. (2)](../../../../../results/bb-5-2/cubic-helix.pdf); `0(10)^b = (01)^b0`. Each exponent ranges independently subject to the stated inequalities and congruences. The diagonal `a=c` is *not* imposed on the source language.

Use the three repeatable local paths `X: A01 → 01A`, `Y: 01b → b10`, `Z: 10b → b01`. A star on **one path** may take any number of copies (including zero), not necessarily a maximal scan. The four programs, in execution order, are

| source | stages |
|---|---|
| R | `A00→b01`, `Y*`, `Y`, `000b→1A01`, `X` |
| K | `A10→1A0`, `X*`, `A00→b01`, `Y*`, `11b→01A` |
| U | `X*`, `A11→0b0`, `Z*`, `000b→1A01` |
| U | `X*` |

Define `Cuts` as **all outputs after zero or more initial stages of any one program**. In particular, partial stars and early stops count; a later stage need not succeed. `H` is the union of (i) blank times 0 through 14 and (ii) the words obtained by taking zero to three exact ordinary steps from a cut, staying within the window, and **then** canonically encoding the result. To canonicalize, remove only leading/trailing plain `0` cells, retain every decorated cell including a decorated zero, then expand `[q:x]` to `qx`.

Every star is represented directly as a language of paired cells in plain unchanged contexts. E.g. `X^j` with `j>0` pairs `A(01)^j x` with `(01)^j Ax`; `Y^j` pairs `x(01)^j b` with `xb(10)^j`, for either bit `x`. `Z` interchanges `01` and `10` in this latter formula. The zero case uses identity; the source at the star is always in the correct head state. By factoring the repeated block, these paired words are exactly successive copies of their atoms. The eight atoms are replayed in the checker from the raw transition table, for all values of any adjacent endpoint bit, verifying the entire path stays inside the minimal footprint. Each takes at most four steps. Thus every cut and every extra step thereafter is a genuine successor of its phase source. The blank prefix is also obtained by raw steps, ending in `10101A0`.

**Safety:** given that *every* R, K and U above is safe, `H` consists of safe words; the forward direction is important. This premise for the broad, independently variable exponents is mathematical, not inferred by DFA equality or by a blank-only certificate. In the paper it follows from the diagonal return and the regular checkpoint repair lemma: a listed P does its down sweeps to a listed Q; exhaust the up sweeps (using the blank-margin variant if right excess persists); after exit the left gap `g=max(1,a-c+1)` can be shortened by 3 per repair while increasing the alternation exponent by 3, down to a diagonal return. See Lemma 3 of the paper. This program verifies the specific blank-cycle endpoint obligations below, **not** every off-diagonal repair or blank-margin rule. Use the checkpoint proof for that input. The companion Lean artifact proves the premise for S: [`Helix.Obstruction.checkpointSafe`](../lean/Helix/Safe.lean) (see `Checkpoint`, `Q_rejoin`, `P_rejoin` in the same file). The conversion to our K/U regular expressions by the one `D0` step and the bridge from its tape model to these Python finite-state computations are mathematical identifications, not Lean theorems about the JSON.

## Coverage is checked differently from safety

Merely showing that each phase has some safe outputs, or that its output *language* intersects the next checkpoint set, is not enough. Here `prescribed_returns()` writes each of the following **paired** source/target word relations independently of the executable programs:

| phase | paired requirement (same underlying window on both tracks) |
|---|---|
| entry | `R(m) → K(1,m+1,1)` |
| down | `K(a,b,c) → K(a+1,b−1,c+1)` for `b>=1` |
| ordinary up | `U(a,b,c) → U(a−3,b+3,c−3)` for `a,c>=4` |
| exit | `U(a,b,1) → 1 0^a 1(01)^(b+1) A0` |

Every source in the table is restricted to its full regular source family as above. Entry takes four of the seven left blank cells and one right blank cell into the new active word. Exit extends the active word by one scanned blank. For down and ordinary up both endpoints are on the same active span. There is no assumption that resets of padding consume machine steps. A paired generator repeats specified **pairs of chunks together** (bounded length lag before synchronization), so the tested relations keep correspondence between unbounded exponents — they are not products of uncorrelated pre/post languages. For example the variable `b−1` in the down row contributes `(10,10)*` at offsets that may differ on the two tracks; `pair_spec()` buffers the lag and emits aligned pairs of physical cells. See the four compact expressions in `prescribed_returns()`. `phase_domains()` independently specifies all valid left tracks to check none are missed. In the up statement, every `U` required on the blank up pass has `a=c`; **we do not require a `Z*` program to cover the exceptional blank-margin sweep from `a=1,c>1`**, which is unnecessary for blank coverage and relevant only to off-diagonal checkpoint safety.

Each program composition is a DFA on **pairs** `(source cell, current cell)`; initially this is identity on its source. To compose with a stage, synchronize `(x,y)` and `(y,z)` on physical cells and emit `(x,z)`, then determinize. For each row the checker verifies the intended domain is contained in the left projection of the requirement and the entire paired requirement is contained in the resulting program relation. The four successful paired graph searches exhaust respectively 21, 50, 32 and 25 reachable comparison pairs. The inclusion directions are intentional: extra genuine paths do not harm safety. There is no claim that the unrestricted `U` program, for example, produces *only* desired complete blank-sweep endpoints.

Starting at `R(2)` at step 14, entry from `R(m)` lands at `K(1,m+1,1)`; `m+1` down passes end in `K(m+2,0,m+2)=U(m+2,0,m+2)`. Then `(m+1)/3` ordinary up passes end in `U(1,m+1,1)`; the exit lands at `R(m+3)`. The guards in the table hold at each required invocation. This iterates forever; the distinct endpoints ensure the covered times are unbounded. By the paired inclusions every required transition has a witness execution in the program. The machine is deterministic. Every intermediate *ordinary* state of such an execution is accounted for: stage endpoints belong to `Cuts`; at a star interruption use just the completed copies to get a cut; inside a remaining atom take at most three single steps from its preceding cut. Raw steps on the complete paths stay within the very windows used. Thus every blank time belongs to `H`. **Blank coverage** uses these paired languages and this induction, not a sampled run and not just `D⊆H`.

## Relation to the broader construction

The paper's rational relation `F` includes identity, a real step and each of the three stars `α*`, `β*`, `γ*` of the *paper* (γ uses state C). The precise comparison is `D = H ⊊ I ∪ F^18(S)` for this shipped JSON; only `D = H` is checked by the two DFA inclusions. For the upper inclusion, `X*` and `Y*` are `α*` and `β*`. For `j>=1`, `Z^j` has read pairs `B0, (C1 B0)^(j−1), C1`; the middle is `γ*`, so this costs at most **three** `F` factors, not necessarily one. From S, K/U cost one initial `D0` step. Counting the ordinary steps in nonstar stages, the stars as above, and the three possible tail steps gives upper bounds 16 (entry), 15 (down), 13 (up), 5 (exit); truncated paths at earlier cuts cost no more, and identities fill any unused factors. This comparison is on canonical configurations, where finite window paths are valid. For strictness, `Q(10,0,4)=10D001111` belongs to S and hence to `F^18(S)`, but the shipped DFA **rejects** it (and accepts its `D0` successor `101A01111`). The checker replays these two membership decisions. No equivalence with a weighted certificate or containment in its invariant is used.

## Trust boundary and mechanics

The proof combines mathematical specifications/arguments above with executable checks, not a proof-assistant certificate for the Python evaluator. Trusted: the target machine table and tape convention; the broad-checkpoint safety lemma; the stated finite-state constructions, Python/stdlib, and their implementation in the two short scripts. Verification uses reachable ε-closed subset construction for nondeterminism, liveness trimming then partition refinement for small equivalent DFAs, and full reachable-product searches for differences (implicit rejecting sink). A failed inclusion reports a shortest witness. Equality is a language-level check against the actual JSON read at run time; the state numbering of the reconstructed automata is irrelevant. The engine and the head-decorated synchronous program/endpoint relations are independent of the shipped extractor's gap-marker image implementation.
