# Busy Beaver research

The [results](results/) use BB(n,k) for n states and k symbols, or BB(n) for binary machines. [Machine families](results/families/) are listed separately. The [supporting material](support/) includes derivations, verification code, data, and Markdown sources.

## Highlights

- With at most one left-moving nonhalting instruction in its table, a 7-state binary machine that halts from blank takes fewer than $2^{251}$ steps, even if it uses that instruction repeatedly. [Running-time bound](results/families/one-left.pdf)
- For both binary Bigfoot and Jacobzheng’s machine, every context-free language of marked tapes that contains the whole run from blank also contains a configuration from which the machine halts. [Context-free tape separators](results/bb-7-2/certificate-barriers.pdf)

## BB(3,3)

| Paper | Result |
|---|---|
| [Factor complexity of Bigfoot’s exact rows](results/bb-3-3/bigfoot-complexity.pdf) | On the arithmetic continuation from blank, the number of distinct blocks of length $m$ grows faster than any constant multiple of $m$. |
| [Spacing of prescribed reserve changes in Bigfoot](results/bb-3-3/bigfoot-spacing.pdf) | Fix $A>0$. In the arithmetic model, every word of length $L$ over the reserve changes from −2 to +3 occurs in every interval of $\lceil C_A 81^L/L^A\rceil$ consecutive nonnegative starting sizes, with $C_A$ depending only on $A$. |
| [Entry into a halting interval for #758 and #153](results/bb-3-3/ternary-entry.pdf) | From 3,732,721 consecutive starting values, #758 first crosses the lower edge of the halting interval in the same configuration and then halts. Whether the blank run enters the interval is open. [Conditional timing calculation](support/derivations/ternary-capture-clock.pdf) |

[Bigfoot’s four-sweep return (Lean)](support/verification/bb-3-3/bigfoot/four-sweeps/). A block halts if its signed final reserve is negative. The only other halting blocks start with zero reserve and an original House size congruent to 8, 13, 32 or 37 modulo 81.

[Verification code](support/verification/bb-3-3/) · [Private prime factors of Bigfoot checkpoint sizes](support/markdown/bigfoot-private-primes.md)

## BB(5)

| Paper | Result |
|---|---|
| [Regular separation for the seventeen weighted BB(5) machines](results/bb-5-2/regular-separation.pdf) | All seventeen lack a regular inductive separator. Only #4817065 admits an ordinary regular separator. For the other sixteen, separation through input span $W$ takes $\Theta(W)$ states. [Lean proofs and replay files](support/verification/bb-5-2/regular-separation/) |
| [Regular separation for the cubic helix](results/bb-5-2/cubic-helix.pdf) | For machine 4817065, a regular language contains the blank orbit and excludes every configuration that eventually halts. No such regular language is closed under machine steps. [Automaton, proofs, and checks](support/verification/bb-5-2/cubic-helix/) |
| [The state cost of bounded induction for a five-state cubic helix](results/bb-5-2/cubic-helix-state-complexity.pdf) | For machine 4817065, separating the blank orbit from all eventually halting configurations takes $\Theta(W)$ states for both deterministic and nondeterministic finite automata when step closure is required from every accepted source of span at most $W$. |

## BB(6)

| Paper | Result |
|---|---|
| [Arithmetic invariants for #184 and #724](results/bb-6-2/six-state-invariants.pdf) | Suppose a test on the two counters accepts every checkpoint on the blank run. If the test is built from finitely many polynomial inequalities and congruences modulo fixed integers, it also accepts a checkpoint that leads to a halt. The same holds for finite Boolean combinations of context-free languages on marked tapes. |
| [Return rules for #623](results/bb-6-2/six-state-623.pdf) | At each sampled return from blank, a halting inner branch requires the two counters to lie within a logarithmic distance of each other. |
| [Parents and grandparents of fatal checkpoints for #623](results/bb-6-2/623-predecessor-density.pdf) | For one family of halting targets indexed by even $t$, the parameters admitting a parent under the sampled return map have relative density $1/3$ among even parameters. Among targets with a parent, the lower relative density of those without a grandparent is at least $70/729$. [Source](support/markdown/623-predecessor-density.md) · [Finite checks](support/verification/bb-6-2/623/) |
| [Halting inputs for Antihydra](results/bb-6-2/antihydra.pdf) | At fixed reserve, every arithmetic progression of sizes contains a subprogression of halting inputs, with an explicit bound on the number of return-map attempts. |
| [Multiplicative independence in machine 66813](results/bb-6-2/66813-rank.pdf) | Each of the 1,567 digit-map terms in level 1 introduces a prime absent from the earlier terms, so they are multiplicatively independent. [Source](support/markdown/66813-rank.md) · [Finite check](support/verification/bb-6-2/66813/check.py) |

[Finite checks for #184](support/verification/bb-6-2/184/184-check.py)

## BB(7)

| Paper | Result |
|---|---|
| [Certificate obstructions for Bigfoot and Jacobzheng](results/bb-7-2/certificate-barriers.pdf) | For either machine, an inductive safety certificate that contains the blank checkpoint and is closed under adding reserve needs at least linearly many size intervals as the reserve grows. |
| [Changing one instruction in Jacobzheng](results/bb-7-2/jacob-neighbors.pdf) | Of 351 neighbors, 176 halt and 172 run forever. Each of the other three halts exactly when the original does. |
| [Comparing Jacobzheng size trajectories](results/bb-7-2/jacob-size.pdf) | Among all positive starting sizes, 2 (the blank start) gives the smallest value after each iteration. From a checkpoint with at least four units of reserve, the machine runs forever if another size trajectory stays within a bounded distance of its own. [Sweep and companion calculations](support/derivations/jacob-derivations.pdf) |
| [Two tape-restoring detours](results/bb-7-2/restoring-detours.pdf) | Deleting two helper states reduces 721 machines from a historical BB(7) holdout list to 33 five-state nonhalters. |

[Jacobzheng verification code](support/verification/bb-7-2/jacobzheng/) · [Seven-to-five-state reduction data](support/data/bb-7-2/restoring-detours/)

## Machine families

| Paper | Result |
|---|---|
| [Blank running time with one left instruction](results/families/one-left.pdf) | With $n$ states and at most one left-moving nonhalting instruction, a binary machine that halts from blank takes at most $2^{O(n^2\log(n+2))}$ steps. |
| [Two-state machines on finite input](results/families/two-state-tail.pdf) | On a two-way tape with a halt instruction, one transition pattern attains quadratic time in the input width, up to reflection and renaming. Every other table takes linear time or less on halting inputs. |
| [Longest halting times on a one-sided tape](results/families/two-state-halting-times.pdf) | Start at the edge and count the move off the tape as the final step. For binary inputs of width $n\ge5$, the maximum over halting runs of the 4,096 two-state tables is $2^{n+2}-3$ steps. Only rules 378 and 1351 attain it, both on the all-ones input. [Certificates and independent replay](support/verification/families/two-state-halting-times/) |

[How to reproduce the checks](support/markdown/verification.md) · [Markdown sources](support/markdown/)

## License

© 2026 maxilism. Original material in this repository is licensed under the [Creative Commons Attribution 4.0 International license](LICENSE).
