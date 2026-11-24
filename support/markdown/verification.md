# Reproducing the proofs and finite checks

Run each command block from the repository root. The Python scripts use the standard library; leave assertions enabled.

## BB(3,3)

The Bigfoot check reproduces the change of input at checkpoint 49 and checks 1,728 three-block residue calculations.

```sh
python3 support/verification/bb-3-3/bigfoot/bigfoot-spacing-check.py
```

For the Lean proof of Bigfoot’s four-sweep return criterion, see the [package and build instructions](../verification/bb-3-3/bigfoot/four-sweeps/). With Elan installed:

```sh
cd support/verification/bb-3-3/bigfoot/four-sweeps
lake build
```

For #758 and #153, these scripts check guarded predecessors, conditional running times, and the two machines’ common future.

```sh
python3 support/verification/bb-3-3/ternary-entry/back-wall.py
python3 support/verification/bb-3-3/ternary-entry/clock758.py
python3 support/verification/bb-3-3/ternary-entry/twin758.py
```

To reproduce the finite entry calculation on a little-endian system, compile the enumerator with a C++17 compiler supporting 128-bit integers. Keep assertions enabled. The output contains 16,000,001 unsigned 16-bit return increments. The entry check computes the predecessor labels from those increments.

```sh
cd support/verification/bb-3-3/ternary-entry
g++ -O3 -std=c++17 basin758.cpp -o basin
./basin 16000000 returns.bin
python3 entry-audit.py returns.bin
```

## BB(5)

The [cubic helix checker](../verification/bb-5-2/cubic-helix/) regenerates the separator automaton, compares it with the supplied transition table and finds an accepted configuration whose successor is rejected. This witness concerns the supplied automaton; the [paper](../../results/bb-5-2/cubic-helix.pdf) rules out every regular inductive separator.

```sh
python3 support/verification/bb-5-2/cubic-helix/check-dfa.py
```

## BB(6)

For #184, the script compares the arithmetic updates with the published return rule on a finite grid and checks consecutive runs of updates from the blank launch. The options below give a short run.

```sh
python3 support/verification/bb-6-2/184/184-check.py --limit 80 --eras 100
```

For #623, the [two block-sieve checkers](../verification/bb-6-2/623/) verify the finite minima used in the [predecessor-density bound](623-predecessor-density.md).

```sh
cd support/verification/bb-6-2/623
python3 digit-masks.py
python3 blocks-check.py
```

## BB(7)

The first Jacobzheng script compares the checkpoint formulas with literal tape transitions. The second enumerates all 351 single-instruction changes and prints the classification for each one.

```sh
python3 support/verification/bb-7-2/jacobzheng/second-check.py
python3 support/verification/bb-7-2/jacobzheng/jacob-sphere.py --list
```

For the tape-restoring detours, each manifest records the seven-state table and its five-state reduction. The row numbers refer to the historical files identified in the paper. [Scan manifest](../data/bb-7-2/restoring-detours/restoring-shadow-crosswalk.tsv) · [Toggle manifest](../data/bb-7-2/restoring-detours/toggle-crosswalk.tsv)

## One-sided two-state machines

The [proof bundle](../verification/families/two-state-halting-times/proof-bundle.zip) contains the rational certificates and the partition of all 4,096 tables. The [independent replay](../verification/families/two-state-halting-times/independent-replay.zip) reconstructs the partition and checks the time bounds. Extract the archives into **separate** directories: each has its own `two-state/` directory.

In the proof bundle’s `two-state/` directory, run `python3 marked-replay.py`, `python3 six-edge-prefix.py`, `python3 coverage.py` and `python3 small-corollary.py`. In the independent archive’s `two-state/` directory, run `python3 all-replay.py`. The [paper](../../results/families/two-state-halting-times.pdf) gives the archive digests and explains how the finite checks give bounds for arbitrary input width.
