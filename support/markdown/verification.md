# Reproducing the finite checks

Run each command block from the repository root. The Python scripts use the standard library.

## BB(3,3)

The Bigfoot check reproduces the change of input at checkpoint 49 and checks 1,728 three-block residue calculations.

```sh
python3 support/verification/bb-3-3/bigfoot/bigfoot-spacing-check.py
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

## BB(6)

For #184, the script compares the arithmetic updates with the published return rule on a finite grid and checks consecutive runs of updates from the blank launch. The options below give a short run.

```sh
python3 support/verification/bb-6-2/184/184-check.py --limit 80 --eras 100
```

## BB(7)

The first Jacobzheng script compares the checkpoint formulas with literal tape transitions. The second enumerates all 351 single-instruction changes and prints the classification for each one.

```sh
python3 support/verification/bb-7-2/jacobzheng/second-check.py
python3 support/verification/bb-7-2/jacobzheng/jacob-sphere.py --list
```

For the tape-restoring detours, each manifest records the seven-state table and its five-state reduction. The row numbers refer to the historical files identified in the paper. [Scan manifest](../data/bb-7-2/restoring-detours/restoring-shadow-crosswalk.tsv) · [Toggle manifest](../data/bb-7-2/restoring-detours/toggle-crosswalk.tsv)
