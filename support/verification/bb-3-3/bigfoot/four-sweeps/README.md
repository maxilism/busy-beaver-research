# Four sweeps of ternary Bigfoot

**maxilism · November 24, 2026**

Start the ternary machine `1RB2RA1LC_2LC1RB2RB_---2LA1LA` at a House checkpoint `B(h,x) = A(h,2x+1,2)`, with nonnegative integer reserve `h` and size `x`. **Four sweeps finish if and only if all four prefix balances are nonnegative.** On success the tape returns to a House checkpoint. On failure the machine halts during the first sweep that attempts a loss from zero.

There is an equivalent test using the net-change table: **require a nonnegative signed final balance, and exclude `h=0` with `x mod 81 ∈ {8,13,32,37}`.** These are the only exceptions in the original `x` coordinate, not in the refined coordinate `y` with `x=2y`. For example, at `h=0, x=8` the arithmetic changes are `0,0,−1,+1`. The third sweep halts; the fourth change restores the *arithmetic* balance to zero but never occurs on the tape.

## The Lean statements

Import `BigfootBridge`. All names below are in namespace `Bigfoot`.

* [One sweep](BigfootBridge/HouseSweep.lean): `encode_house` identifies the initial tape `(12)^h (11)^(2x+1) <A (11)^2` on a blank background, with state A scanning the last left-hand `1`. In the upstream machine's shifted coordinates this is `.A h (2*x) 0`.
* [Four arithmetic steps](BigfootBridge/Arithmetic.lean): `stage_label`, `stage_delta` and `ordered_phase` give the successive residues (odd, odd, even, even) and reserve changes from `x mod 81`. `ghost_four` gives the return size `house x = 256*(x/81) + row (x%81)` in natural-number arithmetic. The 81 representative outputs are calculated from the six one-sweep rules. `house_refined` supplies the `x=2y` convention used in the [spacing paper](../../../../../results/bb-3-3/bigfoot-spacing.pdf).
* [Four physical sweeps](BigfootBridge/FourSweeps.lean): `four_sweeps_iff` says that four applications of the published partial sweep map return `entry (credit h x 4).toNat (house x)` exactly when `Good h x 4` holds. That guard tests the **signed** balances after sweeps 1, 2, 3 and 4. `good_four_iff_net` proves the equivalent four-exception test above. `stage_reaches` and `four_sweeps_reach` prove strictly positive raw-machine reachability for each successful sweep and for the whole block. `four_sweeps_first_underflow` identifies the failed sweep, the preceding successful sweeps and their attained tape, and proves `HaltsFrom` that tape; `four_sweeps_halts` gives halting from the initial checkpoint. `zero_eight` proves the example above.

The equivalence concerns **completion of this block**, not ultimate nonhalting. It gives neither a decision for the blank run nor a correctness proof for the seven-state binary compilation.

## Build and check

With [Elan](https://lean-lang.org/install/) on `PATH`, run from this directory:

```sh
# Optional: download the required mathlib binary cache rather than compile mathlib locally.
lake exe cache get Mathlib.Computability.TuringMachine.PostTuringMachine Mathlib.NumberTheory.LSeries.RiemannZeta Mathlib.SetTheory.ZFC.Basic
lake build
lake env lean BigfootBridge.lean     # print the transitive axiom dependencies
```

`lean-toolchain` pins Lean `v4.35.0-rc4`; `lake-manifest.json` pins the dependencies. Preserve the relative `baselines` and `artifacts` symlinks: once Lake fetches the pinned package, the machine importer reads its tables through these links. The block theorems depend only on `propext`, `Classical.choice` and `Quot.sound`; `stage_label`, `ordered_phase`, `credit_row` and `house_refined` use only `propext` and `Quot.sound`.

## Sources and license

Shawn Ligocki [derived the primitive sweep rules](https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html) from savask's low-level analysis; Matthew House (LegionMammal978) gave the [81-row four-sweep reduction](https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html#alternative-representation). The physical-machine proof uses Google DeepMind's [`cryptids` Bigfoot acceleration](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB33/M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA.lean#L810-L819), whose success and failure clauses apply to every encoded state. Trevor Morris's [`Dyn.step4_block` and `Dyn.step4_legion`](https://github.com/gotrevor/collatz-cryptid/blob/9bdf3ca4213ed3faf09bd0124ecf23e184d97c21/lean/Collatz/Bigfoot/Clock.lean#L293-L353) already verify the arithmetic table at reserve at least two. Those results are a comparison, not an import.

The original proofs and exposition in this package are licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Third-party works and dependencies retain their own licenses, including [`cryptids`' Apache License 2.0](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/LICENSE).
