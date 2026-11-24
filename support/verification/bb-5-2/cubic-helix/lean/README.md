# Kernel-checked results for BB5 machine 4817065

From this directory, with [Elan](https://github.com/leanprover/elan) installed and `lake` on your path, run:

```sh
lake build
```

Elan selects Lean 4.36.0 from [lean-toolchain](lean-toolchain). The project uses only Lean's standard library; there are no external package or certificate dependencies.

The default target [Helix.lean](Helix.lean) imports both results below and
the tape correspondence. Its `#print axioms` audit reports `[propext,
Classical.choice, Quot.sound]` for `WordDFA.not_inductive_separator` and
`[propext, Quot.sound]` for `checkpointSafe` and `Pointed.step_view`. These
are standard Lean principles, not assumptions about the machine or automata.

* **Obstruction.** [`Helix.Obstruction.WordDFA.not_inductive_separator`](Helix/Proof.lean)
  quantifies over all finite DFAs (states numbered by `Fin n`) on the canonical
  tape alphabet. No such language contains blank, is closed under every actual
  nonhalting step, and excludes all immediate halts. `accepts_halt` proves the
  first two conditions force an accepted halt, by two applications of the
  *same* zero-letter period with genuine machine paths in between. [ZeroPeriod](Helix/ZeroPeriod.lean)
  proves the uniform period rather than assuming one. Excluding eventual halts
  is a fortiori impossible under closure.
* **Checkpoint safety.** [`Helix.Obstruction.checkpointSafe`](Helix/Safe.lean)
  proves that no point in the full checkpoint union `S` of the [paper](../../../../../results/bb-5-2/cubic-helix.pdf)
  can reach a halt. `P_rejoin` and `Q_rejoin` give the exact endpoint
  `T [] (1+b+max a c)`. [Paths](Helix/Paths.lean) constructs the diagonal blank
  returns and gap repairs; [BlankSafe](Helix/BlankSafe.lean) proves nonhalting
  from those returns. Neither blank nonhalting nor checkpoint safety is an input.

[Machine](Helix/Machine.lean) is the literal five-state instruction table
(`1RB0RC_1LC0LE_0LD0LB_1RA---_1LB0RD`, `D1` has no successor). It keeps the
scanned bit and two binary stacks; the units bit is nearest the head and
unwritten exterior cells are zero. [HeadTape](Helix/HeadTape.lean) proves the
bijection to finite-support pointed tapes on the integers, identifies precisely
translations, and proves write/shift commutation. [Tape](Helix/Tape.lean)
writes ordinary bits left-to-right with a state marker **before** the head bit,
retaining the head even when it scans zero; `displayedBit` and `displayedEdge`
in [HeadTape](Helix/HeadTape.lean) justify both contents and minimal ends.
[Raw](Helix/Raw.lean) checks entry, down, both up rules, both exits, blank-margin
rules and the final path to `D1` for arbitrary guarded lengths, plus the blank
configurations at exactly 6 and 14 steps.

**Scope.** This is a proof of the *negative* finite-state theorem and the
semantic checkpoint part of the *positive* theorem. It is not a Lean
formalization of rational-transducer interpolation, a proof of the minimum
state count of an ordinary separator, or a Lean reflection of the shipped DFA;
see the separate [finite-automata verification](../automaton-check/README.md).
