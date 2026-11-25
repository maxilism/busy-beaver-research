# Regular separation on the seventeen weighted BB(5) machines

The [paper by maxilism](https://github.com/maxilism/busy-beaver-research/blob/main/results/bb-5-2/regular-separation.pdf) classifies regular separation for the seventeen machines with direct weighted-automaton certificates in the BB(5) proof. Lean checks the classification and the lower bounds. The finite certificate and census calculations have separate replay programs.

[Download the standalone proof bundle](https://github.com/maxilism/busy-beaver-research/raw/refs/heads/main/support/verification/bb-5-2/regular-separation/lean-proof.zip) or [browse the Lean classification](transfers/formal_review/SeventeenClassification.lean) and [width bounds](transfers/formal_review/WidthCases.lean).

Use Lean 4.36.0 (Elan toolchain `leanprover/lean4:v4.36.0`) and Python 3.10 or later. The Lake packages use Lean’s standard library. Run the following from this directory or from the root of the unpacked bundle.

```sh
cd transfers/formal_review
lake build
lake env lean SeventeenClassification.lean
lake env lean WidthCases.lean
python3 -IB check_catalog.py ../../data/SolvedFullCerts.txt
python3 -IB check_positive_dfa.py ../../data/dfa.json
python3 -IB check_positive_weight_data.py
python3 -IB ../check-weighted-suffixes.py ../../data/SolvedFullCerts.txt
python3 -IB check_seven_state_census.py ../../data/toggle-crosswalk.tsv ../../data/restoring-shadow-crosswalk.tsv ../../data/SolvedFullCerts.txt
python3 -IB ../check_skelet17.py
```

* `SeventeenClassification.classification` proves that #4817065 is the unique ordinary positive among the seventeen indexed machines, and that each of them lacks an inductive regular separator. `ReviewedCases.distinctSeventeen` verifies the count and distinct IDs.
* `SeventeenClassification.publishedSeparator` proves that the shipped 176-state partial DFA, completed by one rejecting sink, accepts the full blank orbit and rejects every eventually halting configuration. `PositiveSafetyConclusion.each` isolates one possible way to leave the accepted set. `PositiveSafetyGapBridge.gap_safe_padded` and `PositiveEscapeWeight.notMemOfExit` establish safety and exclusion from the historical weighted invariant for that family. `PositiveSafetyConclusion.escape_iff` identifies it as the exact set of exit sources.
* `WidthCases.dfaStateLower` and `WidthCases.enfaStateLower` give the uniform lower bound in physical cells for the sixteen ordinary negative cases. The manuscript gives the matching upper construction. The suffix-map checker replays its finite premise on all seventeen pinned weighted certificates.
* `PilotCases`, `PilotCorollary` and `CrossCases` prove the obstructions on seven-state rows 9,994,819, 9,932,146 and 12,767,546. The manuscript and `transfers/seven-state-applications.md` give the separate census calculation of at least 494 of 721. The additional Finned lifts use the written five-state obstruction in `transfers/finned-family.md` and `transfers/finned.md`.

The Skelet #17 replay checks two blank-reached checkpoints and two halting splices directly on the five-state table. Section 6 of the manuscript proves the all-length statement using savask’s tape encoding and Xu’s Gray-counter rules.

The two [published census manifests](https://github.com/maxilism/busy-beaver-research/tree/682350182398fa879b9db9fe73a043fe10596b47/support/data/bb-7-2/restoring-detours) let the census checker rebuild each listed shadow from the seven-state instructions. It checks the disjoint contributions to 494 under the stated transfer and obstruction proofs.

The theorem sources call `#print axioms` to show their dependencies. The Python programs compare certificate bytes and finite tables with the formal inputs. No Python result is an assumption of the Lean proofs.

The seventeen weighted records come from the [MITMWFAR archive at commit 3937731](https://github.com/Iijil1/MITMWFAR/blob/3937731f9e1d801d6f6d77cf44787f93fc1ffc76/SolvedFullCerts.txt). The extracted six-line certificate for #4817065 has SHA-256 `5092986314c8bfe602183acd112ca5236114d968beb685cedabee4ff835550f9`. The [published partial DFA](https://github.com/maxilism/busy-beaver-research/blob/ee693aa3127ca2aaa09a37f22e8b846fa6048914/support/verification/bb-5-2/cubic-helix/dfa.json) has SHA-256 `123cdce7aaa1a27daa78cd2ee04c8c02de3dafe5043f4c2eef766a7fdd938b4d`.

## Attribution and license

© 2026 [maxilism](https://github.com/maxilism). The paper and original proofs, code, and notes are licensed under [CC BY 4.0](LICENSE). The upstream weighted certificates in `data/SolvedFullCerts.txt` and the extracted record in `lower-bound/cert-4817065.txt` come from Iijil1 and contributors. Their [MIT license](data/MITMWFAR-LICENSE) is included.
