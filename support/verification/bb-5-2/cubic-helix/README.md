# Verification for the five-state cubic helix

For [machine 4817065](https://bbchallenge.org/4817065), the [regular-separation paper](../../../../results/bb-5-2/cubic-helix.pdf) gives a finite automaton that accepts every configuration on the blank orbit and rejects every configuration that eventually halts. No regular separator is closed under all machine steps. The checks below concern this machine and its canonical words over `01ABCDE`, with the state letter before the scanned bit.

| Artifact | What it verifies |
|---|---|
| [Published automaton](dfa.json) · [extractor](extract_dfa.py) · [regression check](check-dfa.py) | `python3 check-dfa.py` regenerates the 176-state partial DFA byte for byte, tests bounded runs, and finds an accepted word with a rejected successor. Run the command from this directory. |
| [All-length automaton check](automaton-check/) | Two word-language inclusions identify the DFA language exactly with a specified interpolation. Four domain and four paired endpoint checks cover complete blank sweeps. The accompanying argument explains coverage between endpoints and safety from the checkpoint lemma. |
| [Lean proofs](lean/) | Lean checks the obstruction for every finite DFA, blank nonhalting, safety of the full checkpoint family, and the connection with the integer-indexed tape. It does not read the DFA file or verify the Python checker. |
| [State lower-bound certificate](state-lower-bound/) | Replaying 627 distinguishing pairs proves a lower bound of 27 live DFA states for ordinary separation. If malformed words must be rejected, the bounds are 51 live states and 52 states for a complete DFA. No step closure is assumed. |

The [state-cost paper](../../../../results/bb-5-2/cubic-helix-state-complexity.pdf) asks a different question: how the minimum DFA or NFA size grows when one-step closure is required through span `W`. The fixed certificate above is not a computational premise of that proof.

J. Blanchard’s earlier [weighted-automaton certificate](https://github.com/Iijil1/MITMWFAR/blob/3937731f9e1d801d6f6d77cf44787f93fc1ffc76/SolvedFullCerts.txt#L85-L90) proves nonhalting from blank. The checks here do not require that certificate.

© 2026 maxilism. Original material is licensed under [CC BY 4.0](../../../../LICENSE).
