# A state bound for arbitrary ordinary separators

Run from this directory with Python 3:

```sh
python3 -IB check_bounds.py
```

The checker reads the adjacent [certificate](lower-bounds.json) and uses only the standard library. A word uses the seven-letter alphabet `01ABCDE`; the state letter comes immediately before the scanned bit. A live DFA state is one from which some suffix is accepted.

**Proposition.** A partial DFA accepting every blank-orbit word and rejecting every canonical word that reaches a halt needs at least **27 live states**, even allowing arbitrary answers on malformed words. If the DFA must also reject malformed words, it needs at least **51 live states**, or **52 states in a complete DFA**. These are lower bounds, not minimal sizes. This statement concerns the specified alphabet, not the alternative alphabet with a combined state/bit symbol. No step closure is assumed.

**Certificate.** For each group of prefixes `u` the JSON lists a time on the blank run witnessing an accepted extension of each prefix, and a tuple `[a,b,t,d]` for every unordered pair of distinct prefixes. Cut the canonical blank configuration at time `t` as `u[a] z`. The hybrid `u[b] z` is canonical and reaches the missing D1 transition in exactly `d` steps. A DFA must therefore distinguish the two prefixes; both are live because they extend to blank configurations. The two groups respectively contain 27 prefixes with no state marker (351 pairs) and 24 prefixes with one (276 pairs); maximum blank times 15920 and 17576, maximum halt distances 1777 and 1199. Every pair is tested by taking actual single steps of the table. This is a finite certificate of a universal lower bound, not an inference from failing a bounded automaton search.

If malformed words are excluded, the groups are disjoint in the DFA as well: a positive extension suffix of a prefix in the first group contains a state. Applied after a prefix in the second, the word would have two states. The prefix `00` cannot begin any canonical word, hence gives a non-live state in a complete automaton. The pair argument is for DFAs; it does not give these state counts for NFAs. For the different problem of requiring step closure through span `W`, see [the state-cost paper, §2](../../../../../results/bb-5-2/cubic-helix-state-complexity.pdf). The finite certificate here does not require any step closure.
