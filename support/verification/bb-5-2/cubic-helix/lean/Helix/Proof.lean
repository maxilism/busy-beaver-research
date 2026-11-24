import Helix.Paths
import Helix.ZeroPeriod
import Helix.Tape

namespace Helix.Obstruction
/-! ## DFA pumping and the invariant contradiction

`Fin n` merely numbers the states of an arbitrary finite automaton. The
alphabet consists of the two tape symbols and five state-marker symbols.
Closure is on the canonical display of each genuine one-step successor.
-/
structure WordDFA (n : Nat) where
  start : Fin n
  move : Fin n → Sym → Fin n
  final : Fin n → Bool

namespace WordDFA
variable {n : Nat} (d : WordDFA n)

def accepts (c : Cfg) : Prop := d.final ((display c).foldl d.move d.start) = true

private theorem readZeros (q : Fin n) (j : Nat) :
    (List.replicate j (Sym.bit false)).foldl d.move q =
      iter (fun s => d.move s (.bit false)) j q := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ', List.foldl_append, ih]
    rfl

/-- Lift unary periodicity to a canonical checkpoint. The two contexts are
    arbitrary; in particular the length of the trailing ones stays fixed. -/
private theorem pumpQ (j p c : Nat) (f : Wd)
    (h : ∀ q, iter (fun s => d.move s (.bit false)) (j+p) q =
              iter (fun s => d.move s (.bit false)) j q) :
    d.accepts (Q (ext0 (true::f) (j+p)) 0 (c+1)) ↔
    d.accepts (Q (ext0 (true::f) j) 0 (c+1)) := by
  change d.accepts (Q (true :: (f ++ List.replicate (j+p) false)) 0 (c+1)) ↔
         d.accepts (Q (true :: (f ++ List.replicate j false)) 0 (c+1))
  simp only [accepts, displayQ0, List.map_cons, List.map_append, List.map_replicate,
    List.foldl_append, List.foldl_cons, readZeros, h]

/-- In fact any inductive DFA containing blank accepts an *immediate* halt.
    Both pumps change only the contiguous block of zeros to the left of `D`. -/
theorem accepts_halt (hblank : d.accepts blank)
    (hclosed : ∀ c e, d.accepts c → step c = some e → d.accepts e) :
    ∃ t, d.accepts t ∧ Halted t := by
  obtain ⟨N, r, hp⟩ := zero_period (fun q => d.move q (.bit false))
  -- k=3N+4 comes from the diagonal after the N-th right-edge return;
  -- p=3r+6 and s=k+p-4. The second pump shortens s to 3N.
  let k := 3*N+4
  let p := 3*r+6
  let s := 3*N+p
  have atFirst : d.accepts (Q (ext0 [true] k) 0 k) :=
    Reach.closed hclosed ((rightEdges N).trans (diagonal (3*N+2))) hblank
  have pump1 := d.pumpQ k p (3*N+3) [] (hp k (by dsimp [k]; omega))
  have startPath := pump1.mpr atFirst
  have path := forceSecondSite (N+1) r
  rw [show 3*(N+1)+1=k by dsimp [k]; omega,
      show k+3*r+2=s by dsimp [k,s,p]; omega] at path
  have atSecond := Reach.closed hclosed path startPath
  have pump2 := d.pumpQ (3*N) p (s-1) [false,false,false,true]
    (hp (3*N) (by omega))
  have spos : s-1+1 = s := by dsimp [s,p]; omega
  rw [spos] at pump2
  have accepted := pump2.mp atSecond
  obtain ⟨t, ht, bad⟩ := secondSiteHalts N r
  exact ⟨t, Reach.closed hclosed ht accepted, bad⟩

/-- No finite-state inductive separator on canonical configuration words. -/
theorem not_inductive_separator :
    ¬ (d.accepts blank ∧
       (∀ c e, d.accepts c → step c = some e → d.accepts e) ∧
       (∀ c, d.accepts c → ¬ Halted c)) := by
  rintro ⟨hblank, hclosed, hsafe⟩
  obtain ⟨t, ha, hh⟩ := d.accepts_halt hblank hclosed
  exact hsafe t ha hh

/-- For each blank-containing DFA which excludes immediate halts, there is a
    genuine accepted configuration with a rejected one-step successor. In
    particular this applies if the DFA excludes every eventually halting input. -/
theorem closure_counterexample (hblank : d.accepts blank)
    (hexcludes : ∀ t, Halted t → ¬ d.accepts t) :
    ∃ c e, d.accepts c ∧ step c = some e ∧ ¬ d.accepts e := by
  classical
  apply Classical.byContradiction
  intro hn
  have closed c e (hc : d.accepts c) (h : step c = some e) : d.accepts e :=
    Classical.byContradiction (fun he => hn ⟨c,e,hc,h,he⟩)
  obtain ⟨t,ha,hh⟩ := d.accepts_halt hblank closed
  exact hexcludes t hh ha
end WordDFA
end Helix.Obstruction

#print axioms Helix.Obstruction.WordDFA.not_inductive_separator
#print axioms Helix.Obstruction.WordDFA.closure_counterexample
