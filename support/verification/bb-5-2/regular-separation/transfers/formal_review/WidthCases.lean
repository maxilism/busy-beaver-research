import ReviewedCases
import WidthBalanced
import WidthInverter
import WidthSiblings

/-! Linear state lower bounds on all sixteen ordinarily inseparable machines.
The classifier is constrained only on reachable or eventually halting input
words whose canonical tape spans at most the promised width. -/
namespace WidthCases
open ReviewedCases

/-- A width sufficient to defeat any n-state automaton, in physical cells. -/
def threshold : OrdinaryCase → Nat → Nat
  | .balanced _ d, n => 4 * (d.toNat+1) * n + 2*d.toNat + 2
  | .inverter _, n => max 1 (4*n)
  | .sibling v, n => 6*n + 9 + (Helix.Siblings.w v).length

/-- A violation occurs by the indicated width on each literal table.
Cut languages include both DFAs and epsilon-NFAs with their original state count. -/
theorem obstruction (i : OrdinaryCase) (n : Nat) (L : Splice.CutLanguage (machine i).Symbol n) :
    ¬ Width.SeparatesThrough (threshold i n) (machine i).orbit (machine i).halters L.accepts := by
  cases i with
  | balanced v d => exact WidthBalanced.lower v d n L
  | inverter v =>
    intro h
    apply WidthInverter.lower v n L
    refine ⟨h.1, ?_⟩
    rintro w hw ⟨c, ⟨t, p, dead⟩, view⟩
    exact h.2 w hw ⟨c, t, p, dead, view⟩
  | sibling v =>
    intro h
    apply WidthSiblings.lower v n L
    refine ⟨h.1, ?_⟩
    rintro w hw ⟨c, t, view, p, dead⟩
    exact h.2 w hw ⟨c, t, p, dead, view⟩

theorem threshold_le (i : OrdinaryCase) (n : Nat) : threshold i n ≤ 8*n+11 := by
  cases i with
  | balanced _ d => cases d <;> simp [threshold, Bool.toNat] <;> omega
  | inverter _ => simp [threshold]; omega
  | sibling v => cases v <;> simp [threshold, Helix.Siblings.w] <;> omega

theorem stateLower (i : OrdinaryCase) {n W : Nat} (L : Splice.CutLanguage (machine i).Symbol n)
    (hw : 11 ≤ W) (sep : Width.SeparatesThrough W (machine i).orbit (machine i).halters L.accepts) :
    (W-11)/8 + 1 ≤ n := by
  have h : ¬ threshold i n ≤ W := fun bad => obstruction i n L (sep.mono bad)
  have := threshold_le i n
  omega

theorem dfaStateLower (i : OrdinaryCase) {n W : Nat} (D : Splice.DFA (machine i).Symbol n)
    (hw : 11 ≤ W) (sep : Width.SeparatesThrough W (machine i).orbit (machine i).halters D.accepts) :
    (W-11)/8 + 1 ≤ n :=
  stateLower i D.cuts hw sep

theorem enfaStateLower (i : OrdinaryCase) {n W : Nat} (A : Splice.ENFA (machine i).Symbol n)
    (hw : 11 ≤ W) (sep : Width.SeparatesThrough W (machine i).orbit (machine i).halters A.accepts) :
    (W-11)/8 + 1 ≤ n :=
  stateLower i A.cuts hw sep

end WidthCases

#print axioms WidthCases.obstruction
#print axioms WidthCases.enfaStateLower
#print axioms WidthCases.dfaStateLower
