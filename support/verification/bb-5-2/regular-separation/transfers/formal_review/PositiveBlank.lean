import PositiveSafetyConclusion
import PositiveEscapeWeight
import PositiveWeight

/-! Every configuration reachable from blank is accepted by the published
176-state DFA. The weighted invariant excludes the same exceptional words
that occur in the safety proof's one-step check. -/
namespace PositiveBlank
open Helix PositiveSafetyCore

private theorem gapExcluded (c : Cfg) (cut : CutConfig PositiveSafetyGapDFA.accepts c) :
    ¬ PositiveWeight.W c := by
  obtain ⟨l,q,x,r,rfl,h⟩ := cut
  exact PositiveEscapeWeight.notMemOfExit l q x r h

theorem blankCoverage (c : Cfg) (path : Reach blank c) : PositiveDFA.accepts c :=
  coverage PositiveSafetyConclusion.each (by
    simp [PositiveDFA.accepts, display, blank]
    decide) PositiveWeight.blank_mem
    (fun _ _ => PositiveWeight.closed) gapExcluded c path

end PositiveBlank
