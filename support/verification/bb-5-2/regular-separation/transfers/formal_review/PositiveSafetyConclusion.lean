import PositiveSafetyCore
import PositiveSafetyChecks
import PositiveSafetyInclusion
import PositiveSafetyGapBridge
import PositiveEscapeExact

/-! Safety of every canonical configuration accepted by the published
176-state partial deterministic automaton for machine 4817065. Its finite
one-step check allows an exit only from a certified safe gap. -/
namespace PositiveSafetyConclusion
open Helix PositiveSafetyCore

theorem decode (l : Wd) (q : St) (x : Bool) (r : Wd) :
    PositiveSafetyAuto.K (wordOf l q x r) ↔ PositiveDFA.accepts (cfgOf l q x r) := by
  obtain ⟨i,j,h⟩ := paddedCanonical l q x r
  rw [h]
  exact PositiveSafetyInclusion.pad_display_iff i j (cfgOf l q x r)

/-- An accepted tape either is an exceptional gap or can take
a defined step to another accepted tape. -/
theorem each (c : Cfg) (h : PositiveDFA.accepts c) :
    CutConfig PositiveSafetyGapDFA.accepts c ∨ ∃ d, step c = some d ∧ PositiveDFA.accepts d :=
  oneStep PositiveSafetyChecks.rules decode c h

/-- Every transition from acceptance to rejection starts at a canonical gap word. -/
theorem escapeShape {c d : Cfg} (h : PositiveDFA.accepts c) (move : step c = some d)
    (outside : ¬PositiveDFA.accepts d) : ∃ i j, display c = PositiveSafetyGap.gapWord i j := by
  rcases each c h with ⟨l,q,x,r,rfl,shape⟩ | ⟨e,se,ae⟩
  · obtain ⟨u,i,j,v,spelling⟩ := PositiveSafetyGapDFA.decode shape
    exact ⟨i,j,PositiveSafetyGapBridge.configOfShape l q x r u i j v spelling⟩
  · rw [move] at se
    cases se
    exact False.elim (outside ae)

/-- The gap words are exactly the sources of transitions out of the separator. -/
theorem escape_iff (c : Cfg) :
    (PositiveDFA.accepts c ∧ ∃ d, step c = some d ∧ ¬PositiveDFA.accepts d) ↔
      ∃ i j, display c = PositiveSafetyGap.gapWord i j := by
  constructor
  · rintro ⟨accepted,d,move,rejected⟩
    exact escapeShape accepted move rejected
  · rintro ⟨i,j,shape⟩
    exact PositiveEscapeExact.escapesOfShape shape

/-- No accepted configuration can reach a halting configuration. -/
theorem acceptedSafe (c : Cfg) (h : PositiveDFA.accepts c) : Helix.Obstruction.Safe c :=
  safety each (fun _ ⟨l,q,x,r,e,shape⟩ =>
    e ▸ PositiveSafetyGapBridge.gap_safe_padded l q x r shape) c h

end PositiveSafetyConclusion

#print axioms PositiveSafetyConclusion.acceptedSafe
#print axioms PositiveSafetyConclusion.escape_iff
