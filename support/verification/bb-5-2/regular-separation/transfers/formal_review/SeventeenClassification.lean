import ReviewedCases
import PositiveBlank
import PositiveSafetyConclusion

/-! On the seventeen weighted BB(5) tables, the cubic helix #4817065
is the unique machine whose blank orbit admits an ordinary regular separator.
None of the seventeen admits an inductive regular separator. -/
namespace SeventeenClassification
open ReviewedCases

/-- Accept every blank-reachable canonical word and reject every canonical
word of a configuration from which a halt is reachable. -/
def Separates (M : Machine) {n : Nat} (D : Splice.DFA M.Symbol n) : Prop :=
  (∀ w, M.orbit w → D.accepts w) ∧ (∀ w, M.halters w → ¬ D.accepts w)

def HasOrdinary (M : Machine) : Prop :=
  ∃ n, ∃ D : Splice.DFA M.Symbol n, Separates M D

/-- The published 176-state partial table, completed by one rejecting sink. -/
theorem publishedSeparator : Separates base PositiveDFA.machine := by
  constructor
  · rintro _ ⟨c, path, rfl⟩
    exact PositiveBlank.blankCoverage c path
  · rintro _ ⟨c, t, path, halted, rfl⟩ accepted
    exact PositiveSafetyConclusion.acceptedSafe c accepted t path halted

theorem ordinary_iff (i : Option OrdinaryCase) :
    HasOrdinary (reviewed i) ↔ catalogId i = 4817065 := by
  cases i with
  | none => exact ⟨fun _ => rfl, fun _ => ⟨177, PositiveDFA.machine, publishedSeparator⟩⟩
  | some i =>
    constructor
    · rintro ⟨n, D, h⟩
      exact False.elim (ordinarySixteen i n D h)
    · intro id
      cases i with
      | balanced v d => cases v <;> cases d <;> contradiction
      | inverter v => cases v <;> contradiction
      | sibling v => cases v <;> contradiction

theorem classification (i : Option OrdinaryCase) :
    (HasOrdinary (reviewed i) ↔ catalogId i = 4817065) ∧
    (∀ n (D : Splice.DFA (reviewed i).Symbol n), ¬ (reviewed i).regularCTL D) :=
  ⟨ordinary_iff i, allSeventeen i⟩

end SeventeenClassification

#print axioms SeventeenClassification.publishedSeparator
#print axioms SeventeenClassification.classification
