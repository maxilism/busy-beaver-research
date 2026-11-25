import BalancedCases
import InverterCases
import SiblingCatalog
import Helix.Proof

/-! Canonical finite-word separation on the seventeen reviewed BB(5) tables.
The sixteen ordinary obstructions also exclude inductive languages. The
remaining table, #4817065, uses its separate two-pump closure theorem. -/
namespace ReviewedCases

/-- Each family supplies the actual catalog step and its finite paths. -/
structure Machine where
  Cfg : Type
  Symbol : Type
  blank : Cfg
  step : Cfg → Option Cfg
  display : Cfg → List Symbol
  reach : Cfg → Cfg → Prop
  closed {P : Cfg → Prop} (one : ∀ c e, step c = some e → P c → P e)
    {c e} : reach c e → P c → P e

namespace Machine

def orbit (M : Machine) (w : List M.Symbol) : Prop :=
  ∃ c, M.reach M.blank c ∧ M.display c = w

def halters (M : Machine) (w : List M.Symbol) : Prop :=
  ∃ c h, M.reach c h ∧ M.step h = none ∧ M.display c = w

/-- A regular CTL invariant accepts blank, preserves acceptance under every
one-step successor, and rejects each configuration with an undefined step. -/
def regularCTL (M : Machine) {n : Nat} (D : Splice.DFA M.Symbol n) : Prop :=
  D.accepts (M.display M.blank) ∧
    (∀ c e, M.step c = some e → D.accepts (M.display c) → D.accepts (M.display e)) ∧
    (∀ c, M.step c = none → ¬ D.accepts (M.display c))

theorem noRegularCTL_of_noSeparator (M : Machine)
    (h : Splice.NoDFASeparator M.orbit M.halters) (n : Nat) (D : Splice.DFA M.Symbol n) :
    ¬ M.regularCTL D := by
  rintro ⟨ini, closed, safe⟩
  apply h n D
  constructor
  · rintro _ ⟨c, p, rfl⟩
    exact M.closed closed p ini
  · rintro _ ⟨c, t, p, dead, rfl⟩ accept
    exact safe t dead (M.closed closed p accept)

end Machine

def balanced (v : BalancedTM.Variant) (d : Bool) : Machine where
  Cfg := BalancedTM.Cfg
  Symbol := BalancedCases.Symbol
  blank := BalancedTM.blank .A
  step := BalancedCatalog.catalogStep v d
  display := BalancedCases.display
  reach := BalancedTM.Walk (BalancedCatalog.catalogStep v d)
  closed := by
    intro P one c e p
    induction p with
    | nil => exact id
    | tick h _ ih => exact fun hc => ih (one _ _ h hc)

def inverter (v : Bool) : Machine where
  Cfg := Helix.Cfg
  Symbol := Helix.Sym
  blank := Helix.blank
  step := Inverter.step v
  display := Helix.display
  reach := Inverter.Reach v
  closed := by
    intro P one c e p
    induction p with
    | refl => exact id
    | cons h _ ih => exact fun hc => ih (one _ _ h hc)

def sibling (v : Bool) : Machine where
  Cfg := Helix.Cfg
  Symbol := Helix.Sym
  blank := Helix.blank
  step := SiblingCatalog.step v
  display := Helix.display
  reach := SiblingCatalog.Reach v
  closed := by
    intro P one c e p
    induction p with
    | refl => exact id
    | cons h _ ih => exact fun hc => ih (one _ _ h hc)

def base : Machine where
  Cfg := Helix.Cfg
  Symbol := Helix.Sym
  blank := Helix.blank
  step := Helix.step
  display := Helix.display
  reach := Helix.Reach
  closed one := Helix.Reach.closed (fun c e hc step => one c e step hc)

/-- Parameterization of the sixteen tables with an ordinary obstruction. -/
inductive OrdinaryCase where
  | balanced (v : BalancedTM.Variant) (dRoot : Bool)
  | inverter (v : Bool)
  | sibling (v : Bool)
  deriving DecidableEq, Repr

def machine : OrdinaryCase → Machine
  | .balanced v d => balanced v d
  | .inverter v => inverter v
  | .sibling v => sibling v

/-- `none` selects the original cubic helix, #4817065. -/
def reviewed : Option OrdinaryCase → Machine
  | none => base
  | some i => machine i

def catalogId : Option OrdinaryCase → Nat
  | none => 4817065
  | some (.balanced v d) => BalancedCatalog.machineId v d
  | some (.inverter v) => if v then 12699987 else 12781955
  | some (.sibling v) => SiblingCatalog.catalogId v

def indices : List (Option OrdinaryCase) :=
  let variants : List BalancedTM.Variant :=
    [.m8210683, .m8210684, .m8210685, .m8226493, .m10818491, .m10818510]
  none :: (variants.flatMap fun v => [some (.balanced v false), some (.balanced v true)]) ++
    [some (.inverter false), some (.inverter true), some (.sibling false), some (.sibling true)]

theorem indices_exhaustive (i : Option OrdinaryCase) : i ∈ indices := by
  cases i with
  | none => decide
  | some i => cases i with
    | balanced v d => cases v <;> cases d <;> decide
    | inverter v => cases v <;> decide
    | sibling v => cases v <;> decide

theorem distinctSeventeen : indices.length = 17 ∧ (indices.map catalogId).Nodup := by decide

/-- For each of sixteen catalog indices, every DFA accepting the full blank
orbit accepts an input from which an immediate halt is reachable. -/
theorem ordinarySixteen (i : OrdinaryCase) :
    Splice.NoDFASeparator (machine i).orbit (machine i).halters := by
  cases i with
  | balanced v d => exact BalancedCases.noSeparator v d
  | inverter v =>
    intro n D hyp
    apply Inverter.noOrdinarySeparator v n D
    refine ⟨hyp.1, ?_⟩
    rintro w ⟨c, ⟨t, p, h⟩, hw⟩
    exact hyp.2 w ⟨c, t, p, h, hw⟩
  | sibling v =>
    intro n D hyp
    apply SiblingCatalog.noSeparator v n D
    refine ⟨hyp.1, ?_⟩
    rintro w ⟨c, t, hw, p, h⟩
    exact hyp.2 w ⟨c, t, p, h, hw⟩

private theorem baseNoRegularCTL (n : Nat) (D : Splice.DFA Helix.Sym n) : ¬ base.regularCTL D := by
  classical
  let A : Helix.Obstruction.WordDFA n := ⟨D.start, D.move, fun q => decide (D.final q)⟩
  have accepts (c : Helix.Cfg) : A.accepts c ↔ D.accepts (Helix.display c) := by
    simp [Helix.Obstruction.WordDFA.accepts, A, Splice.DFA.accepts]
  rintro ⟨initial, closed, safe⟩
  apply A.not_inductive_separator
  exact ⟨(accepts _).mpr initial,
         fun c e hc h => (accepts _).mpr (closed c e h ((accepts c).mp hc)),
         fun c hc h => safe c h ((accepts c).mp hc)⟩

/-- None of the seventeen catalog tables admits a regular CTL invariant. -/
theorem allSeventeen (i : Option OrdinaryCase) (n : Nat) (D : Splice.DFA (reviewed i).Symbol n) :
    ¬ (reviewed i).regularCTL D := by
  cases i with
  | none => exact baseNoRegularCTL n D
  | some i => exact (machine i).noRegularCTL_of_noSeparator (ordinarySixteen i) n D

end ReviewedCases

#print axioms ReviewedCases.distinctSeventeen
#print axioms ReviewedCases.ordinarySixteen
#print axioms ReviewedCases.allSeventeen
