import PilotCases

/-! An unblinded corollary of the experiment on row 9,994,819.
Row 9,932,146 changes only B0. From an A head a B0 step of the
first table has a one immediately to its left, allowing B0, B1, A1
of the second table to reach its exact successor. -/
namespace PilotCorollary
open Pilot (St Cfg F K Sym display blank checkpoint)
open Helix (Dir push top pop o)

def instruction : St → Bool → Option (Bool × Dir × St)
  | .B, false => some (true, .L, .B)
  | q, x => Pilot.instruction q x

private def letter : St → String
  | .A => "A" | .B => "B" | .C => "C" | .D => "D"
  | .E => "E" | .F => "F" | .G => "G"

private def code (q : St) (x : Bool) : String :=
  match instruction q x with
  | none => "---"
  | some (w, dir, next) =>
    (if w then "1" else "0") ++ (if dir = .L then "L" else "R") ++ letter next

theorem literalTable :
    String.intercalate "_" ([St.A,.B,.C,.D,.E,.F,.G].map
      (fun q => code q false ++ code q true)) =
      "1RB1LC_1LB1RA_0LG0LD_0RE1RD_1RE1LF_0RA0LF_---0LC" := by decide

def step (c : Cfg) : Option Cfg :=
  match instruction c.q c.x with
  | none => none
  | some (w, .R, q) => some (F q (push w c.l) c.r)
  | some (w, .L, q) => some (K q c.l (push w c.r))

inductive Reach : Cfg → Cfg → Prop where
  | refl (c) : Reach c c
  | cons {a b c} : step a = some b → Reach b c → Reach a c

theorem Reach.trans {a b c} (p : Reach a b) (q : Reach b c) : Reach a c := by
  induction p with
  | refl => exact q
  | cons h _ ih => exact .cons h (ih q)

def Marked (c : Cfg) : Prop := c.q = .B → top c.l = true

private theorem marksNext {c d : Cfg} (h : Pilot.step c = some d) : Marked d := by
  obtain ⟨q,l,x,r⟩ := c
  cases q <;> cases x <;> simp [Pilot.step, Pilot.instruction] at h <;> subst d <;>
    simp [Marked, F, K]

private theorem otherStep {c : Cfg} (h : ¬ (c.q = .B ∧ c.x = false)) :
    step c = Pilot.step c := by
  obtain ⟨q,l,x,r⟩ := c
  cases q <;> cases x <;> first | rfl | simp at h

private theorem replaceB0 (l r : Nat) :
    Reach ⟨.B, o l, false, r⟩ (K .C (o l) (o r)) := by
  apply Reach.cons (b := ⟨.B, l, true, o r⟩)
  · simp [step, instruction, K]
  apply Reach.cons (b := ⟨.A, o l, true, r⟩)
  · simp [step, instruction, Pilot.instruction, F]
  exact .cons rfl (.refl _)

private theorem liftStep {c d : Cfg} (good : Marked c) (h : Pilot.step c = some d) :
    Reach c d := by
  by_cases bad : c.q = .B ∧ c.x = false
  · obtain ⟨q,l,x,r⟩ := c
    rcases bad with ⟨rfl, rfl⟩
    have bit := good rfl
    have bits : o (pop l) = l := by
      simpa only [bit] using Helix.push_unpack l
    simp [Pilot.step, Pilot.instruction] at h
    subst d
    simpa only [bits] using replaceB0 (pop l) r
  · exact .cons ((otherStep bad).trans h) (.refl _)

theorem liftPath {c d : Cfg} (p : Pilot.Reach c d) (good : Marked c) : Reach c d := by
  induction p with
  | refl => exact .refl _
  | cons h _ ih => exact (liftStep good h).trans (ih (marksNext h))

private theorem haltPreserved {c : Cfg} (h : Pilot.step c = none) : step c = none := by
  obtain ⟨q,l,x,r⟩ := c
  cases q <;> cases x <;> first | rfl | simp [Pilot.step, Pilot.instruction] at h

def EventuallyHalts (c : Cfg) := ∃ t, Reach c t ∧ step t = none

theorem diagonalReached (n : Nat) : Reach blank (checkpoint n n) :=
  liftPath (Pilot.diagonalReached n) (by simp [Marked, blank, F])

theorem rightHeavyHalts {n m : Nat} (h : n < m) : EventuallyHalts (checkpoint n m) := by
  obtain ⟨t, p, halt⟩ := Pilot.rightHeavyHalts h
  exact ⟨t, liftPath p (by simp [Marked, checkpoint, F]), haltPreserved halt⟩

def orbitWords (w : List Sym) := ∃ c, Reach blank c ∧ display c = w
def haltingWords (w : List Sym) := ∃ c, EventuallyHalts c ∧ display c = w

theorem noOrdinarySeparator : Splice.NoDFASeparator orbitWords haltingWords :=
  Splice.noSeparator_of_slices Pilot.leftPart Pilot.rightPart
    (fun i => ⟨_, diagonalReached i, Pilot.checkpointWord i i⟩)
    (fun i j h => Or.inl ⟨_, rightHeavyHalts h, Pilot.checkpointWord i j⟩)

end PilotCorollary

#print axioms PilotCorollary.noOrdinarySeparator
