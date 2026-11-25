import InverterCases
import WidthCore

/-! The physical width of an inverter slice, including the scanned zero
when the right bank is empty. -/
namespace WidthInverter
open Inverter Helix

private theorem pushedLength (a : Nat) (b : Bool) (h : push b a ≠ 0) :
    (cells (push b a)).length = (cells a).length + 1 := by
  rw [cells]
  simp only [dite_eq_right h, pop_push, List.length_cons]

private theorem bankLength (i : Nat) : (cells (bank i)).length = 3 * i := by
  induction i with
  | zero => simp [bank]
  | succ i ih =>
    simp only [bank]
    rw [pushedLength _ false (by simp [push, Bool.toNat]),
        pushedLength _ true (by simp [push, Bool.toNat]),
        pushedLength _ true (by simp [push, Bool.toNat]), ih]
    omega

/-- The state marker takes one alphabet symbol and no physical cell. -/
theorem wordLength (i j : Nat) :
    (leftPart i ++ rightPart j).length = 3*i + max 1 j + 1 := by
  cases j with
  | zero => simp [leftPart, rightPart, bankLength, ones, pop]
  | succ j =>
    simp only [leftPart, rightPart, List.length_append, List.length_map, List.length_reverse,
      bankLength, ones, pop_push, cellsOnes, List.length_replicate, List.length_cons,
      List.length_nil]
    omega

/-- An n-state cut automaton fails on physical span at most max(1,4n).
The same bound applies to DFAs and to epsilon-NFAs. -/
theorem lower (v : Bool) (n : Nat) (L : Splice.CutLanguage Sym n) :
    ¬ Width.SeparatesThrough (max 1 (4*n)) (orbitWords v) (haltingWords v) L.accepts := by
  apply Width.noSeparatorOfSlices n _ L leftPart rightPart
  · intro i
    exact ⟨_, diagonalReached v i, checkpointWord i i⟩
  · intro i j hij
    exact Or.inl ⟨_, rightHeavyHalts v hij, checkpointWord i j⟩
  · intro i j
    rw [wordLength]
    have hi := i.isLt
    have hj := j.isLt
    omega

theorem stateCount (v : Bool) {n W : Nat} (hW : 0 < W)
    (L : Splice.CutLanguage Sym n)
    (sep : Width.SeparatesThrough W (orbitWords v) (haltingWords v) L.accepts) :
    W / 4 < n := by
  apply Classical.byContradiction
  intro small
  exact lower v n L (sep.mono (by omega))

end WidthInverter
