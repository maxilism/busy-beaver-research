import SiblingCatalog
import WidthCore

/-! On either reflected sibling table, the shorter prefix and longer suffix
from two diagonal visits produce a halting input. A mixed word has as many
physical cells as the sum of the two bank lengths plus a fixed prefix and
three cells. We use consecutive positive multiples of three as bank sizes. -/
namespace WidthSiblings

open Helix Helix.Obstruction Helix.Siblings SiblingCatalog

private def leftFragment (s : Bool) (i : Nat) := reflectedPrefix s (3*(i+1))

private def rightFragment (s : Bool) (j : Nat) :=
  reflectedSuffix (ext0 (w s ++ [true]) (3*(j+1)))

private theorem diag (s : Bool) (i : Nat) : Orbit s (leftFragment s i ++ rightFragment s i) := by
  refine ⟨_, ?_, displayMirrorQ s _ _⟩
  have hb : mirror s (root s) = blank := by cases s <;> rfl
  exact hb ▸ reachMirror s (reachesDiagonal s i)

private theorem off (s : Bool) {i j : Nat} (h : i < j) :
    Fatal s (leftFragment s i ++ rightFragment s j) := by
  obtain ⟨t, path, halted⟩ := leftHeavyHalts (w s) (i+1) (j+1) (by omega)
  exact ⟨_, mirror s t, displayMirrorQ s _ _, reachMirror s path, haltMirror s halted⟩

private theorem prefix_length (s : Bool) (i : Nat) :
    (leftFragment s i).length = 3*(i+1) + 3 := by
  let j := 3*i+2
  have hj : 3*(i+1) = j+1 := by dsimp [j]; omega
  have nz : z (ones (j+1)) ≠ 0 := by simp [ones, push, Bool.toNat]
  have hcells : cells (z (ones (j+1))) = false :: cells (ones (j+1)) := by
    rw [cells, dite_eq_right nz]
    simp
  simp [leftFragment, reflectedPrefix, hj, hcells, Nat.add_assoc]

private theorem suffix_length (s : Bool) (j : Nat) :
    (rightFragment s j).length = (w s).length + 1 + 3*(j+1) := by
  have h (f : Wd) : (cells (left (true :: f))).length = f.length + 1 := by
    simpa using congrArg List.length (cellsLeft f)
  cases s <;> simp [rightFragment, reflectedSuffix, w, ext0, h] <;> omega

/-- An n-state machine fails on the finite promise of 6n+9 cells for
#5377178 or 6n+11 cells for #7138511. -/
theorem lower (s : Bool) (n : Nat) (L : Splice.CutLanguage Sym n) :
    ¬ Width.SeparatesThrough (6*n + 9 + (w s).length) (Orbit s) (Fatal s) L.accepts := by
  apply Width.noSeparatorOfSlices n _ L (leftFragment s) (rightFragment s) (diag s)
    (fun _ _ h => Or.inl (off s h))
  intro i j
  rw [List.length_append, prefix_length, suffix_length]
  have := i.isLt
  have := j.isLt
  omega

end WidthSiblings
