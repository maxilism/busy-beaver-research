import BalancedCases
import WidthCore

/-! Exact bank lengths in either catalog orientation for all twelve balanced tables. -/
namespace WidthBalanced

open Balanced BalancedTM BalancedCases BalancedCatalog

private theorem sideLengthPush (b : Bool) (t : Nat) (h : push b t ≠ 0) :
    (side (push b t)).length = (side t).length + 1 := by
  rw [side]
  simp [h]

private theorem oddNonzero (t : Nat) : o t ≠ 0 := by
  simp [o, push, Bool.toNat]

private theorem doubleNonzero (t : Nat) (ht : t ≠ 0) : z t ≠ 0 := by
  simp [z, push, Bool.toNat]
  omega

private theorem bankLength (n : Nat) : (side (bank n)).length = 2*n := by
  induction n with
  | zero => rw [bank, side]; simp
  | succ n ih =>
    rw [bank, sideLengthPush _ _ (doubleNonzero _ (oddNonzero _)),
      sideLengthPush _ _ (oddNonzero _), ih]
    omega

private theorem pairsNext (n : Nat) : pairs (n+1) = o (z (pairs n)) := by
  simp [pairs, List.replicate_succ, encode]

private theorem pairsNonzero (n : Nat) : pairs n ≠ 0 := by
  cases n with
  | zero => exact oddNonzero _
  | succ n => rw [pairsNext]; exact oddNonzero _

private theorem pairsLength (n : Nat) : (side (pairs n)).length = 2*n+1 := by
  induction n with
  | zero =>
    change (side (o 0)).length = 1
    rw [sideLengthPush _ _ (oddNonzero _), side]
    simp
  | succ n ih =>
    rw [pairsNext, sideLengthPush _ _ (oddNonzero _),
      sideLengthPush _ _ (doubleNonzero _ (pairsNonzero _)), ih]
    omega

/-- Each word has a state marker, a scanned zero, a terminal one and two
cells per bank pair. Reflection changes the order but preserves this size. -/
theorem sliceLength (v : Variant) (d : Bool) (i j : Nat) :
    (sliceLeft v d i ++ sliceRight v d j).length =
      2 * (d.toNat + visitIndex d i + visitIndex d j) + 3 := by
  cases h : mirror v d <;>
    simp [sliceLeft, sliceRight, h, mark, bankLength, pairsLength] <;> omega

/-- At physical span 4n+2 on the six A roots, or 8n+4 on the six D roots,
no n-state cut automaton separates the reached and eventually halting words. -/
theorem lower (v : Variant) (d : Bool) (n : Nat) (L : Splice.CutLanguage Symbol n) :
    ¬ Width.SeparatesThrough (4 * (d.toNat + 1) * n + 2*d.toNat + 2)
       (orbit v d) (halters v d) L.accepts := by
  obtain ⟨diag, off⟩ := slice_properties v d
  apply Width.noSeparatorOfSlices n _ L (sliceLeft v d) (sliceRight v d) diag off
  intro i j
  rw [sliceLength]
  have hi := i.isLt
  have hj := j.isLt
  cases d <;> simp [visitIndex, Bool.toNat] <;> omega

end WidthBalanced
