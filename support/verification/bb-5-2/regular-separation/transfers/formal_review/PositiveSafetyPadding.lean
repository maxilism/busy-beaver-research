import PositiveSafetyAuto

/-! The padded tape automaton absorbs blank cells on the left at its start.
After it reads the marker and the scanned cell, a right blank preserves its
acceptance bit. -/
namespace PositiveSafetyPadding

open Helix PositiveSafetyAuto

set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- States reached after a marker, a scanned cell, and any further plain cells. -/
private def afterHead (s : State) : Bool :=
  (0x2090d23e4c0e707d130ccf207a1d81a63a18e87ea00 : Nat).testBit s.val

private theorem head (s : State) (q : St) (x : Bool) :
    afterHead (move (move s (.mark q)) (.bit x)) = true := by
  cases q <;> cases x <;> revert s <;> decide

private theorem cell (s : State) (b : Bool) :
    afterHead s = true → afterHead (move s (.bit b)) = true := by
  cases b <;> revert s <;> decide

private theorem blank (s : State) :
    afterHead s = true → final (move s (.bit false)) = final s := by
  revert s; decide

private theorem tailCells (bs : Wd) (s : State) (h : afterHead s = true) :
    afterHead ((bs.map Sym.bit).foldl move s) = true := by
  induction bs generalizing s with
  | nil => exact h
  | cons b bs ih => exact ih _ (cell _ _ h)

private theorem rightBlanks (j : Nat) (s : State) (h : afterHead s = true) :
    final ((List.replicate j (.bit false)).foldl move s) = final s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    simp only [List.replicate_succ, List.foldl_cons]
    exact (ih _ (cell _ _ h)).trans (blank _ h)

private theorem leftBlanks (i : Nat) :
    (List.replicate i (.bit false)).foldl move start = start := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [List.replicate_succ, List.foldl_cons]
    exact ih

private theorem displayEnd (c : Cfg) : afterHead ((display c).foldl move start) = true := by
  simp only [display, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact tailCells _ _ (head _ _ _)

theorem pad_iff (i j : Nat) (c : Cfg) :
    K (List.replicate i (.bit false) ++ display c ++ List.replicate j (.bit false)) ↔
      K (display c) := by
  simp only [PositiveSafetyAuto.K, PositiveSafetyAuto.read, List.foldl_append, leftBlanks, rightBlanks j _ (displayEnd c)]

end PositiveSafetyPadding
