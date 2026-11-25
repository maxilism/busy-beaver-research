import PositiveWeightData
import Helix.Tape

/-! Evaluate the two weighted automata from exterior to head. The low bit of
each stack is the last bit read, and missing exterior cells have no effect. -/
namespace PositiveWeight
open Helix

def advance {α : Type} (edge : α → Bool → α × Int) (s : α × Int) (b : Bool) : α × Int :=
  ((edge s.1 b).1, s.2 + (edge s.1 b).2)

def reader {α : Type} (edge : α → Bool → α × Int) (start : α) (n : Nat) : α × Int :=
  (cells n).foldr (fun b s => advance edge s b) (start,0)

theorem reader_push {α : Type} (edge : α → Bool → α × Int) (start : α)
    (exterior : edge start false = (start,0)) (b : Bool) (n : Nat) :
    reader edge start (push b n) = advance edge (reader edge start n) b := by
  by_cases h : push b n = 0
  · have hz : n = 0 := by cases b <;> simp [push,Bool.toNat] at h <;> omega
    subst n
    cases b with
    | true => contradiction
    | false => simp [reader,h,advance, exterior]
  · have hh : cells (push b n) = b :: cells n := by
      rw [cells]; simp [h]
    simp [reader,hh]

def left := reader edgeL 0
def right := reader edgeR 0

@[simp] theorem left_zero : left 0 = (0,0) := by simp [left,reader]
@[simp] theorem right_zero : right 0 = (0,0) := by simp [right,reader]
theorem left_push (b : Bool) (n : Nat) :
    left (push b n) = advance edgeL (left n) b :=
  reader_push edgeL 0 (by decide) b n
theorem right_push (b : Bool) (n : Nat) :
    right (push b n) = advance edgeR (right n) b :=
  reader_push edgeR 0 (by decide) b n

/-- The invariant tested by the original singleton intervals. -/
def W (c : Cfg) : Prop :=
  guard c.q c.x (left c.l).1 (right c.r).1 = some ((left c.l).2 + (right c.r).2)

theorem blank_mem : W blank := by
  simp only [W,blank,left_zero,right_zero]
  decide

theorem present {c : Cfg} (h : W c) :
    (guard c.q c.x (left c.l).1 (right c.r).1).isSome = true := by
  rw [show guard c.q c.x (left c.l).1 (right c.r).1 = _ from h]
  rfl

private theorem reader_signs {α : Type} (edge : α → Bool → α × Int) (start : α)
    (ge le : α → Bool)
    (signs : ∀ q b, (ge (edge q b).1 = true → ge q = true ∧ 0 ≤ (edge q b).2) ∧
                     (le (edge q b).1 = true → le q = true ∧ (edge q b).2 ≤ 0))
    (n : Nat) :
    (ge (reader edge start n).1 = true → 0 ≤ (reader edge start n).2) ∧
    (le (reader edge start n).1 = true → (reader edge start n).2 ≤ 0) := by
  unfold reader
  induction cells n with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldr_cons,advance]
    let s := bs.foldr (fun b s => advance edge s b) (start,0)
    change (ge (edge s.1 b).1 = true → 0 ≤ s.2 + (edge s.1 b).2) ∧
           (le (edge s.1 b).1 = true → s.2 + (edge s.1 b).2 ≤ 0)
    constructor
    · intro h
      obtain ⟨hprev,hinc⟩ := (signs s.1 b).1 h
      have hpos : 0 ≤ s.2 := ih.1 hprev
      omega
    · intro h
      obtain ⟨hprev,hinc⟩ := (signs s.1 b).2 h
      have hneg : s.2 ≤ 0 := ih.2 hprev
      omega

set_option maxRecDepth 32000 in
set_option maxHeartbeats 1200000 in
private theorem leftTransitions :
    ∀ q b, (nonnegL (edgeL q b).1 = true → nonnegL q = true ∧ 0 ≤ (edgeL q b).2) ∧
           (nonposL (edgeL q b).1 = true → nonposL q = true ∧ (edgeL q b).2 ≤ 0) := by decide

set_option maxRecDepth 32000 in
set_option maxHeartbeats 1200000 in
private theorem rightTransitions :
    ∀ q b, (nonnegR (edgeR q b).1 = true → nonnegR q = true ∧ 0 ≤ (edgeR q b).2) ∧
           (nonposR (edgeR q b).1 = true → nonposR q = true ∧ (edgeR q b).2 ≤ 0) := by decide

theorem leftSigns (n : Nat) :
    (nonnegL (left n).1 = true → 0 ≤ (left n).2) ∧
    (nonposL (left n).1 = true → (left n).2 ≤ 0) :=
  reader_signs edgeL 0 nonnegL nonposL leftTransitions n

theorem rightSigns (n : Nat) :
    (nonnegR (right n).1 = true → 0 ≤ (right n).2) ∧
    (nonposR (right n).1 = true → (right n).2 ≤ 0) :=
  reader_signs edgeR 0 nonnegR nonposR rightTransitions n

end PositiveWeight
