import PositiveWeightData

/-!
Finite one-step checks for the published weighted invariant of #4817065.
For a right move the right reader loses its last edge and the left reader
gains the edge for the written bit. A left move interchanges these roles.
The two sign alternatives exclude charges inconsistent with the resulting
reader endpoints.
-/
namespace PositiveWeight
open Helix

private def allowed (q : St) (x : Bool) (l : Fin 58) (r : Fin 37) (v : Int) : Prop :=
  guard q x l r = some v ∨
    (((nonnegL l && nonnegR r) = true ∧ v < 0) ∨
     ((nonposL l && nonposR r) = true ∧ 0 < v))

private instance (q : St) (x : Bool) (l : Fin 58) (r : Fin 37) (v : Int) :
    Decidable (allowed q x l r v) := by unfold allowed; infer_instance

private def checkRight (q : St) (x w : Bool) (p : St)
    (l : Fin 58) (r : Fin 37) (b : Bool) : Bool :=
  match guard q x l (edgeR r b).1 with
  | none => true
  | some g => decide (allowed p b (edgeL l w).1 r (g + (edgeL l w).2 - (edgeR r b).2))

private def checkLeft (q : St) (x w : Bool) (p : St)
    (l : Fin 58) (r : Fin 37) (b : Bool) : Bool :=
  match guard q x (edgeL l b).1 r with
  | none => true
  | some g => decide (allowed p b l (edgeR r w).1 (g + (edgeR r w).2 - (edgeL l b).2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem allRight (q : St) (x w : Bool) (p : St)
    (raw : instruction q x = some (w,.R,p)) :
    ∀ (l : Fin 58) (r : Fin 37) (b : Bool), checkRight q x w p l r b = true := by
  cases q <;> cases x <;> simp [instruction] at raw <;> rcases raw with ⟨rfl,rfl⟩ <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem allLeft (q : St) (x w : Bool) (p : St)
    (raw : instruction q x = some (w,.L,p)) :
    ∀ (l : Fin 58) (r : Fin 37) (b : Bool), checkLeft q x w p l r b = true := by
  cases q <;> cases x <;> simp [instruction] at raw <;> rcases raw with ⟨rfl,rfl⟩ <;> decide

theorem localRight (q : St) (x w : Bool) (p : St)
    (raw : instruction q x = some (w,.R,p)) (l : Fin 58) (r : Fin 37) (b : Bool) (g : Int)
    (src : guard q x l (edgeR r b).1 = some g) :
    guard p b (edgeL l w).1 r = some (g + (edgeL l w).2 - (edgeR r b).2) ∨
    (((nonnegL (edgeL l w).1 && nonnegR r) = true ∧ g + (edgeL l w).2 - (edgeR r b).2 < 0) ∨
     ((nonposL (edgeL l w).1 && nonposR r) = true ∧ 0 < g + (edgeL l w).2 - (edgeR r b).2)) := by
  have ok := allRight q x w p raw l r b
  simpa only [checkRight, src, decide_eq_true_eq, allowed] using ok

theorem localLeft (q : St) (x w : Bool) (p : St)
    (raw : instruction q x = some (w,.L,p)) (l : Fin 58) (r : Fin 37) (b : Bool) (g : Int)
    (src : guard q x (edgeL l b).1 r = some g) :
    guard p b l (edgeR r w).1 = some (g + (edgeR r w).2 - (edgeL l b).2) ∨
    (((nonnegL l && nonnegR (edgeR r w).1) = true ∧ g + (edgeR r w).2 - (edgeL l b).2 < 0) ∨
     ((nonposL l && nonposR (edgeR r w).1) = true ∧ 0 < g + (edgeR r w).2 - (edgeL l b).2)) := by
  have ok := allLeft q x w p raw l r b
  simpa only [checkLeft, src, decide_eq_true_eq, allowed] using ok

set_option maxRecDepth 20000 in
theorem noHaltGuard : ∀ (l : Fin 58) (r : Fin 37), guard .D true l r = none := by
  decide

end PositiveWeight
