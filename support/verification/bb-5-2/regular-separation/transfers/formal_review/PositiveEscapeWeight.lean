import PositiveWeightRead
import PositiveSafetyGapBridge

/-! The exceptional source word always gives the same weighted-automaton
endpoints. The certificate has no guard for those endpoints. -/
namespace PositiveEscapeWeight
open Helix

private def next (s : Fin 58) (b : Bool) := (PositiveWeight.edgeL s b).1

private theorem endpointFold (w : Wd) (n : Nat) :
    (PositiveWeight.left (w.foldl (fun a b => push b a) n)).1 =
      w.foldl next (PositiveWeight.left n).1 := by
  induction w generalizing n with
  | nil => rfl
  | cons b w ih =>
    simp only [List.foldl_cons, ih, PositiveWeight.left_push, PositiveWeight.advance, next]

private theorem zeros (i : Nat) :
    (List.replicate (4+3*i) false).foldl next 1 = 11 := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [show 4+3*(i+1) = (4+3*i)+3 by omega, ← List.replicate_append_replicate, List.foldl_append, ih]
    decide

private theorem pairs (j : Nat) :
    (List.replicate (3*j) [false,true]).flatten.foldl next 18 = 18 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 3*(j+1) = 3*j+3 by omega, ← List.replicate_append_replicate, List.flatten_append,
      List.foldl_append, ih]
    decide

private theorem endpoint (i j : Nat) :
    (PositiveWeight.left (Helix.left (true :: (List.replicate (4+3*i) false ++ [true] ++
      (List.replicate (3*j) [false,true]).flatten ++ [false])))).1 = 26 := by
  unfold Helix.left
  rw [endpointFold, PositiveWeight.left_zero]
  simp only [List.foldl_cons, List.foldl_append, List.foldl_nil]
  rw [show next 0 true = 1 by decide, zeros, show next 11 true = 18 by decide, pairs]
  decide

private theorem exceptional (i j : Nat) :
    ¬ PositiveWeight.W ⟨.B, Helix.left (true :: (List.replicate (4+3*i) false ++ [true] ++
      (List.replicate (3*j) [false,true]).flatten ++ [false])), true, [false,true].foldr push 0⟩ := by
  intro h
  have g := PositiveWeight.present h
  change (PositiveWeight.guard .B true _ _).isSome = true at g
  rw [endpoint i j, show (PositiveWeight.right ([false,true].foldr push 0)).1 = 2 by
    simp only [List.foldr_cons, List.foldr_nil, PositiveWeight.right_push, PositiveWeight.right_zero]
    decide] at g
  exact (by decide : ¬ (PositiveWeight.guard .B true 26 2).isSome = true) g

open PositiveSafetyCore PositiveSafetyGapBridge

/-- Every padded spelling of the exceptional source is outside the weighted invariant. -/
theorem notMemOfShape (l : Wd) (q : St) (x : Bool) (r : Wd) (u i j v : Nat)
    (h : wordOf l q x r = List.replicate u (.bit false) ++ PositiveSafetyGap.gapWord i j ++
        List.replicate v (.bit false)) : ¬ PositiveWeight.W (cfgOf l q x r) := by
  rw [gap_spell] at h
  rw [paddingCfg u v h]
  exact exceptional i j

theorem notMemOfExit (l : Wd) (q : St) (x : Bool) (r : Wd)
    (h : PositiveSafetyGapDFA.accepts (wordOf l q x r)) : ¬ PositiveWeight.W (cfgOf l q x r) := by
  obtain ⟨u,i,j,v,e⟩ := PositiveSafetyGapDFA.decode h
  exact notMemOfShape l q x r u i j v e

end PositiveEscapeWeight
