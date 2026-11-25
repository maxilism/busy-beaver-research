import PositiveDFA
import PositiveSafetyGap
import PositiveSafetyCore

/-! Each member of the exceptional family leaves the shipped separator on its
next literal B1 transition. In the original automaton, the zero bank loops at
state 39. The alternating bank ends at either 62 or 174. Both endpoints accept
the B suffix and reject its E successor. -/
namespace PositiveEscapeExact
open Helix PositiveDFA PositiveSafetyGap

private def bank (i j : Nat) : Wd :=
  List.replicate (4+3*i) false ++ [true] ++ (List.replicate (3*j) [false,true]).flatten

private def prefixWord (i j : Nat) := (true :: bank i j).map Sym.bit

private theorem zeros (i : Nat) :
    read start ((true :: List.replicate (4+3*i) false).map Sym.bit) = 39 := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [show 4 + 3*(i+1) = (4+3*i)+3 by omega, ← List.replicate_append_replicate,
      ← List.cons_append, List.map_append, read_append, ih]
    decide

private theorem bankEndpoint (i j : Nat) :
    read start (prefixWord i j) = 62 ∨ read start (prefixWord i j) = 174 := by
  induction j with
  | zero =>
    have h : prefixWord i 0 =
        (true :: List.replicate (4+3*i) false).map Sym.bit ++ [.bit true] := by
      simp [prefixWord,bank]
    rw [h,read_append,zeros]
    exact Or.inl (by decide)
  | succ j ih =>
    have h : prefixWord i (j+1) = prefixWord i j ++
        [.bit false,.bit true,.bit false,.bit true,.bit false,.bit true] := by
      simp only [prefixWord,bank,Nat.mul_succ]
      rw [← List.replicate_append_replicate (a := [false,true]),List.flatten_append]
      simp [List.append_assoc]
    rw [h,read_append]
    rcases ih with h | h <;> rw [h] <;> exact Or.inr (by decide)

private def source (i j : Nat) : Cfg :=
  ⟨.B, left ((true :: bank i j) ++ [false]), true, 2⟩
private def target (i j : Nat) : Cfg :=
  ⟨.E, left (true :: bank i j), false, 4⟩

private theorem cellsTwo : cells 2 = [false,true] := by
  rw [cells, cells]
  simp [pop,top]

private theorem sourceWord (i j : Nat) :
    display (source i j) = prefixWord i j ++ [.bit false,.mark .B,.bit true,.bit false,.bit true] := by
  change (cells (left (true :: (bank i j ++ [false])))).reverse.map Sym.bit ++ _ ++ _ = _
  rw [cellsLeft]
  simp [source,cellsTwo,prefixWord,List.append_assoc]

private theorem targetWord (i j : Nat) :
    display (target i j) = prefixWord i j ++
      [.mark .E,.bit false,.bit false,.bit false,.bit true] := by
  have right : cells 4 = [false,false,true] := by
    rw [cells, dite_eq_right (by decide : 4 ≠ 0)]
    exact congrArg (false :: ·) cellsTwo
  simp [display,target,right,cellsLeft,prefixWord,List.append_assoc]

private theorem sourceShape (i j : Nat) : display (source i j) = gapWord i j := by
  rw [sourceWord]
  simp [gapWord,prefixWord,bank,List.append_assoc]

theorem escapesOfShape {c : Cfg} {i j : Nat} (shape : display c = gapWord i j) :
    accepts c ∧ ∃ d, step c = some d ∧ ¬ accepts d := by
  have eq := displayInjective (shape.trans (sourceShape i j).symm)
  subst c
  refine ⟨?_,target i j,?_,?_⟩
  · change final (read start (display (source i j))) = true
    rw [sourceWord,read_append]
    rcases bankEndpoint i j with h | h <;> rw [h] <;> decide
  · simp only [step,source,target,instruction,K,PositiveSafetyCore.leftSnoc,top_push,pop_push]
    rfl
  · change ¬ final (read start (display (target i j))) = true
    rw [targetWord,read_append]
    rcases bankEndpoint i j with h | h <;> rw [h] <;> decide

theorem existsEscape (i j : Nat) : ∃ c d, display c = gapWord i j ∧
    accepts c ∧ step c = some d ∧ ¬ accepts d := by
  obtain ⟨inside,d,move,outside⟩ := escapesOfShape (sourceShape i j)
  exact ⟨source i j,d,sourceShape i j,inside,move,outside⟩

end PositiveEscapeExact
