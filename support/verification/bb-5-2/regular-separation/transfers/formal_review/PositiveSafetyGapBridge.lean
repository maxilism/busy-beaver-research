import PositiveSafetyGap
import PositiveSafetyCore
import PositiveSafetyGapDFA

/-! Erasing exterior zero padding preserves the configuration represented by
a word. The left and right stacks may therefore be read from any padded
spelling of the exceptional configuration. -/

namespace PositiveSafetyGapBridge
open Helix PositiveSafetyCore

private theorem spell_inj {l s : Wd} {q t : St} {b y : Bool} {r u : Wd}
    (heq : wordOf l q b r = wordOf s t y u) : l = s ∧ q = t ∧ b = y ∧ r = u := by
  induction l generalizing s with
  | nil =>
    cases s with
    | nil =>
      simp [wordOf] at heq
      exact ⟨rfl, heq.1, heq.2.1, (List.map_inj_right (fun _ _ e => Sym.bit.inj e)).mp heq.2.2⟩
    | cons v s => simp [wordOf] at heq
  | cons a l ih =>
    cases s with
    | nil => simp [wordOf] at heq
    | cons v s =>
      change Sym.bit a :: wordOf l q b r = Sym.bit v :: wordOf s t y u at heq
      obtain ⟨av, tail⟩ := List.cons.inj heq
      obtain ⟨ls,qt,by',ru⟩ := ih tail
      cases av
      exact ⟨congrArg _ ls, qt, by', ru⟩

private theorem left_pad (n : Nat) (l : Wd) :
    left (List.replicate n false ++ l) = left l := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, left, push] using ih

private theorem right_pad (n : Nat) (r : Wd) :
    (r ++ List.replicate n false).foldr push 0 = r.foldr push 0 := by
  have zeros : (List.replicate n false).foldr push 0 = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih, push]
  simp [List.foldr_append, zeros]

theorem paddingCfg {l r a d : Wd} {q s : St} {x y : Bool} (u v : Nat)
    (h : wordOf l q x r = List.replicate u (.bit false) ++ wordOf a s y d ++
                         List.replicate v (.bit false)) :
    cfgOf l q x r = cfgOf a s y d := by
  have eq : wordOf l q x r = wordOf (List.replicate u false ++ a) s y
                                (d ++ List.replicate v false) := by
    simpa [wordOf, List.append_assoc] using h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := spell_inj eq
  simp only [cfgOf, left_pad, right_pad]

def bankTail (i j : Nat) : Wd :=
  List.replicate (4+3*i) false ++ [true] ++ (List.replicate (3*j) [false,true]).flatten ++ [false]

theorem gap_spell (i j : Nat) :
    PositiveSafetyGap.gapWord i j = wordOf (true :: bankTail i j) .B true [false,true] := by
  simp [bankTail, wordOf, PositiveSafetyGap.gapWord, List.append_assoc]

private theorem gap_display (i j : Nat) :
    display (cfgOf (true :: bankTail i j) .B true [false,true]) = PositiveSafetyGap.gapWord i j := by
  rw [gap_spell]
  simp only [display, cfgOf, cellsLeft, wordOf]
  have small : cells 2 = [false,true] := by
    rw [cells, dite_eq_right (by decide : 2 ≠ 0)]
    change false :: cells 1 = _
    rw [cells, dite_eq_right (by decide : 1 ≠ 0)]
    change false :: true :: cells 0 = _
    rw [cells0]
  rw [show [false,true].foldr push 0 = 2 by rfl, small]

theorem configOfShape (l : Wd) (q : St) (x : Bool) (r : Wd) (u i j v : Nat)
    (h : wordOf l q x r = List.replicate u (.bit false) ++ PositiveSafetyGap.gapWord i j ++
        List.replicate v (.bit false)) : display (cfgOf l q x r) = PositiveSafetyGap.gapWord i j := by
  rw [gap_spell] at h
  rw [paddingCfg u v h]
  exact gap_display i j

theorem gap_safe_padded (l : Wd) (q : St) (x : Bool) (r : Wd)
    (h : PositiveSafetyGapDFA.accepts (wordOf l q x r)) : Helix.Obstruction.Safe (cfgOf l q x r) := by
  obtain ⟨u,i,j,v,e⟩ := PositiveSafetyGapDFA.decode h
  exact PositiveSafetyGap.wordGapSafe i j (configOfShape l q x r u i j v e)

end PositiveSafetyGapBridge
