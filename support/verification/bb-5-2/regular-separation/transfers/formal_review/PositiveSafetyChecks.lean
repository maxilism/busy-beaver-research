import PositiveSafetyResidual
import PositiveSafetyCore

/-! A bit in a residual row is acceptance of a common right suffix.
The finite inequalities check each instruction for all left prefixes and
right suffixes simultaneously. -/
namespace PositiveSafetyChecks
open Helix PositiveSafetyResidual PositiveSafetyCore

set_option maxRecDepth 200000
set_option maxHeartbeats 0

private theorem prefixKStep (p : Pre) (b : Bool) :
    preK (nextP p b) = PositiveSafetyAuto.move (preK p) (.bit b) := by
  cases b <;> revert p <;> decide

private theorem prefixHStep (p : Pre) (b : Bool) :
    preH (nextP p b) = PositiveSafetyGapDFA.move (preH p) (.bit b) := by
  cases b <;> revert p <;> decide

private theorem prefixK (l : Wd) (p : Pre) :
    (l.map Sym.bit).foldl PositiveSafetyAuto.move (preK p) = preK (l.foldl nextP p) := by
  induction l generalizing p with
  | nil => rfl
  | cons b l ih => simp only [List.map_cons,List.foldl_cons, ← prefixKStep, ih]

private theorem prefixH (l : Wd) (p : Pre) :
    (l.map Sym.bit).foldl PositiveSafetyGapDFA.move (preH p) = preH (l.foldl nextP p) := by
  induction l generalizing p with
  | nil => rfl
  | cons b l ih => simp only [List.map_cons,List.foldl_cons, ← prefixHStep, ih]

private def suffix : Wd → Suf
  | [] => 0
  | b::r => nextS (suffix r) b

private theorem zeroK (q : PositiveSafetyAuto.State) : (rowK q).testBit 0 = PositiveSafetyAuto.final q := by
  revert q; decide

private theorem zeroH (q : PositiveSafetyGapDFA.State) : (rowH q).testBit 0 = PositiveSafetyGapDFA.final q := by
  revert q; decide

private theorem shiftK (q : PositiveSafetyAuto.State) (i : Suf) (b : Bool) :
    (rowK q).testBit (nextS i b).val = (rowK (PositiveSafetyAuto.move q (.bit b))).testBit i.val := by
  cases b <;> revert i q <;> decide

private theorem shiftH (q : PositiveSafetyGapDFA.State) (i : Suf) (b : Bool) :
    (rowH q).testBit (nextS i b).val = (rowH (PositiveSafetyGapDFA.move q (.bit b))).testBit i.val := by
  cases b <;> revert i q <;> decide

private theorem suffixK (r : Wd) (q : PositiveSafetyAuto.State) :
    PositiveSafetyAuto.final ((r.map Sym.bit).foldl PositiveSafetyAuto.move q) = (rowK q).testBit (suffix r).val := by
  induction r generalizing q with
  | nil => exact (zeroK _).symm
  | cons b r ih => simp only [List.map_cons,List.foldl_cons, suffix, shiftK, ih]

private theorem suffixH (r : Wd) (q : PositiveSafetyGapDFA.State) :
    PositiveSafetyGapDFA.final ((r.map Sym.bit).foldl PositiveSafetyGapDFA.move q) = (rowH q).testBit (suffix r).val := by
  induction r generalizing q with
  | nil => exact (zeroH _).symm
  | cons b r ih => simp only [List.map_cons,List.foldl_cons, suffix, shiftH, ih]

private def midK (p : Pre) (q : St) (x : Bool) :=
  PositiveSafetyAuto.move (PositiveSafetyAuto.move (preK p) (.mark q)) (.bit x)

private def midH (p : Pre) (q : St) (x : Bool) :=
  PositiveSafetyGapDFA.move (PositiveSafetyGapDFA.move (preH p) (.mark q)) (.bit x)

private def check (p : Pre) (q : St) (x b : Bool) : Bool :=
  match instruction q x with
  | none => rowK (midK p q x) == 0
  | some (w,.R,t) =>
    let old := rowK (PositiveSafetyAuto.move (midK p q x) (.bit b))
    let cut := rowH (PositiveSafetyGapDFA.move (midH p q x) (.bit b))
    let succ := rowK (midK (nextP p w) t b)
    old &&& (cut ||| succ) == old
  | some (w,.L,t) =>
    let old := rowK (midK (nextP p b) q x)
    let cut := rowH (midH (nextP p b) q x)
    let succ := rowK (PositiveSafetyAuto.move (midK p t b) (.bit w))
    old &&& (cut ||| succ) == old

private theorem checked (p : Pre) (q : St) (x b : Bool) : check p q x b = true := by
  cases q <;> cases x <;> cases b <;> revert p <;> decide

private theorem bitOfSubset (old cut succ i : Nat)
    (h : old &&& (cut ||| succ) = old) (b : old.testBit i = true) :
    cut.testBit i = true ∨ succ.testBit i = true := by
  have k := congrArg (fun n : Nat => n.testBit i) h
  simpa [Nat.testBit_and,Nat.testBit_or,b] using k

private def pre (l : Wd) : Pre := l.foldl nextP 0
private theorem preSnoc (l : Wd) (b : Bool) : pre (l++[b]) = nextP (pre l) b := by
  simp [pre,List.foldl_append]

private theorem wordK (l r : Wd) (q : St) (x : Bool) :
    PositiveSafetyAuto.K (wordOf l q x r) ↔ (rowK (midK (pre l) q x)).testBit (suffix r).val = true := by
  have h : PositiveSafetyAuto.start = preK 0 := rfl
  simp only [PositiveSafetyAuto.K,PositiveSafetyAuto.read,wordOf,List.foldl_append,h,prefixK,List.foldl_cons,List.foldl_nil,
    suffixK,pre,midK]

private theorem wordH (l r : Wd) (q : St) (x : Bool) :
    PositiveSafetyGapDFA.accepts (wordOf l q x r) ↔ (rowH (midH (pre l) q x)).testBit (suffix r).val = true := by
  have h : PositiveSafetyGapDFA.start = preH 0 := rfl
  simp only [PositiveSafetyGapDFA.accepts,wordOf,List.foldl_append,h,prefixH,List.foldl_cons,List.foldl_nil,
    suffixH,pre,midH]

theorem rules : CutRules PositiveSafetyAuto.K PositiveSafetyGapDFA.accepts where
  stepRight l r q x b w t inst old := by
    have ok := checked (pre l) q x b
    simp only [check,inst,beq_iff_eq] at ok
    simp only [wordK,wordH,suffix,shiftK,shiftH,preSnoc] at old ⊢
    exact bitOfSubset _ _ _ _ ok old
  stepLeft l r q x b w t inst old := by
    have ok := checked (pre l) q x b
    simp only [check,inst,beq_iff_eq] at ok
    simp only [wordK,wordH,suffix,shiftK,preSnoc] at old ⊢
    exact bitOfSubset _ _ _ _ ok old
  terminal l r q x inst old := by
    have ok := checked (pre l) q x false
    simp only [check,inst,beq_iff_eq] at ok
    simp [wordK,ok] at old

end PositiveSafetyChecks
