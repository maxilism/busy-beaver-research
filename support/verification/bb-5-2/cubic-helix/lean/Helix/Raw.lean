import Helix.Machine
namespace Helix

/-- Execute exactly this many instructions (fail on premature halt). -/
def run : Nat → Cfg → Option Cfg
  | 0, c => some c
  | n+1, c => (step c).bind (run n)
theorem reach_run (n : Nat) {c d : Cfg} (h : run n c = some d) : Reach c d := by
  induction n generalizing c with
  | zero => cases h; exact .refl _
  | succ n ih =>
    cases e : step c with
    | none => simp [run, e] at h
    | some m => exact .cons e (ih (by simpa [run,e] using h))

private theorem top0 : top 0 = false := rfl
private theorem pop0 : pop 0 = 0 := rfl
private theorem z0 : z 0 = 0 := rfl
/-- Symbolically execute a bounded literal path, never guessing bits of a context. -/
macro "fixed" n:num : tactic => `(tactic|
  (apply reach_run $n; simp [run,step,instruction,F,K,top0,pop0,z0]))

private theorem alpha (l r : Nat) : Reach (F .A l (z (o r))) (F .A (o (z l)) r) := by fixed 4
private theorem beta (l r : Nat) : Reach (K .B (o (z l)) r) (K .B l (o (z r))) := by fixed 2
private theorem gamma (l r : Nat) : Reach (K .C (o (z l)) r) (K .C l (o (z r))) := by fixed 2

theorem zo_snoc (n r : Nat) : zo n (z (o r)) = zo (n+1) r := by
  induction n with | zero => rfl | succ n ih => exact congrArg (fun v => z (o v)) ih
theorem oz_snoc (n r : Nat) : oz n (o (z r)) = oz (n+1) r := by
  induction n with | zero => rfl | succ n ih => exact congrArg (fun v => o (z v)) ih
private theorem alphaN (n l r : Nat) : Reach (F .A l (zo n r)) (F .A (oz n l) r) := by
  induction n generalizing l with
  | zero => exact .refl _
  | succ n ih => exact (alpha _ _).trans (by simpa only [oz_snoc] using ih (o (z l)))
private theorem leftN {q : St}
    (unit : ∀ l r, Reach (K q (o (z l)) r) (K q l (o (z r)))) (n l r : Nat) :
    Reach (K q (oz n l) r) (K q l (oz n r)) := by
  induction n generalizing r with
  | zero => exact .refl _
  | succ n ih => exact (unit _ _).trans (by simpa only [oz_snoc] using ih (o (z r)))

-- Phase changes of the alternating word, for arbitrary lengths and tails.
private theorem phaseO (n r : Nat) : o (zo n r) = oz n (o r) := by
  induction n with | zero => rfl | succ n ih => exact congrArg (fun s => o (z s)) ih
private theorem phaseZ (n r : Nat) : z (oz n r) = zo n (z r) := by
  induction n with | zero => rfl | succ n ih => exact congrArg (fun s => z (o s)) ih

-- The shared scan rows and the constant-size endings use an arbitrary stack
-- on each side: no implicit restriction to the machine's orbit.
private theorem A00 (l r : Nat) : Reach (F .A l (z (z r))) (K .B l (z (o r))) := by fixed 3
private theorem entryScan (f : Wd) (m : Nat) :
    Reach (T f m) (K .B (o (left f)) (oz m (z (o 0)))) := by
  unfold T; rw [phaseO]; exact (A00 _ 0).trans (leftN beta m _ _)
private theorem finish11 (l r : Nat) :
    Reach (K .B (o (o l)) r) (F .D (z l) (z r)) := by fixed 2
private theorem finish00001 (l r : Nat) :
    Reach (K .B (o (z (z (z (z l))))) r) (F .D (z (o l)) (z (o (z r)))) := by fixed 8
private theorem finish000 (l r : Nat) :
    Reach (K .B (z (z (z l))) r) (F .D l (z (z (o r)))) := by fixed 2
private theorem finish00010 (l r : Nat) :
    Reach (K .B (z (o (z (z (z l))))) r) (F .D (z (o l)) (z (z (o r)))) := by fixed 8

private theorem left_app (f g : Wd) : left (f++g) = g.foldl (fun n b => push b n) (left f) :=
  List.foldl_append

theorem entryFour (h : Wd) (m : Nat) :
    Reach (T (h++[false,false,false,false]) m) (P (h++[true,false]) (m+1) 1) := by
  apply (entryScan _ _).trans
  simpa only [P, left_app, List.foldl_cons, List.foldl_nil, oz, ones] using
    finish00001 (left h) (oz m (z (o 0)))
theorem entryOne (h : Wd) (m : Nat) : Reach (T (h++[true]) m) (P (h++[false]) m 1) := by
  apply (entryScan _ _).trans
  simpa only [P, left_app, List.foldl_cons, List.foldl_nil, ones] using
    finish11 (left h) (oz m (z (o 0)))
theorem entryBlank (m : Nat) : Reach (T [] m) (P [true,false] (m+1) 1) := entryFour [] m

private theorem downStart (l r : Nat) : Reach (F .D l (z (o (z r)))) (F .A (o (o l)) (z r)) := by fixed 4

theorem down (f : Wd) (b c : Nat) : Reach (P f (b+1) c) (P (f++[false]) b (c+1)) := by
  apply (downStart (left f) (oz b (z (ones c)))).trans
  rw [phaseZ]; apply (alphaN b _ _).trans
  apply (A00 _ _).trans; apply (leftN beta b _ _).trans
  simpa only [P,left_app,List.foldl_cons,List.foldl_nil,ones] using
    finish11 (left f) (oz b (z (o (ones c))))

private theorem D0 (l r : Nat) : Reach (F .D l (z r)) (F .A (o l) r) := by fixed 1
private theorem A11 (l r : Nat) : Reach (F .A l (o (o r))) (K .C l (o (z r))) := by fixed 3
private theorem C1 (l r : Nat) : Reach (K .C (o l) r) (K .B l (z r)) := by fixed 1
private theorem upScan (f : Wd) (b c : Nat) :
    Reach (Q f b (c+3)) (K .B (left f) (z (oz (b+2) (ones c)))) := by
  apply (D0 _ _).trans
  change Reach (F .A (o (left f)) (z (oz b (o (o (o (ones c))))))) _
  rw [phaseZ,zo_snoc]; apply (alphaN (b+1) _ _).trans
  apply (A11 _ _).trans; apply (leftN gamma (b+1) _ _).trans
  rw [oz_snoc]; exact C1 _ _

theorem upThree (h : Wd) (b c : Nat) :
    Reach (Q (h++[false,false,false]) b (c+3)) (Q h (b+3) c) := by
  apply (upScan _ _ _).trans
  simpa only [Q,left_app,List.foldl_cons,List.foldl_nil,oz] using
    finish000 (left h) (z (oz (b+2) (ones c)))
theorem upFive (h : Wd) (b c : Nat) :
    Reach (Q (h++[false,false,false,true,false]) b (c+3)) (Q (h++[true,false]) (b+3) c) := by
  apply (upScan _ _ _).trans
  simpa only [Q,left_app,List.foldl_cons,List.foldl_nil,oz] using
    finish00010 (left h) (z (oz (b+2) (ones c)))
theorem upMargin (b c : Nat) : Reach (Q [true,false] b (c+3)) (Q [true,false] (b+3) c) :=
  upFive [] b c

theorem exitZero (f : Wd) (b : Nat) : Reach (Q f b 0) (T f b) := by
  apply (D0 _ _).trans
  simp only [T, phaseO, phaseZ,ones,z0]; exact alphaN b _ _
theorem exitOne (f : Wd) (b : Nat) : Reach (Q f b 1) (T f (b+1)) := by
  apply (D0 _ _).trans
  simp only [T, phaseO,phaseZ,ones,zo_snoc]; exact alphaN (b+1) _ _
theorem pqZero (f : Wd) (c : Nat) : P f 0 c = Q f 0 c := rfl
theorem tTen (m : Nat) : T [true,false] m = T [] (m+1) := by
  unfold T; change F _ (o (zo m (z (o 0)))) 0 = _
  rw [zo_snoc]; rfl

theorem up_partial_10001 (b c : Nat) (hc : 3 ≤ c) :
    ∃ t, Reach (Q [true,false,false,false,true] b c) t ∧ Halted t := by
  obtain ⟨k,eq⟩ : ∃ k, c = k+3 := ⟨c-3,by omega⟩
  subst c; let r := z (oz (b+2) (ones k))
  refine ⟨K .D (o 0) (z (o (o (z r)))), (upScan _ _ _).trans ?_,rfl⟩
  change Reach (K .B (o (z (z (z (o 0))))) r) _
  fixed 4

theorem startup6 : run 6 blank = some (F .A (o 0) (z (o (z (o 0))))) := rfl
theorem startup14 : run 14 blank = some (T [] 2) := rfl
theorem blankReachR2 : Reach blank (T [] 2) := reach_run 14 startup14
end Helix
