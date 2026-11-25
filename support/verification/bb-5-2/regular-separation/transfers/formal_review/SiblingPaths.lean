import Helix.Paths

/-! The extra two-right-ones case in the sibling cubic helices. All local
    paths below are evaluated against the literal instructions in Helix.Raw. -/
namespace Helix.Siblings
open Obstruction

private theorem phaseOne (n r : Nat) : o (zo n r) = oz n (o r) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun a => o (z a)) ih

private theorem phaseZero (n r : Nat) : z (oz n r) = zo n (z r) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun a => z (o a)) ih

/-- Move A to the right across n copies of 01. -/
private theorem forwardTiles (n l r : Nat) : Reach (F .A l (zo n r)) (F .A (oz n l) r) := by
  induction n generalizing l with
  | zero => exact .refl _
  | succ n ih =>
    have tile : Reach (F .A l (z (o (zo n r)))) (F .A (o (z l)) (zo n r)) := by fixed 4
    exact tile.trans (by simpa only [oz_snoc] using ih (o (z l)))

/-- The common entry position used for the two different starting states. -/
theorem entryScan (f : Wd) (m : Nat) :
    Reach (T f m) (K .B (o (left f)) (oz m (z (o 0)))) := by
  have across (n l r : Nat) : Reach (K .B (oz n l) r) (K .B l (oz n r)) := by
    induction n generalizing r with
    | zero => exact .refl _
    | succ n ih =>
      have tile : Reach (K .B (o (z (oz n l))) r) (K .B (oz n l) (o (z r))) := by fixed 2
      exact tile.trans (by simpa only [oz_snoc] using ih (o (z r)))
  unfold T
  rw [phaseOne]
  apply Reach.trans _ (across m (o (left f)) _)
  fixed 3

/-- Move B left across n copies of 10. -/
private theorem backwardTiles (n l r : Nat) : Reach (K .B (zo n l) r) (K .B l (zo n r)) := by
  induction n generalizing r with
  | zero => exact .refl _
  | succ n ih =>
    have tile : Reach (K .B (z (o (zo n l))) r) (K .B (zo n l) (z (o r))) := by fixed 2
    exact tile.trans (by simpa only [zo_snoc] using ih (z (o r)))

private def turnTail := o (z (o (z (z (o 0)))))

/-- The finite right-margin turn, with an arbitrary left stack. -/
private theorem rightTurn (j : Nat) : Reach (F .A (o j) (o 0)) (K .B j turnTail) := by
  have a : Reach (F .A (o j) (o 0)) (F .A (o (o j)) 0) := by fixed 3
  have b : Reach (F .A (o (o j)) 0) (F .D (z j) (z (z (o 0)))) := by fixed 5
  have c : Reach (F .D (z j) (z (z (o 0)))) (F .A (o (z (o (z j)))) 0) := by fixed 5
  apply (a.trans (b.trans c)).trans
  unfold turnTail
  fixed 7

/-- After the right scan and the right-margin turn B returns to the prefix
    h100. The final two instructions put D on its one, for every b including zero. -/
theorem residualTwoHalts (h : Wd) (b : Nat) :
    ∃ t, Reach (Q (h++[true,false,false]) b 2) t ∧ Halted t := by
  let l := z (z (o (left h)))
  let tail := zo (b+1) turnTail
  have first : Reach (F .D l (z (z (oz b (ones 2)))))
      (F .A (o l) (z (oz b (ones 2)))) := by fixed 1
  have right : z (oz b (ones 2)) = zo (b+1) (o 0) := by
    rw [phaseZero, ← zo_snoc]; rfl
  rw [right] at first
  have runToTurn := first.trans (forwardTiles (b+1) (o l) (o 0))
  rw [← phaseOne] at runToTurn
  have returnB := (runToTurn.trans (rightTurn _)).trans (backwardTiles (b+1) l turnTail)
  have finish : Reach (K .B l tail) (K .D (o (left h)) (z (o tail))) := by
    dsimp only [l]
    fixed 2
  refine ⟨K .D (o (left h)) (z (o tail)), ?_, ?_⟩
  · have result := returnB.trans finish
    simpa only [← right, Q, l, left, List.foldl_append, List.foldl_cons, List.foldl_nil] using result
  · simp [Halted, step, K, instruction]

private theorem extAppend (x : Wd) (a b : Nat) : ext0 (ext0 x a) b = ext0 x (a+b) := by
  simp [ext0]

/-- Four or more excess zeros lead from an arbitrary prefix to the residual-two halt. -/
theorem hybridHalts (f : Wd) (i excess : Nat) (he : 4 ≤ excess) :
    ∃ t, Reach (Q (ext0 f (3*i+excess)) 0 (3*i)) t ∧ Halted t := by
  let h := ext0 f (excess-4)
  have u := upAll (ext0 h 4) i 0 0
  simp only [Nat.zero_add, extAppend, h, show excess-4+4+3*i=3*i+excess by omega] at u
  have e := entryFour h (3*i)
  have d := downAll (h++[true,false]) (3*i+1) 1
  have up := upAll (h++[true,false,false]) i 0 2
  have left1 : h++[true,false] = ext0 (h++[true]) 1 := by simp [ext0]
  have left2 : h++[true,false,false] = ext0 (h++[true]) 2 := by simp [ext0]
  rw [left1] at e
  rw [left1, extAppend] at d
  rw [left2, extAppend] at up
  simp only [Nat.zero_add, show 1+(3*i+1)=2+3*i by omega] at d up
  obtain ⟨t, endPath, halted⟩ := residualTwoHalts h (3*i)
  rw [left2] at endPath
  refine ⟨t, u.trans ((exitZero _ _).trans ?_), halted⟩
  rw [← extAppend f (excess-4) 4]
  change Reach (T (ext0 h 4) (3*i)) t
  exact e.trans (d.trans (up.trans endPath))

/-- With exactly three excess zeros, the anchor one is exposed directly. -/
theorem hybridThreeHalts (g : Wd) (i : Nat) :
    ∃ t, Reach (Q (ext0 (g++[true]) (3*i+3)) 0 (3*i)) t ∧ Halted t := by
  let f := ext0 (g++[true]) 3
  let r := oz (3*i) (z (o 0))
  have up := upAll f i 0 0
  simp only [Nat.zero_add] at up
  have start := (up.trans (exitZero _ _)).trans (entryScan f (3*i))
  have head : left f = z (z (z (o (left g)))) := by
    simp [f, ext0, left, List.foldl_append]
  rw [head] at start
  have finish : Reach (K .B (o (z (z (z (o (left g)))))) r)
      (K .D (o (left g)) (z (o (o (z r))))) := by fixed 4
  refine ⟨K .D (o (left g)) (z (o (o (z r)))), ?_, ?_⟩
  · simpa only [f, extAppend, Nat.add_comm 3 (3*i)] using start.trans finish
  · simp [Halted, step, K, instruction]

/-- Every left-heavy splice on the full positive-multiple-of-three diagonal halts. -/
theorem leftHeavyHalts (g : Wd) (i j : Nat) (hij : i < j) :
    ∃ t, Reach (Q (ext0 (g++[true]) (3*j)) 0 (3*i)) t ∧ Halted t := by
  by_cases next : j = i+1
  · simpa only [next, Nat.mul_succ] using hybridThreeHalts g i
  · have path := hybridHalts (g++[true]) i (3*j-3*i) (by omega)
    simpa only [show 3*i+(3*j-3*i)=3*j by omega] using path

end Helix.Siblings
