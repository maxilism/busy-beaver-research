import PositiveWeightRead
import PositiveWeightCert
import Helix.Nonhalt

/-! The published weighted invariant for #4817065 contains blank, is closed
under the machine step, and excludes every halting configuration. -/
namespace PositiveWeight
open Helix

private theorem actualGuard (c : Cfg) (v : Int)
    (charge : v = (left c.l).2 + (right c.r).2)
    (allowed : guard c.q c.x (left c.l).1 (right c.r).1 = some v ∨
      (((nonnegL (left c.l).1 && nonnegR (right c.r).1) = true ∧ v < 0) ∨
       ((nonposL (left c.l).1 && nonposR (right c.r).1) = true ∧ 0 < v))) : W c := by
  subst v
  rcases allowed with h | ⟨signs, lt⟩ | ⟨signs, lt⟩
  · exact h
  · rw [Bool.and_eq_true] at signs
    have := (leftSigns c.l).1 signs.1
    have := (rightSigns c.r).1 signs.2
    omega
  · rw [Bool.and_eq_true] at signs
    have := (leftSigns c.l).2 signs.1
    have := (rightSigns c.r).2 signs.2
    omega

private theorem moveRight (q p : St) (x w b : Bool) (l r : Nat)
    (raw : instruction q x = some (w,.R,p)) (src : W ⟨q,l,x,push b r⟩) :
    W ⟨p,push w l,b,r⟩ := by
  simp only [W, right_push, advance] at src
  have opt := localRight q x w p raw (left l).1 (right r).1 b _ src
  apply actualGuard _ _ _ (by simpa only [left_push, advance] using opt)
  simp only [left_push, advance]
  omega

private theorem moveLeft (q p : St) (x w b : Bool) (l r : Nat)
    (raw : instruction q x = some (w,.L,p)) (src : W ⟨q,push b l,x,r⟩) :
    W ⟨p,l,b,push w r⟩ := by
  simp only [W, left_push, advance] at src
  have opt := localLeft q x w p raw (left l).1 (right r).1 b _ src
  apply actualGuard _ _ _ (by simpa only [right_push, advance] using opt)
  simp only [right_push, advance]
  omega

theorem closed {c d : Cfg} (h : W c) (hs : step c = some d) : W d := by
  rcases c with ⟨q,l,x,r⟩
  cases raw : instruction q x with
  | none => simp [step,raw] at hs
  | some act =>
    obtain ⟨w, dir, p⟩ := act
    cases dir with
    | R =>
      simp only [step,raw,Option.some.injEq] at hs
      subst d
      exact moveRight q p x w (top r) l (pop r) raw (by simpa only [push_unpack] using h)
    | L =>
      simp only [step,raw,Option.some.injEq] at hs
      subst d
      exact moveLeft q p x w (top l) (pop l) r raw (by simpa only [push_unpack] using h)

theorem excludes_halt {c : Cfg} (h : W c) : ¬ Halted c := by
  rcases c with ⟨q,l,x,r⟩
  cases q <;> cases x <;> simp [Halted,step,instruction]
  simp only [W,noHaltGuard,reduceCtorEq] at h

theorem safe {c : Cfg} (h : W c) : Helix.Obstruction.Safe c := by
  intro d reach
  exact excludes_halt (reach.closed (fun _ _ => closed) h)

end PositiveWeight
