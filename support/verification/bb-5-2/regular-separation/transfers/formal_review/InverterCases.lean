import Inverter
import Splice

/-! The two recursive tape rewrites from `Inverter` place every equal-bank
checkpoint on the actual blank run. A second recursion takes every checkpoint
with more right-hand ones than left-hand triples to the missing instruction.
All reachability statements use the step semantics of the chosen literal table. -/
namespace Inverter
open Helix

/-- The tape immediately to the left of the head is (110)^n. -/
def bank : Nat → Nat
  | 0 => 0
  | n+1 => z (o (o (bank n)))

def checkpoint (n m : Nat) : Cfg := F .A (bank n) (ones m)

private theorem bankEndsZero (n : Nat) : ∃ l, bank n = z l := by
  cases n with
  | zero => exact ⟨0, rfl⟩
  | succ n => exact ⟨o (o (bank n)), rfl⟩

private theorem zzPush (k r : Nat) : zz k (z r) = z (zz k r) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [zz, ih]

private theorem ooPush (k r : Nat) : oo k (o r) = o (oo k r) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [oo, ih]

private theorem zzPadding (k : Nat) : zz k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [zz, ih]; rfl

private theorem zoLast (k r : Nat) : zo k (z (o r)) = zo (k+1) r := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun t => z (o t)) ih

/-- Advance the left bank by one triple and move a one to the right bank.
The odd number of recursive pairs used in the manuscript is k+1 here;
the step works for every k. -/
private theorem extendBank (v : Bool) (k l r : Nat) :
    Reach v (F .A (z l) (zz (k+2) r))
      (F .A (z (o (o (z l)))) (zz k (o r))) := by
  have lrule := leftRule v (k+1) l (z (z r))
  have lp : zz (k+1) (z (z r)) = zz (k+2) r := by
    rw [zzPush, zzPush]; rfl
  rw [lp] at lrule
  apply lrule.trans
  apply (tiles v (k+1) (z l) (z (z r))).trans
  apply (turn00 v (oo (k+1) (z l)) r).trans
  have rr := rightRule v k (o (o (o (z l)))) r
  simp only [ooPush] at rr
  apply rr.trans
  exact turn111 v (z l) (zz k (o r))

private theorem extendAll (v : Bool) (k d s : Nat) :
    Reach v (F .A (bank d) (zz (2*k) (ones s)))
      (checkpoint (d+k) (s+k)) := by
  induction k generalizing d s with
  | zero => exact .refl _
  | succ k ih =>
    rcases bankEndsZero d with ⟨l, hl⟩
    have path := extendBank v (2*k) l (ones s)
    have hr : z (o (o (z l))) = bank (d+1) := by rw [bank, hl]
    rw [hr, ← hl] at path
    rw [show 2*(k+1)=2*k+2 by omega]
    apply path.trans
    have tail := ih (d+1) (s+1)
    rw [show d+1+k=d+(k+1) by omega, show s+1+k=s+(k+1) by omega] at tail
    exact tail

theorem diagonalReached (v : Bool) (n : Nat) : Reach v blank (checkpoint n n) := by
  have h := extendAll v n 0 0
  simp only [Nat.zero_add, ones, zzPadding] at h
  exact h

/-- Consume the first one to complete the last rightward tile, while the
second one remains at the boundary for the leftward rewrite. -/
private theorem stripToC (v : Bool) (j l r : Nat) :
    Reach v (F .A (z l) (zz j (z (o (o r)))))
      (K .C (z l) (zz (j+1) (o r))) := by
  apply (leftRule v j l (z (o (o r)))).trans
  rw [zoLast]
  apply (tiles v (j+1) (z l) (o r)).trans
  apply (aOne v (oo (j+1) (z l)) r).trans
  exact rightRule v (j+1) (z l) r

def EventuallyHalts (v : Bool) (s : Cfg) := ∃ c, Reach v s c ∧ step v c = none

private theorem haltsBefore {v a b} (h : Reach v a b) (hb : EventuallyHalts v b) :
    EventuallyHalts v a := by
  obtain ⟨c, p, t⟩ := hb
  exact ⟨c, h.trans p, t⟩

private theorem stripAll (v : Bool) (n j t : Nat) :
    EventuallyHalts v (F .A (bank n) (zz j (z (ones (n+t+2))))) := by
  induction n generalizing j with
  | zero =>
    have c := stripToC v j 0 (ones t)
    rw [Nat.zero_add]
    exact haltsBefore c (deadMargin v _)
  | succ n ih =>
    obtain ⟨l, hl⟩ := bankEndsZero n
    have p := stripToC v j (o (o (bank n))) (ones (n+t+1))
    rw [show n+1+t+2=(n+t+1)+2 by omega]
    apply haltsBefore p
    rw [hl]
    apply haltsBefore (turn110 v l _)
    have ht := ih (j+2)
    rw [hl, zzPush] at ht
    exact ht

theorem rightHeavyHalts (v : Bool) {n m : Nat} (h : n < m) :
    EventuallyHalts v (checkpoint n m) := by
  cases n with
  | zero =>
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    exact haltsBefore (aOne v 0 (ones s)) (deadMargin v _)
  | succ n =>
    let t := m-(n+2)
    have hm : m=n+t+2 := by dsimp [t]; omega
    rw [hm, checkpoint]
    apply haltsBefore (aOne v (bank (n+1)) (ones (n+t+1)))
    obtain ⟨l, hl⟩ := bankEndsZero n
    rw [bank, hl]
    apply haltsBefore (turn110 v l _)
    have ht := stripAll v n 1 t
    rw [hl] at ht
    exact ht

def leftPart (n : Nat) := (cells (bank n)).reverse.map Sym.bit
def rightPart (m : Nat) :=
    [Sym.mark .A, Sym.bit (top (ones m))] ++ (cells (pop (ones m))).map Sym.bit

theorem checkpointWord (n m : Nat) :
    display (checkpoint n m) = leftPart n ++ rightPart m := by
  simp [display, checkpoint, F, leftPart, rightPart, List.append_assoc]

def orbitWords (v : Bool) (w : List Sym) := ∃ c, Reach v blank c ∧ display c = w
def haltingWords (v : Bool) (w : List Sym) := ∃ c, EventuallyHalts v c ∧ display c = w

theorem noOrdinarySeparator (v : Bool) : Splice.NoDFASeparator (orbitWords v) (haltingWords v) :=
  Splice.noSeparator_of_slices leftPart rightPart
    (fun i => ⟨_, diagonalReached v i, checkpointWord i i⟩)
    (fun i j h => Or.inl ⟨_, rightHeavyHalts v h, checkpointWord i j⟩)


/-- The same canonical checkpoints rule out epsilon-NFA separators directly,
without converting the nondeterministic machines to deterministic ones. -/
theorem noENFASeparator (v : Bool) {n : Nat} (a : Splice.ENFA Sym n) :
    ¬ ((∀ w, orbitWords v w → a.accepts w) ∧ (∀ w, haltingWords v w → ¬ a.accepts w)) :=
  Splice.noENFASeparator_of_slices leftPart rightPart
    (fun i => ⟨_, diagonalReached v i, checkpointWord i i⟩)
    (fun i j h => Or.inl ⟨_, rightHeavyHalts v h, checkpointWord i j⟩) a

end Inverter
