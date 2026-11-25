import PilotMachine
import InverterCases
import Splice

/-! The literal seven-state row 9,994,819 reaches every checkpoint
`(110)^n A 1^n`. Every right-heavy splice eventually reaches its
undefined instruction. Guards at each helper call witness a one in the
suffix it scans. The same arithmetic tape banks appear in its shadow. -/
namespace Pilot
open Helix (z o zo ones top pop cells)
open Inverter (zz oo bank zz_push oo_push)

def checkpoint (n m : Nat) : Cfg := F .A (bank n) (ones m)

private theorem bankEndsZero (n : Nat) : ∃ l, bank n = z l := by
  cases n with
  | zero => exact ⟨0, rfl⟩
  | succ n => exact ⟨o (o (bank n)), rfl⟩

private theorem zzPadding (k : Nat) : zz k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [zz, ih]; rfl

private theorem zoLast (k r : Nat) : zo k (z (o r)) = zo (k+1) r := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun t => z (o t)) ih

/-- Advance the left bank by one triple and move a one to the right bank.
The marker inside the right stack survives every pair of zero pushes and
guarantees that the final helper call returns. -/
private theorem extendBank (k l r : Nat) :
    Reach (F .A (z l) (zz (k+2) r))
      (F .A (z (o (o (z l)))) (zz k (o r))) := by
  have lrule := leftRule (k+1) l (z (z r))
  have lp : zz (k+1) (z (z r)) = zz (k+2) r := by
    rw [zz_push, zz_push]; rfl
  rw [lp] at lrule
  apply lrule.trans
  apply (tiles (k+1) (z l) (z (z r))).trans
  apply (turn00 (oo (k+1) (z l)) r).trans
  have rr := rightRule k (o (o (o (z l)))) r
  simp only [oo_push] at rr
  apply rr.trans
  exact turn111 (z l) (zz k (o r)) (zz_nonzero k (o_nonzero r))

private theorem extendAll (k d s : Nat) :
    Reach (F .A (bank d) (zz (2*k) (ones s)))
      (checkpoint (d+k) (s+k)) := by
  induction k generalizing d s with
  | zero => exact .refl _
  | succ k ih =>
    rcases bankEndsZero d with ⟨l, hl⟩
    have path := extendBank (2*k) l (ones s)
    have hr : z (o (o (z l))) = bank (d+1) := by rw [bank, hl]
    rw [hr, ← hl] at path
    rw [show 2*(k+1)=2*k+2 by omega]
    apply path.trans
    have tail := ih (d+1) (s+1)
    rw [show d+1+k=d+(k+1) by omega, show s+1+k=s+(k+1) by omega] at tail
    exact tail

theorem diagonalReached (n : Nat) : Reach blank (checkpoint n n) := by
  have h := extendAll n 0 0
  simp only [Nat.zero_add, ones, zzPadding] at h
  exact h

/-- Consume the first one to complete the last rightward tile, while the
second one remains at the boundary for the leftward rewrite. -/
private theorem stripToC (j l r : Nat) :
    Reach (F .A (z l) (zz j (z (o (o r)))))
      (K .C (z l) (zz (j+1) (o r))) := by
  apply (leftRule j l (z (o (o r)))).trans
  rw [zoLast]
  apply (tiles (j+1) (z l) (o r)).trans
  apply (aOne (oo (j+1) (z l)) r).trans
  exact rightRule (j+1) (z l) r

def EventuallyHalts (s : Cfg) := ∃ c, Reach s c ∧ step c = none

private theorem haltsBefore {a b} (h : Reach a b) (hb : EventuallyHalts b) :
    EventuallyHalts a := by
  obtain ⟨c, p, t⟩ := hb
  exact ⟨c, h.trans p, t⟩

private theorem stripAll (n j t : Nat) :
    EventuallyHalts (F .A (bank n) (zz j (z (ones (n+t+2))))) := by
  induction n generalizing j with
  | zero =>
    have c := stripToC j 0 (ones t)
    rw [Nat.zero_add]
    exact haltsBefore c (deadMargin _)
  | succ n ih =>
    obtain ⟨l, hl⟩ := bankEndsZero n
    have p := stripToC j (o (o (bank n))) (ones (n+t+1))
    rw [show n+1+t+2=(n+t+1)+2 by omega]
    apply haltsBefore p
    rw [hl]
    apply haltsBefore (turn110 l _ (zz_nonzero _ (o_nonzero _)))
    have ht := ih (j+2)
    rw [hl, zz_push] at ht
    exact ht

theorem rightHeavyHalts {n m : Nat} (h : n < m) :
    EventuallyHalts (checkpoint n m) := by
  cases n with
  | zero =>
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    exact haltsBefore (aOne 0 (ones s)) (deadMargin _)
  | succ n =>
    let t := m-(n+2)
    have hm : m=n+t+2 := by dsimp [t]; omega
    rw [hm, checkpoint]
    apply haltsBefore (aOne (bank (n+1)) (ones (n+t+1)))
    obtain ⟨l, hl⟩ := bankEndsZero n
    rw [bank, hl]
    apply haltsBefore (turn110 l _ (o_nonzero _))
    have ht := stripAll n 1 t
    rw [hl] at ht
    exact ht

def leftPart (n : Nat) := (cells (bank n)).reverse.map Sym.bit
def rightPart (m : Nat) :=
    [Sym.mark .A, Sym.bit (top (ones m))] ++ (cells (pop (ones m))).map Sym.bit

/-- The split is at the state marker. These identities tie the arithmetic
checkpoints to the literal tape fragments emitted by the experiment. -/
theorem leftPart_zero : leftPart 0 = [] := by simp [leftPart, bank]

theorem leftPart_succ (n : Nat) :
    leftPart (n+1) = leftPart n ++ [.bit true, .bit true, .bit false] := by
  have cellsCons (b : Bool) (v : Nat) (h : Helix.push b v ≠ 0) :
      cells (Helix.push b v) = b :: cells v := by
    rw [Helix.cells]
    simp only [dite_eq_right h, Helix.top_push, Helix.pop_push]
  have nz : z (o (o (bank n))) ≠ 0 := by simp [z, o, Helix.push, Bool.toNat]
  simp only [leftPart, bank, cellsCons false _ nz, cellsCons true _ (o_nonzero _),
    List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
    List.cons_append, List.nil_append]

theorem rightPart_zero : rightPart 0 = [.mark .A, .bit false] := by simp [rightPart, ones, top, pop]

theorem rightPart_succ (n : Nat) :
    rightPart (n+1) = .mark .A :: List.replicate (n+1) (.bit true) := by
  simp [rightPart, ones, List.replicate_succ]

theorem checkpointWord (n m : Nat) :
    display (checkpoint n m) = leftPart n ++ rightPart m := by
  simp [display, checkpoint, F, leftPart, rightPart, List.append_assoc]

def orbitWords (w : List Sym) := ∃ c, Reach blank c ∧ display c = w
def haltingWords (w : List Sym) := ∃ c, EventuallyHalts c ∧ display c = w

theorem noOrdinarySeparator : Splice.NoDFASeparator orbitWords haltingWords :=
  Splice.noSeparator_of_slices leftPart rightPart
    (fun i => ⟨_, diagonalReached i, checkpointWord i i⟩)
    (fun i j h => Or.inl ⟨_, rightHeavyHalts h, checkpointWord i j⟩)

/-- The same canonical checkpoints rule out epsilon-NFA separators directly,
without converting the nondeterministic machines to deterministic ones. -/
theorem noENFASeparator {n : Nat} (a : Splice.ENFA Sym n) :
    ¬ ((∀ w, orbitWords w → a.accepts w) ∧ (∀ w, haltingWords w → ¬ a.accepts w)) :=
  Splice.noENFASeparator_of_slices leftPart rightPart
    (fun i => ⟨_, diagonalReached i, checkpointWord i i⟩)
    (fun i j h => Or.inl ⟨_, rightHeavyHalts h, checkpointWord i j⟩) a

end Pilot
