import Helix.Tape

/-! Shift recursions for BB(5) #12781955 and #12699987 on the literal
two-way tape. The flag selects the B0 instruction, the only difference. -/
namespace Inverter
open Helix

def instruction (variant : Bool) : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true  => some (true, .L, .C)
  | .B, false => some (true, .L, if variant then .B else .C)
  | .B, true  => some (true, .R, .A)
  | .C, false => some (false, .L, .E)
  | .C, true  => some (false, .L, .D)
  | .D, false => some (false, .R, .A)
  | .D, true  => some (true, .R, .D)
  | .E, false => none
  | .E, true  => some (false, .L, .C)

/-- Render the ten instructions in the catalog's literal format. -/
private def catalogCode (v : Bool) : String := Id.run do
  let stateLetter : St → String
    | .A => "A" | .B => "B" | .C => "C" | .D => "D" | .E => "E"
  let encode (q : St) (bit : Bool) :=
    match instruction v q bit with
    | none => "---"
    | some (w, dir, p) =>
      (if w then "1" else "0") ++ (match dir with | .L => "L" | .R => "R") ++ stateLetter p
  return String.intercalate "_" ([St.A,.B,.C,.D,.E].map fun q => encode q false ++ encode q true)

theorem catalog_12781955 :
    catalogCode false = "1RB1LC_1LC1RA_0LE0LD_0RA1RD_---0LC" := by decide

theorem catalog_12699987 :
    catalogCode true = "1RB1LC_1LB1RA_0LE0LD_0RA1RD_---0LC" := by decide

def step (v : Bool) (c : Cfg) : Option Cfg :=
  match instruction v c.q c.x with
  | none => none
  | some (w, .R, q) => some (F q (push w c.l) c.r)
  | some (w, .L, q) => some (K q c.l (push w c.r))

inductive Reach (v : Bool) : Cfg → Cfg → Prop where
  | refl (c) : Reach v c c
  | cons {c d e} : step v c = some d → Reach v d e → Reach v c e

theorem Reach.trans {v c d e} (p : Reach v c d) (q : Reach v d e) : Reach v c e := by
  induction p with
  | refl => exact q
  | cons a _ ih => exact .cons a (ih q)

def run (v : Bool) : Nat → Cfg → Option Cfg
  | 0,c => some c
  | k+1,c => (step v c).bind (run v k)

theorem ofRun (v k) {c e} (h : run v k c = some e) : Reach v c e := by
  induction k generalizing c with
  | zero => cases h; exact .refl _
  | succ k ih =>
    cases hstep : step v c with
    | none => simp [run,hstep] at h
    | some d => exact .cons hstep (ih (by simpa [run,hstep] using h))

theorem topZero : top 0 = false := rfl
theorem popZero : pop 0 = 0 := rfl
theorem zZero : z 0 = 0 := rfl

macro "invfixed" n:num : tactic => `(tactic|
  (apply Inverter.ofRun _ $n
   simp [Inverter.run, Inverter.step, Inverter.instruction, Helix.F, Helix.K,
      Inverter.topZero, Inverter.popZero, Inverter.zZero]))

def zz : Nat → Nat → Nat
  | 0, r => r
  | k+1, r => z (z (zz k r))

def oo : Nat → Nat → Nat
  | 0, l => l
  | k+1, l => o (o (oo k l))

theorem zz_snoc (k r) : zz k (z (z r)) = zz (k+1) r := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun s => z (z s)) ih

theorem oo_snoc (k l) : oo k (o (o l)) = oo (k+1) l := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun s => o (o s)) ih

theorem zz_push (k r) : zz k (z r) = z (zz k r) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun s => z (z s)) ih

theorem oo_push (k l) : oo k (o l) = o (oo k l) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun s => o (o s)) ih

private theorem zo_snoc (k r) : zo k (z (o r)) = zo (k+1) r := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun s => z (o s)) ih

/-- Cross from left to right through one or more copies of 01, writing 11. -/
theorem tiles (v : Bool) (k l r : Nat) :
    Reach v (F .A l (zo k r)) (F .A (oo k l) r) := by
  induction k generalizing l with
  | zero => exact .refl _
  | succ k ih =>
    have first : Reach v (F .A l (zo (k+1) r)) (F .A (o (o l)) (zo k r)) := by
      change Reach v (F .A l (z (o (zo k r)))) _
      invfixed 2
    exact first.trans (by simpa only [oo_snoc] using ih (o (o l)))

/-- A0,B0 on the original table. The other table takes two extra steps:
the new B scans the one just written by A0, and B1,A1 restore the endpoint. -/
theorem turn00 (v : Bool) (l r : Nat) :
    Reach v (F .A l (z (z r))) (K .C (o l) (o r)) := by
  cases v
  · invfixed 2
  · invfixed 4

theorem turn111 (v : Bool) (l r : Nat) :
    Reach v (K .C (o (o (o l))) r) (F .A (z (o (o l))) r) := by
  invfixed 3

theorem turn110 (v : Bool) (l r : Nat) :
    Reach v (K .C (z (o (o (z l)))) r) (F .A (z l) (z (z (z r)))) := by
  invfixed 4

theorem aOne (v : Bool) (l r : Nat) :
    Reach v (F .A l (o r)) (K .C l (o r)) := by invfixed 1

theorem deadMargin (v : Bool) (r : Nat) :
    ∃ c, Reach v (K .C 0 r) c ∧ step v c = none := by
  refine ⟨K .E 0 (z r), ?_, ?_⟩
  · invfixed 1
  · rfl

private theorem endI (v : Bool) (l r : Nat) :
    Reach v (K .C (o (z l)) r) (F .A (z l) (z r)) := by invfixed 2

private theorem startJ (v : Bool) (l r : Nat) :
    Reach v (K .C (o (o l)) r) (F .A (z (o l)) r) := by invfixed 3

private theorem endJ (v : Bool) (l r : Nat) :
    Reach v (K .C (z (o l)) r) (K .C l (z (z r))) := by invfixed 2

/-- Georgiev's two recursions, proved together on both literal tables.
The arbitrary outer stacks ensure every application preserves its context. -/
theorem shifts (v : Bool) (k : Nat) :
    (∀ l r, Reach v (F .A (z l) (zz k r)) (F .A (z l) (zo k r))) ∧
    (∀ l r, Reach v (K .C (oo k l) (o r)) (K .C l (zz k (o r)))) := by
  induction k with
  | zero => exact ⟨fun _ _ => .refl _, fun _ _ => .refl _⟩
  | succ k ih =>
    obtain ⟨I,J⟩ := ih
    constructor
    · intro l r
      rw [← zz_snoc]
      apply (I l (z (z r))).trans
      apply (tiles v k (z l) (z (z r))).trans
      apply (turn00 v _ _).trans
      rw [← oo_push]
      apply (J _ _).trans
      apply (endI v _ _).trans
      rw [← zz_push, ← zo_snoc]
      exact I _ _
    · intro l r
      rw [← oo_snoc]
      apply (J _ _).trans
      apply (startJ v _ _).trans
      apply (I _ _).trans
      apply (tiles v k _ _).trans
      apply (aOne v _ _).trans
      apply (J _ _).trans
      exact endJ v _ _

theorem leftRule (v : Bool) (k l r : Nat) :
    Reach v (F .A (z l) (zz k r)) (F .A (z l) (zo k r)) := (shifts v k).1 l r

theorem rightRule (v : Bool) (k l r : Nat) :
    Reach v (K .C (oo k l) (o r)) (K .C l (zz k (o r))) := (shifts v k).2 l r

end Inverter
