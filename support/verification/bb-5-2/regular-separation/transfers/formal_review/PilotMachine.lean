import Inverter

/-! Literal seven-state table at row 9994819 of the 15,743,264-row holdout file.
The D0 instruction invokes a reversible scan to its right. A set bit on that
side guarantees return; an empty side instead stays in the scanning state.
The two inverter recursions below account for every invocation. -/
namespace Pilot
open Helix (Dir push top pop z o zo ones cells top_push pop_push)
open Inverter (zz oo zz_push oo_push zz_snoc oo_snoc)

inductive St where | A | B | C | D | E | F | G deriving DecidableEq, Repr
structure Cfg where
  q : St
  l : Nat
  x : Bool
  r : Nat
  deriving DecidableEq, Repr

def F (q : St) (l r : Nat) : Cfg := ⟨q,l,top r,pop r⟩
def K (q : St) (l r : Nat) : Cfg := ⟨q,pop l,top l,r⟩
def blank : Cfg := F .A 0 0

inductive Sym where | bit (b : Bool) | mark (s : St) deriving DecidableEq, Repr
def display (c : Cfg) : List Sym :=
  (cells c.l).reverse.map Sym.bit ++ [Sym.mark c.q, Sym.bit c.x] ++ (cells c.r).map Sym.bit

def instruction : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true  => some (true, .L, .C)
  | .B, false => some (true, .L, .C)
  | .B, true  => some (true, .R, .A)
  | .C, false => some (false, .L, .G)
  | .C, true  => some (false, .L, .D)
  | .D, false => some (false, .R, .E)
  | .D, true  => some (true, .R, .D)
  | .E, false => some (true, .R, .E)
  | .E, true  => some (true, .L, .F)
  | .F, false => some (false, .R, .A)
  | .F, true  => some (false, .L, .F)
  | .G, false => none
  | .G, true  => some (false, .L, .C)

def catalogCode : String := Id.run do
  let letter : St → String
    | .A => "A" | .B => "B" | .C => "C" | .D => "D"
    | .E => "E" | .F => "F" | .G => "G"
  let encode (q : St) (b : Bool) :=
    match instruction q b with
    | none => "---"
    | some (w,d,p) => (if w then "1" else "0") ++ (match d with | .L => "L" | .R => "R") ++ letter p
  return String.intercalate "_" ([St.A,.B,.C,.D,.E,.F,.G].map fun q => encode q false ++ encode q true)

theorem literal9994819 :
    catalogCode = "1RB1LC_1LC1RA_0LG0LD_0RE1RD_1RE1LF_0RA0LF_---0LC" := by decide

def step (c : Cfg) : Option Cfg :=
  match instruction c.q c.x with
  | none => none
  | some (w,.R,q) => some (F q (push w c.l) c.r)
  | some (w,.L,q) => some (K q c.l (push w c.r))

inductive Reach : Cfg → Cfg → Prop where
  | refl (c) : Reach c c
  | cons {c d e} : step c = some d → Reach d e → Reach c e

theorem Reach.trans {c d e} (p : Reach c d) (q : Reach d e) : Reach c e := by
  induction p with
  | refl => exact q
  | cons a _ ih => exact .cons a (ih q)

def run : Nat → Cfg → Option Cfg
  | 0,c => some c
  | k+1,c => (step c).bind (run k)

theorem ofRun (k) {c e} (h : run k c = some e) : Reach c e := by
  induction k generalizing c with
  | zero => cases h; exact .refl _
  | succ k ih =>
    cases ht : step c with
    | none => simp [run,ht] at h
    | some d => exact .cons ht (ih (by simpa [run,ht] using h))

macro "pilotSteps" n:num : tactic => `(tactic|
  (apply Pilot.ofRun $n
   simp [Pilot.run, Pilot.step, Pilot.instruction, Pilot.F, Pilot.K,
     Inverter.topZero, Inverter.popZero, Inverter.zZero]))

private def zeros : Nat → Nat → Nat
  | 0,r => r
  | k+1,r => z (zeros k r)

private theorem firstOne {r : Nat} (h : r ≠ 0) : ∃ k s, r = zeros k (o s) := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    have unpack := Helix.push_unpack r
    cases hx : top r with
    | true =>
      exact ⟨0, pop r, by simpa only [zeros, hx] using unpack.symm⟩
    | false =>
      rw [hx] at unpack
      change z (pop r) = r at unpack
      have lt : pop r < r := by unfold pop; omega
      have nz : pop r ≠ 0 := by intro eq; rw [eq] at unpack; exact h unpack.symm
      obtain ⟨k,s,eq⟩ := ih (pop r) lt nz
      exact ⟨k+1,s,by rw [zeros, ← eq, unpack]⟩

/-- E marks zeros up to the first one; F reverses those marks until the
original D0 sentinel. The tape beyond that first one is arbitrary. -/
private theorem scanRestore (k l r : Nat) :
    Reach (F .E l (zeros k (o r))) (K .F l (zeros k (o r))) := by
  induction k generalizing l with
  | zero => change Reach (F .E l (o r)) (K .F l (o r)); pilotSteps 1
  | succ k ih =>
    change Reach (F .E l (z (zeros k (o r)))) (K .F l (z (zeros k (o r))))
    have out : Reach (F .E l (z (zeros k (o r)))) (F .E (o l) (zeros k (o r))) := by pilotSteps 1
    apply out.trans ((ih (o l)).trans ?_)
    pilotSteps 1

/-- On exactly the guarded branch used below, D0 returns with its entire
original tape intact and its head one cell to the right in A. -/
theorem detour (l r : Nat) (h : r ≠ 0) : Reach (F .D l (z r)) (F .A (z l) r) := by
  obtain ⟨k,s,rfl⟩ := firstOne h
  apply Reach.trans (d := F .E (z l) (zeros k (o s)))
  · pilotSteps 1
  apply (scanRestore k (z l) s).trans
  pilotSteps 1

def marked : Nat → Nat → Nat
  | 0,l => l
  | k+1,l => marked k (o l)

/-- If D0 sees no one anywhere to its right, E advances on blank zeros
forever. This case cannot be substituted by a returning shadow step. -/
theorem emptyScan (k l : Nat) : run k (F .E l 0) = some (F .E (marked k l) 0) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih => exact ih (o l)

theorem o_nonzero (r : Nat) : o r ≠ 0 := by simp [o,push,Bool.toNat]
theorem z_nonzero {r : Nat} (h : r ≠ 0) : z r ≠ 0 := by simp [z,push,Bool.toNat]; omega
theorem zz_nonzero (k : Nat) {r : Nat} (h : r ≠ 0) : zz k r ≠ 0 := by
  induction k with
  | zero => exact h
  | succ k ih => exact z_nonzero (z_nonzero ih)

theorem tiles (k l r : Nat) : Reach (F .A l (zo k r)) (F .A (oo k l) r) := by
  induction k generalizing l with
  | zero => exact .refl _
  | succ k ih =>
    have first : Reach (F .A l (zo (k+1) r)) (F .A (o (o l)) (zo k r)) := by
      change Reach (F .A l (z (o (zo k r)))) _
      pilotSteps 2
    exact first.trans (by simpa only [oo_snoc] using ih (o (o l)))

theorem turn00 (l r : Nat) : Reach (F .A l (z (z r))) (K .C (o l) (o r)) := by
  pilotSteps 2

theorem turn111 (l r : Nat) (h : r ≠ 0) :
    Reach (K .C (o (o (o l))) r) (F .A (z (o (o l))) r) := by
  apply Reach.trans (d := F .D (o (o l)) (z r))
  · pilotSteps 2
  exact detour (o (o l)) r h

theorem turn110 (l r : Nat) (h : r ≠ 0) :
    Reach (K .C (z (o (o (z l)))) r) (F .A (z l) (z (z (z r)))) := by
  apply Reach.trans (d := F .D l (z (z (z (z r)))))
  · pilotSteps 3
  exact detour l _ (z_nonzero (z_nonzero (z_nonzero h)))

theorem aOne (l r : Nat) : Reach (F .A l (o r)) (K .C l (o r)) := by pilotSteps 1

theorem deadMargin (r : Nat) : ∃ c, Reach (K .C 0 r) c ∧ step c = none := by
  refine ⟨K .G 0 (z r), ?_, ?_⟩
  · pilotSteps 1
  · rfl

private theorem endI (l r : Nat) (h : r ≠ 0) :
    Reach (K .C (o (z l)) r) (F .A (z l) (z r)) := by
  apply Reach.trans (d := F .D l (z (z r)))
  · pilotSteps 1
  exact detour l _ (z_nonzero h)

private theorem startJ (l r : Nat) (h : r ≠ 0) :
    Reach (K .C (o (o l)) r) (F .A (z (o l)) r) := by
  apply Reach.trans (d := F .D (o l) (z r))
  · pilotSteps 2
  exact detour (o l) _ h

private theorem endJ (l r : Nat) :
    Reach (K .C (z (o l)) r) (K .C l (z (z r))) := by pilotSteps 2

private theorem zo_snoc (k r : Nat) : zo k (z (o r)) = zo (k+1) r := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun s => z (o s)) ih

/-- Both recursive shifts generate a protecting one before every D0 invocation,
including when the original right exterior has no one at all. -/
theorem shifts (k : Nat) :
    (∀ l r, Reach (F .A (z l) (zz k r)) (F .A (z l) (zo k r))) ∧
    (∀ l r, Reach (K .C (oo k l) (o r)) (K .C l (zz k (o r)))) := by
  induction k with
  | zero => exact ⟨fun _ _ => .refl _, fun _ _ => .refl _⟩
  | succ k ih =>
    obtain ⟨I,J⟩ := ih
    constructor
    · intro l r
      rw [← zz_snoc]
      apply (I l (z (z r))).trans
      apply (tiles k (z l) (z (z r))).trans
      apply (turn00 _ _).trans
      rw [← oo_push]
      apply (J _ _).trans
      apply (endI _ _ (zz_nonzero k (o_nonzero _))).trans
      rw [← zz_push, ← zo_snoc]
      exact I _ _
    · intro l r
      rw [← oo_snoc]
      apply (J _ _).trans
      apply (startJ _ _ (zz_nonzero k (o_nonzero _))).trans
      apply (I _ _).trans
      apply (tiles k _ _).trans
      apply (aOne _ _).trans
      apply (J _ _).trans
      exact endJ _ _

theorem leftRule (k l r : Nat) :
    Reach (F .A (z l) (zz k r)) (F .A (z l) (zo k r)) := (shifts k).1 l r
theorem rightRule (k l r : Nat) :
    Reach (K .C (oo k l) (o r)) (K .C l (zz k (o r))) := (shifts k).2 l r

end Pilot
