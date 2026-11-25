import Std

/-! Primitive, translation-invariant binary-tape semantics for the six counter-balanced
transition tables. Each tape half is a natural number, nearest bit least significant;
exterior zeros cost no space. -/
namespace BalancedTM

inductive St where | A | B | C | D | E deriving DecidableEq, Repr
inductive Dir where | L | R deriving DecidableEq, Repr
inductive Variant where
  | m8210683 | m8210684 | m8210685 | m8226493 | m10818491 | m10818510
  deriving DecidableEq, Repr
open St

abbrev Action := Option (Bool × Dir × St)
def instruction (v : Variant) : St → Bool → Action
  | A, false => some (true,.R,B)
  | A, true => some (true,.R,if v = .m10818491 ∨ v = .m10818510 then E else A)
  | B, false => some (true,.L,C)
  | B, true => some (true,.L,if v = .m8226493 then E else B)
  | C, false => some (false,.R,D)
  | C, true => some (false,.L,C)
  | D, false => some (true,if v = .m10818510 then .L else .R,E)
  | D, true => none
  | E, false => some (false,.R,A)
  | E, true => match v with
    | .m8210684 => some (true,.L,A)
    | .m8210685 => some (true,.L,E)
    | .m8226493 => some (true,.L,B)
    | _ => some (true,.R,A)

def push (b : Bool) (n : Nat) := 2*n + b.toNat
abbrev z := push false
abbrev o := push true
def top (n : Nat) := decide (n % 2 = 1)
def pop (n : Nat) := n / 2
@[simp] theorem top_push (b : Bool) (n : Nat) : top (push b n) = b := by
  cases b <;> simp [top,push,Bool.toNat] <;> omega
@[simp] theorem pop_push (b : Bool) (n : Nat) : pop (push b n) = n := by
  cases b <;> simp [pop,push,Bool.toNat] <;> omega
@[simp] theorem push_parts (n : Nat) : push (top n) (pop n) = n := by
  simp [push,top,pop,Bool.toNat]; split <;> omega
@[simp] theorem top_zero : top 0 = false := rfl
@[simp] theorem pop_zero : pop 0 = 0 := rfl
@[simp] theorem z_zero : z 0 = 0 := rfl

structure Cfg where
  q : St
  l : Nat
  r : Nat
  deriving DecidableEq, Repr

/-- The scanned bit is at the top of the right stack. -/
abbrev F (q : St) (l r : Nat) : Cfg := ⟨q,l,r⟩
/-- Same tape boundary, with the head instead scanning the nearest left bit. -/
def K (q : St) (l r : Nat) : Cfg := F q (pop l) (push (top l) r)
@[simp] theorem kpush (q : St) (b : Bool) (l r : Nat) :
    K q (push b l) r = F q l (push b r) := by simp [K]

def machineStep (tm : St → Bool → Action) (c : Cfg) : Option Cfg := do
  let (w,dir,q) ← tm c.q (top c.r)
  match dir with
  | .R => return F q (push w c.l) (pop c.r)
  | .L => return K q c.l (push w (pop c.r))

abbrev step (v : Variant) := machineStep (instruction v)

inductive Walk (s : Cfg → Option Cfg) : Cfg → Cfg → Prop where
  | nil (c : Cfg) : Walk s c c
  | tick {a b c} : s a = some b → Walk s b c → Walk s a c

abbrev Path (v : Variant) := Walk (step v)
theorem Walk.trans {s : Cfg → Option Cfg} {a b c : Cfg}
    (p : Walk s a b) (q : Walk s b c) : Walk s a c := by
  induction p with
  | nil => exact q
  | tick h _ ih => exact .tick h (ih q)

def bits (b : Bool) : Nat → Nat → Nat
  | 0, t => t
  | n+1, t => push b (bits b n t)

@[simp] theorem bits_zero (b : Bool) (t : Nat) : bits b 0 t = t := rfl
@[simp] theorem bits_succ (b : Bool) (n t : Nat) :
    bits b (n+1) t = push b (bits b n t) := rfl
theorem bits_push (b : Bool) (n t : Nat) :
    bits b n (push b t) = push b (bits b n t) := by
  induction n <;> simp_all
theorem bits_join (b : Bool) (m n t : Nat) :
    bits b m (bits b n t) = bits b (m+n) t := by
  induction m with
  | zero => simp
  | succ m ih => simpa [Nat.succ_add] using congrArg (push b) ih

/-- Left of the D marker lies (10)^d in reading order. -/
def bank : Nat → Nat
  | 0 => 0
  | d+1 => z (o (bank d))
def cp (d s : Nat) := F D (bank d) (z s)
def blank (q : St) := F q 0 0
def Fatal (v : Variant) (c : Cfg) := ∃ h, Path v c h ∧ step v h = none


private def run (v : Variant) : Nat → Cfg → Option Cfg
  | 0,c => some c
  | n+1,c => (step v c).bind (run v n)

private theorem run_path (v : Variant) (n : Nat) {a b : Cfg}
    (h : run v n a = some b) : Path v a b := by
  induction n generalizing a with
  | zero =>
    simp [run] at h
    subst b
    exact .nil _
  | succ n ih =>
    cases hs : step v a with
    | none => simp [run,hs] at h
    | some a' => exact .tick hs (ih (by simpa [run,hs] using h))

private theorem prologue (v : Variant) (l r : Nat) (b : Bool) :
    Path v (F D (z l) (z (push b r))) (F A (push b (o (z l))) r) := by
  cases v <;> cases b <;> first
    | apply run_path _ 2; rfl
    | apply run_path _ 2; simp [run,machineStep,instruction,K]; done
    | apply run_path _ 4; simp [run,machineStep,instruction,K]; done
    | apply run_path _ 6; simp [run,machineStep,instruction,K]; done


/-- The scan starting at A crosses two ones even in the tables where its
intermediate state is E. The leftward B scan has the same parity property. -/
private theorem aPair (v : Variant) (l r : Nat) :
    Path v (F A l (o (o r))) (F A (o (o l)) r) := by
  cases v <;> apply run_path _ 2 <;> simp [run,machineStep,instruction,K]

private theorem bPair (v : Variant) (l r : Nat) :
    Path v (K B (o (o l)) r) (K B l (o (o r))) := by
  cases v <;> apply run_path _ 2 <;> simp [run,machineStep,instruction,K]

private theorem cOne (v : Variant) (l r : Nat) :
    Path v (K C (o l) r) (K C l (z r)) := by
  apply run_path _ 1
  simp [run,machineStep,instruction,K]

private theorem aSweep (v : Variant) (j l r : Nat) :
    Path v (F A l (bits true (2*j) r)) (F A (bits true (2*j) l) r) := by
  induction j generalizing l with
  | zero => exact .nil _
  | succ j ih =>
    rw [show 2*(j+1)=2*j+2 by omega]
    simp only [bits_succ]
    exact (aPair v _ _).trans (by simpa only [bits_push] using ih (o (o l)))

private theorem bSweep (v : Variant) (j l r : Nat) :
    Path v (K B (bits true (2*j) l) r) (K B l (bits true (2*j) r)) := by
  induction j generalizing r with
  | zero => exact .nil _
  | succ j ih =>
    rw [show 2*(j+1)=2*j+2 by omega]
    simp only [bits_succ]
    exact (bPair v _ _).trans (by simpa only [bits_push] using ih (o (o r)))

private theorem cSweep (v : Variant) (j l r : Nat) :
    Path v (K C (bits true j l) r) (K C l (bits false j r)) := by
  induction j generalizing r with
  | zero => exact .nil _
  | succ j ih =>
    exact (cOne v _ _).trans (by simpa only [bits_succ,bits_push] using ih (z r))

private theorem bank_zero_first (d : Nat) : z (pop (bank d)) = bank d := by
  cases d <;> simp [bank]

private theorem startSweep (v : Variant) (d r : Nat) (b : Bool) :
    Path v (cp d (push b r)) (F A (push b (o (bank d))) r) := by
  simpa only [bank_zero_first,cp] using prologue v (pop (bank d)) r b

theorem rowPush (v : Variant) (d s : Nat) :
    Path v (cp d (z (z (z (z s))))) (cp (d+1) (o (z s))) := by
  apply (startSweep v d _ false).trans
  apply run_path _ 4
  simp [run,machineStep,instruction,K,cp,bank]

theorem rowFill (v : Variant) (d s : Nat) :
    Path v (cp d (z (z (o s)))) (cp d (o (o (o s)))) := by
  apply (startSweep v d _ false).trans
  cases v <;> apply run_path _ 6 <;> cases d <;> simp [run,machineStep,instruction,K,cp,bank]


theorem rowShift (v : Variant) (d j s : Nat) :
    Path v (cp d (bits true (2*j+1) (z (z s))))
      (cp d (bits false (2*j+2) (o s))) := by
  apply (startSweep v d _ true).trans
  apply (aSweep v j _ _).trans
  have cross : Path v (F A (bits true (2*j) (o (o (bank d)))) (z (z s)))
      (K C (bits true (2*j+3) (bank d)) (o s)) := by
    apply run_path _ 2
    simp [run,machineStep,instruction,K,bits_push]
  apply cross.trans
  apply (cSweep v (2*j+3) _ _).trans
  cases d <;> apply run_path _ 1 <;> simp [run,machineStep,instruction,K,cp,bank]

private theorem popPrefix (v : Variant) (d j s : Nat) :
    Path v (cp d (bits true (2*j+1) (z (o s))))
      (K B (bank d) (bits true (2*j+4) s)) := by
  apply (startSweep v d _ true).trans
  apply (aSweep v j _ _).trans
  have cross : Path v (F A (bits true (2*j) (o (o (bank d)))) (z (o s)))
      (K B (bits true (2*j+4) (bank d)) s) := by
    apply run_path _ 1
    simp [run,machineStep,instruction,K,bits_push]
  apply cross.trans
  simpa only [show 2*(j+2)=2*j+4 by omega] using bSweep v (j+2) (bank d) s

theorem rowPop (v : Variant) (d j s : Nat) :
    Path v (cp (d+1) (bits true (2*j+1) (z (o s)))) (cp d (bits true (2*j+5) s)) := by
  apply (popPrefix v (d+1) j s).trans
  cases d <;> apply run_path _ 3 <;> simp [run,machineStep,instruction,K,cp,bank]

theorem rowHalt (v : Variant) (j s : Nat) :
    Fatal v (cp 0 (bits true (2*j+1) (z (o s)))) := by
  refine ⟨F D 0 (o (bits true (2*j+4) s)), (popPrefix v 0 j s).trans ?_, ?_⟩
  · apply run_path _ 2
    simp [run,machineStep,instruction,K,bank]
  · simp [machineStep,instruction]

theorem blankA (v : Variant) : Path v (blank A) (cp 0 (o 0)) := by
  apply run_path _ 4
  simp [run,machineStep,instruction,blank,K,cp,bank]

theorem blankD (v : Variant) : Path v (blank D) (cp 1 (o 0)) := by
  simpa [blank,cp,bank] using rowPush v 0 0

end BalancedTM
