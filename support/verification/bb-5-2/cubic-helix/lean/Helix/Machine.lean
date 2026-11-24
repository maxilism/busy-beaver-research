import Std

/-! Exact TM semantics. A stack is the natural whose binary expansion has the
nearest bit at the least significant place. Infinite far-end zeros are implicit. -/
namespace Helix
abbrev Wd := List Bool
inductive St where | A | B | C | D | E deriving DecidableEq, Repr
structure Cfg where
  q : St
  l : Nat
  x : Bool
  r : Nat
  deriving DecidableEq, Repr

def push (b : Bool) (n : Nat) := 2*n + b.toNat
def top (n : Nat) : Bool := decide (n % 2 = 1)
def pop (n : Nat) := n / 2
@[simp] theorem top_push (b : Bool) (n : Nat) : top (push b n) = b := by
  cases b <;> simp [top,push,Bool.toNat] <;> omega
@[simp] theorem pop_push (b : Bool) (n : Nat) : pop (push b n) = n := by
  cases b <;> simp [pop,push,Bool.toNat] <;> omega
@[simp] theorem push_unpack (n : Nat) : push (top n) (pop n) = n := by
  simp [push,top,pop,Bool.toNat]; split <;> rename_i h <;> (try simp_all) <;> omega

inductive Dir where | L | R deriving DecidableEq, Repr
/-- None means immediate halt, with no write or shift. -/
def instruction : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true  => some (false, .R, .C)
  | .B, false => some (true, .L, .C)
  | .B, true  => some (false, .L, .E)
  | .C, false => some (false, .L, .D)
  | .C, true  => some (false, .L, .B)
  | .D, false => some (true, .R, .A)
  | .D, true  => none
  | .E, false => some (true, .L, .B)
  | .E, true  => some (false, .R, .D)

/-- Right marker before r / left marker after l. -/
def F (q : St) (l r : Nat) : Cfg := ⟨q,l,top r,pop r⟩
def K (q : St) (l r : Nat) : Cfg := ⟨q,pop l,top l,r⟩

def step (c : Cfg) : Option Cfg :=
  match instruction c.q c.x with
  | none => none
  | some (w, .R, q) => some (F q (push w c.l) c.r)
  | some (w, .L, q) => some (K q c.l (push w c.r))

def Halted (c : Cfg) := step c = none
def blank : Cfg := ⟨.A,0,false,0⟩
inductive Reach : Cfg → Cfg → Prop where
  | refl (c : Cfg) : Reach c c
  | cons {c d e} : step c = some d → Reach d e → Reach c e
namespace Reach
theorem single {c d} (h : step c = some d) : Reach c d := .cons h (.refl _)
theorem trans {c d e} (h : Reach c d) (g : Reach d e) : Reach c e := by
  induction h with | refl => exact g | cons a _ ih => exact .cons a (ih g)
theorem closed {S : Cfg → Prop} (hclosed : ∀ c d, S c → step c = some d → S d)
    {c d} (p : Reach c d) (h : S c) : S d := by
  induction p with
  | refl => exact h
  | cons a _ ih => exact ih (hclosed _ _ h a)
end Reach

/-- Encode displayed prefix in reading order as a stack, nearest bit last. -/
def left (f : Wd) := f.foldl (fun n b => push b n) 0
abbrev z := push false
abbrev o := push true
/-- Repeated alternating pair put on front of a stack. -/
def zo : Nat → Nat → Nat | 0,r => r | n+1,r => z (o (zo n r))
def oz : Nat → Nat → Nat | 0,r => r | n+1,r => o (z (oz n r))
def ones : Nat → Nat | 0 => 0 | n+1 => o (ones n)

def T (f : Wd) (m : Nat) : Cfg := F .A (o (zo m (left f))) 0
def P (f : Wd) (b c : Nat) : Cfg := F .D (left f) (z (oz b (z (ones c))))
def Q (f : Wd) (b c : Nat) : Cfg := F .D (left f) (z (z (oz b (ones c))))
end Helix
