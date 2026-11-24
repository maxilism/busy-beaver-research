import Helix.Machine

/-! Canonical finite display of the two stacks, preserved scanned bit, and
    word representation used for the finite-state argument. -/
namespace Helix
inductive Sym where
  | bit (v : Bool)
  | mark (q : St)
  deriving DecidableEq, Repr

def cells (n : Nat) : Wd :=
  if _h : n = 0 then [] else top n :: cells (pop n)
termination_by n
decreasing_by unfold pop; omega

@[simp] theorem cells0 : cells 0 = [] := by rw [cells]; simp

private theorem push_pos (a : Nat) (b : Bool) (h : a ≠ 0 ∨ b = true) : push b a ≠ 0 := by
  cases b <;> simp_all [push,Bool.toNat] <;> omega
private theorem cellsPush (a : Nat) (b : Bool) (h : a ≠ 0 ∨ b = true) : cells (push b a) = b :: cells a := by
  rw [cells]; simp [push_pos a b h]
private theorem cellsFold (f : Wd) (a : Nat) (h : a ≠ 0) :
    cells (f.foldl (fun n b => push b n) a) = f.reverse ++ cells a := by
  induction f generalizing a with
  | nil => rfl
  | cons b f ih =>
    simp only [List.foldl_cons, List.reverse_cons, List.append_assoc]
    rw [ih _ (push_pos _ _ (Or.inl h)), cellsPush _ _ (Or.inl h)]
    rfl

theorem cellsLeft (f : Wd) : (cells (left (true::f))).reverse = true::f := by
  simp only [left,List.foldl_cons]; rw [cellsFold _ _ (by decide)]
  simp [cellsPush 0 true (Or.inr rfl)]
@[simp] theorem cellsOnes (n : Nat) : cells (ones n) = List.replicate n true := by
  induction n with
  | zero => exact cells0
  | succ n ih =>
    simp only [ones, List.replicate_succ]; rw [cellsPush _ true (Or.inr rfl), ih]

/-- Stack display loses neither interior zeros nor any nonblank cells. -/
theorem cellsValue (n : Nat) : (cells n).foldr push 0 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n=0
    · subst n; simp
    · conv => lhs; arg 3; rw [cells, dite_eq_right hn]
      simp only [List.foldr_cons]; rw [ih (pop n) (by unfold pop; omega), push_unpack]

/-- Both sides extend only to their outermost one. Always write the head bit,
even a scanned zero; put one state marker before it. -/
def display (c : Cfg) : List Sym :=
  (cells c.l).reverse.map Sym.bit ++ [Sym.mark c.q,Sym.bit c.x] ++ (cells c.r).map Sym.bit

theorem displayQ0 (f : Wd) (c : Nat) :
    display (Q (true::f) 0 (c+1)) = (true::f).map Sym.bit ++
    [Sym.mark .D, Sym.bit false, Sym.bit false] ++ (List.replicate (c+1) (Sym.bit true)) := by
  simp only [display,Q,F,top_push,pop_push,cellsLeft,oz]
  rw [cellsPush (ones (c+1)) false (Or.inl (push_pos _ true (Or.inr rfl))), cellsOnes]
  simp [List.append_assoc]
end Helix
