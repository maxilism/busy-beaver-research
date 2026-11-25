import Std

/-! The abstract D-checkpoints of the counter-balanced machines.
A list of tiles on the right is followed by a one, then blank exterior.
The checked literal table calculations are linked in BalancedCases. -/

namespace Balanced

inductive Tile where
  | Z | U | T
deriving DecidableEq, Repr

inductive Cell where
  | live (depth : Nat) (right : List Tile)
  | halt
deriving DecidableEq, Repr

def Lead : List Tile → Prop
  | .Z :: _ => False
  | _ => True

/-- The four literal rewrites. Underflow is the zero-depth branch of pop,
and margin instantiates shift on the terminal one and exterior zeros. -/
inductive Step : Cell → Cell → Prop where
  | push (d s) :
      Step (.live d (.Z :: .Z :: s)) (.live (d+1) (.T :: s))
  | fill (d s) (h : Lead s) :
      Step (.live d (.Z :: s)) (.live d (.U :: s))
  | shift (d j s) :
      Step (.live d (List.replicate j .U ++ .T :: .Z :: s))
           (.live d (List.replicate (j+1) .Z ++ .T :: s))
  | pop (d j s) (h : Lead s) :
      Step (.live (d+1) (List.replicate j .U ++ .T :: s))
           (.live d (List.replicate (j+2) .U ++ s))
  | underflow (j s) (h : Lead s) :
      Step (.live 0 (List.replicate j .U ++ .T :: s)) .halt
  | margin (d j) :
      Step (.live d (List.replicate j .U)) (.live d (List.replicate (j+1) .Z))

inductive Reach : Cell → Cell → Prop where
  | refl (c) : Reach c c
  | cons {a b c} : Step a b → Reach b c → Reach a c

theorem Reach.single {a b} (s : Step a b) : Reach a b := .cons s (.refl b)

theorem Reach.trans {a b c} (h : Reach a b) (g : Reach b c) : Reach a c := by
  induction h with
  | refl => exact g
  | cons step _ ih => exact .cons step (ih g)

theorem Reach.inductAlong (R : Cell → Prop)
    (hstep : ∀ {u v}, Step u v → R u → R v) {a b} (h : Reach a b) : R a → R b := by
  induction h with
  | refl => exact id
  | cons s _ ih => exact fun r => ih (hstep s r)

theorem rep_snoc {α} (x : α) (n : Nat) (s : List α) :
    List.replicate (n+1) x ++ s = List.replicate n x ++ x :: s := by
  induction n with
  | zero => rfl
  | succ n h => exact congrArg (List.cons x) h

/-- Move the T across k zero tiles one at a time. Each crossing invokes
a strictly smaller conversion than the enclosing one. -/
theorem slide (d n i k : Nat) (s : List Tile)
    (bound : i+k ≤ n)
    (smaller : ∀ j ≤ n, ∀ t : List Tile, Lead t →
      Reach (.live d (List.replicate j .Z ++ t))
            (.live d (List.replicate j .U ++ t))) :
    Reach (.live d (List.replicate i .U ++ .T :: (List.replicate k .Z ++ s)))
          (.live d (List.replicate (i+k) .U ++ .T :: s)) := by
  induction k generalizing i with
  | zero => exact .refl _
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    apply Reach.cons (Step.shift d i (List.replicate k Tile.Z ++ s))
    apply Reach.trans (smaller (i+1) (by omega) (Tile.T :: (List.replicate k Tile.Z ++ s)) trivial)
    have h := ih (i+1) (by omega)
    simpa only [show i+1+k = i+(k+1) by omega] using h

theorem convert (n d : Nat) (s : List Tile) (ok : Lead s) :
    Reach (.live d (List.replicate n .Z ++ s))
          (.live d (List.replicate n .U ++ s)) := by
  induction n using Nat.strongRecOn generalizing d s with
  | ind n ih =>
    match n with
    | 0 => exact .refl _
    | 1 => exact .single (.fill d s ok)
    | k+2 =>
      rw [List.replicate_succ, List.replicate_succ (n := k), List.cons_append, List.cons_append]
      apply Reach.cons (Step.push d (List.replicate k Tile.Z ++ s))
      have hslide := slide (d+1) k 0 k s (by omega)
        (fun j le t ht => ih j (by omega) (d+1) t ht)
      apply Reach.trans (by simpa only [Nat.zero_add, List.replicate_zero, List.nil_append] using hslide)
      exact .single (.pop d k s ok)

/-- Inside the conversion at n=2k, one of its nested calls reaches depth d+k. -/
theorem nested (d k : Nat) (s : List Tile) :
    Reach (.live d (List.replicate (2*k) .Z ++ s))
          (.live (d+k) (List.replicate k .T ++ s)) := by
  induction k generalizing d s with
  | zero => exact .refl _
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      exact .single (.push d s)
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      let m := 2*u+1
      have ar : 2*(u+1+1) = (m+1)+2 := by dsimp [m]; omega
      rw [ar]
      rw [List.replicate_succ, List.replicate_succ (n := m+1), List.cons_append, List.cons_append]
      apply Reach.cons (Step.push d (List.replicate (m+1) Tile.Z ++ s))
      rw [rep_snoc Tile.Z m s]
      have hslide := slide (d+1) m 0 m (.Z :: s) (by omega)
        (fun j _ t ht => convert j (d+1) t ht)
      apply Reach.trans (by simpa only [Nat.zero_add, List.replicate_zero, List.nil_append] using hslide)
      apply Reach.cons (Step.shift (d+1) m s)
      have sub := ih (d+1) (.T :: s)
      have ar' : m+1 = 2*(u+1) := by dsimp [m]; omega
      rw [ar', rep_snoc Tile.T (u+1) s]
      simpa only [show d+1+(u+1) = d+(u+1+1) by omega] using sub

theorem roundStart (e n : Nat) :
    Reach (.live e []) (.live e (List.replicate n .Z)) := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    apply Reach.trans ih
    have cv := convert n e [] trivial
    simp only [List.append_nil] at cv
    exact cv.trans (.single (.margin e n))

theorem diagonal (e k : Nat) :
    Reach (.live e []) (.live (e+k) (List.replicate k .T)) := by
  apply Reach.trans (roundStart e (2*k))
  simpa only [List.append_nil] using nested e k []

theorem manyPops (a b j : Nat) (lt : a < b) :
    Reach (.live a (List.replicate j .U ++ List.replicate b .T)) .halt := by
  induction a generalizing b j with
  | zero =>
    cases b with
    | zero => omega
    | succ b =>
      apply Reach.single (Step.underflow j (List.replicate b .T) ?_)
      cases b <;> trivial
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      have ok : Lead (List.replicate b .T) := by cases b <;> trivial
      exact Reach.cons (Step.pop a j (List.replicate b .T) ok) (ih b (j+2) (by omega))

theorem fatal (a b : Nat) (h : a < b) :
    Reach (.live a (List.replicate b .T)) .halt :=
  manyPops a b 0 h

end Balanced
