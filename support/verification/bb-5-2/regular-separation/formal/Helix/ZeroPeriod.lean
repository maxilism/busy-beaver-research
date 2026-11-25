import Std

/-! A common eventual period of the powers of one finite-state transition.
We enumerate finite output vectors, not the infinitely many lengths fed to the DFA. -/
namespace Helix

def iter (f : α → α) : Nat → α → α
  | 0, q => q
  | j+1, q => f (iter f j q)

private theorem repetition {α : Type} (L : List α) (g : Nat → α)
    (mem : ∀ i, g i ∈ L) : ∃ i j, i < j ∧ g i = g j := by
  classical
  induction L generalizing g with
  | nil => simpa using mem 0
  | cons a L ih =>
    by_cases once : ∃ i, g i = a
    · obtain ⟨k,hk⟩ := once
      by_cases later : ∃ j, k < j ∧ g j = a
      · obtain ⟨j,hj,he⟩ := later
        exact ⟨k,j,hj,hk.trans he.symm⟩
      · have tail (i : Nat) : g (k+1+i) ∈ L := by
          rcases List.mem_cons.mp (mem (k+1+i)) with h|h
          · exact False.elim (later ⟨_,by omega,h⟩)
          · exact h
        obtain ⟨i,j,hij,he⟩ := ih (fun i => g (k+1+i)) tail
        exact ⟨k+1+i,k+1+j,by omega,he⟩
    · exact ih g (fun i => (List.mem_cons.mp (mem i)).resolve_left (fun h => once ⟨i,h⟩))

private def words (n : Nat) : Nat → List (List (Fin n))
  | 0 => [[]]
  | j+1 => (List.finRange n).flatMap fun a => (words n j).map (a :: ·)

private theorem mem_words (n : Nat) (w : List (Fin n)) : w ∈ words n w.length := by
  induction w with
  | nil => simp [words]
  | cons a l ih =>
    exact List.mem_flatMap.mpr ⟨a,List.mem_finRange a,List.mem_map.mpr ⟨l,ih,rfl⟩⟩

private theorem iter_extend {α} (f : α → α) {a b : Nat}
    (h : ∀ q, iter f a q = iter f b q) (k : Nat) : ∀ q, iter f (a+k) q = iter f (b+k) q := by
  induction k with
  | zero => exact h
  | succ k ih => intro q; exact congrArg f (ih q)

/-- A common period ≥6 divisible by 3, after a uniform threshold. -/
theorem zero_period {n : Nat} (f : Fin n → Fin n) : ∃ N t : Nat,
    ∀ j, N ≤ j → ∀ q : Fin n, iter f (j+(3*t+6)) q = iter f j q := by
  let g := fun i => List.ofFn (iter f i)
  have hm (i : Nat) : g i ∈ words n n := by
    have h := mem_words n (g i)
    simpa [g,List.length_ofFn] using h
  obtain ⟨a,b,lt,h⟩ := repetition _ g hm
  have base (q : Fin n) : iter f b q = iter f a q := by
    have eq := congrArg (fun l : List (Fin n) => l[q.val]?) h
    simpa [g, List.getElem?_ofFn, q.isLt] using eq.symm
  let p := b-a
  have period (j : Nat) (hj : a ≤ j) (q : Fin n) : iter f (j+p) q = iter f j q := by
    have h := iter_extend f base (j-a) q
    rwa [show b+(j-a)=j+p by dsimp[p];omega, show a+(j-a)=j by omega] at h
  have mult (m j : Nat) (hj : a ≤ j) (q : Fin n) : iter f (j+m*p) q = iter f j q := by
    induction m with
    | zero => simp
    | succ k ih => simpa only [Nat.succ_mul, ←Nat.add_assoc] using
        (period (j+k*p) (by omega) q).trans ih
  refine ⟨a,2*p-2,?_⟩
  intro j hj q
  have h := mult 6 j hj q
  rwa [show 6*p=3*(2*p-2)+6 by dsimp[p]; omega] at h
end Helix
