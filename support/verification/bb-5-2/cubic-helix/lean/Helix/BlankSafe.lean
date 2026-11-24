import Helix.Paths

/-! Blank nonhalting is also available inside the same literal semantics;
it is not a hypothesis about the exterior of the formal machine. -/
namespace Helix

/-- On a deterministic halting run every reachable left stack is bounded.
This finite-prefix argument requires no time complexity formula. -/
private theorem bounded_before_halt {c t : Cfg} (p : Reach c t) (ht : Halted t) :
    ∃ B : Nat, ∀ x, Reach c x → x.l ≤ B := by
  induction p with
  | refl t =>
    refine ⟨t.l,?_⟩
    intro x hx; cases hx with
    | refl => exact Nat.le_refl _
    | cons h _ => rw [show step t = none from ht] at h; contradiction
  | @cons c d e h _ ih =>
    obtain ⟨B,hB⟩ := ih ht
    refine ⟨max c.l B,?_⟩
    intro x hx; cases hx with
    | refl => exact Nat.le_max_left _ _
    | cons g w => rw [h] at g; injection g with he; subst he; exact Nat.le_trans (hB x w) (Nat.le_max_right _ _)

private theorem alt_lower (m : Nat) : m ≤ zo m 0 := by
  induction m with
  | zero => exact Nat.zero_le _
  | succ k ih => simp [zo,z,o,push] at *; omega

/-- The sequence of right edges is unbounded, so a halt is unreachable from blank. -/
theorem blank_safe {t : Cfg} (h : Reach blank t) : ¬ Halted t := by
  intro ht
  obtain ⟨B,hB⟩ := bounded_before_halt h ht
  have v := hB _ (Obstruction.rightEdges B)
  change o (zo (3*B+2) 0) ≤ B at v
  have u := alt_lower (3*B+2)
  simp [o,push] at v; omega
/-- Safety can also be propagated backward along a known finite deterministic path. -/
theorem safe_of_reaches_safe {c d : Cfg} (p : Reach c d)
    (h : ∀ t, Reach d t → ¬ Halted t) : ∀ t, Reach c t → ¬ Halted t := by
  induction p with
  | refl => exact h
  | @cons c e d hs _ ih =>
    intro t w; cases w with
    | refl => intro bad; rw [show step c = none from bad] at hs; contradiction
    | cons ht w => rw [hs] at ht; injection ht with he; subst he; exact ih h _ w
end Helix
