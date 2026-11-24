module

public import BigfootBridge.Arithmetic

/-! # The guarded four-sweep return of ternary Bigfoot

`run` iterates the certified, partial `next`; `credit` is the signed reserve in the total
arithmetic continuation. They agree precisely while all intervening prefix balances are
nonnegative. In particular failure is a statement about a *particular primitive sweep*,
not a converse claiming that one completed block runs forever.
-/

@[expose] public section
namespace Bigfoot

open BusyBeaver
open BusyBeaver.M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA (State next encode target is_valid_acceleration)

/-- Initial reserve plus the successive ordered increments; may become negative. -/
def credit (h x : ℕ) : ℕ → ℤ
  | 0 => h
  | i+1 => credit h x i + delta (stage x i)

/-- Every within-block guard can be read at the representative `x % 81`. -/
theorem credit_row (h x i : ℕ) (hi : i ≤ 4) : credit h x i = credit h (x%81) i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [credit, credit, ih (by omega), stage_delta x i (by omega)]

/-- All `n` balances *after* the corresponding updates, not merely the last one. -/
def Good (h x n : ℕ) : Prop := ∀ j < n, 0 ≤ credit h x (j+1)

/-- A putative primitive checkpoint. Used as an actual state only for a good prefix. -/
def atState (h x i : ℕ) : State := raw (credit h x i).toNat (stage x i)

/-- The physical House checkpoint is the upstream encoding of this state. -/
def entry (h x : ℕ) : State := raw h (2*x, 0)

/-- Exactly `i` successive applications of the published partial sweep map. -/
def run (h x : ℕ) : ℕ → Option State
  | 0 => some (entry h x)
  | i+1 => (run h x i).bind next

private theorem good_succ (h x i : ℕ) :
    Good h x (i+1) ↔ Good h x i ∧ 0 ≤ credit h x (i+1) := by
  constructor
  · intro p
    exact ⟨fun j hj => p j (by omega), p i (by omega)⟩
  · rintro ⟨p, hp⟩ j hj
    by_cases he : j = i
    · simpa only [he] using hp
    · exact p j (by omega)

private theorem current_nonneg {h x i : ℕ} (p : Good h x i) : 0 ≤ credit h x i := by
  cases i with
  | zero => simp [credit]
  | succ i => exact p i (by omega)

private theorem next_at {h x i : ℕ} (p : Good h x i) :
    next (atState h x i) =
      if 0 ≤ credit h x (i+1) then some (atState h x (i+1)) else none := by
  simp only [atState, next_raw, Int.toNat_of_nonneg (current_nonneg p), credit, stage, Function.iterate_succ_apply']

/-- One successful physical sweep, including its exact start and end tape families. -/
theorem stage_reaches {h x i : ℕ} (p : Good h x (i+1)) :
    ReachesPlus target (encode (atState h x i)) (encode (atState h x (i+1))) := by
  obtain ⟨prev, last⟩ := (good_succ h x i).mp p
  exact is_valid_acceleration.step_some _ _ (by rw [next_at prev, ite_eq_left last])

private theorem prefix_spec (h x i : ℕ) :
    (Good h x i → run h x i = some (atState h x i) ∧
      ReachesStar target (encode (entry h x)) (encode (atState h x i))) ∧
    (¬ Good h x i → run h x i = none) := by
  induction i with
  | zero =>
    constructor
    · intro _
      exact ⟨rfl, ReachesStar.refl _ _⟩
    · intro bad
      exact False.elim (bad (fun j hj => by omega))
  | succ i ih =>
    constructor
    · intro p
      obtain ⟨prev, last⟩ := (good_succ h x i).mp p
      obtain ⟨hr, ht⟩ := ih.1 prev
      exact ⟨by rw [run, hr, Option.bind_some, next_at prev, ite_eq_left last],
        ht.trans (stage_reaches p).to_star⟩
    · intro bad
      by_cases prev : Good h x i
      · have last : ¬ 0 ≤ credit h x (i+1) := fun hn => bad ((good_succ h x i).mpr ⟨prev, hn⟩)
        rw [run, (ih.1 prev).1, Option.bind_some, next_at prev, ite_eq_right last]
      · rw [run, ih.2 prev]; rfl

private theorem at_four (h x : ℕ) : atState h x 4 = entry (credit h x 4).toNat (house x) := by
  simp only [atState, entry, stage, ghost_four]

/-- The four partial sweeps return to the affine House endpoint iff every prefix pays its loss. -/
theorem four_sweeps_iff (h x : ℕ) :
    run h x 4 = some (entry (credit h x 4).toNat (house x)) ↔ Good h x 4 := by
  rw [← at_four]
  constructor
  · intro returned
    by_contra bad
    rw [(prefix_spec h x 4).2 bad] at returned
    contradiction
  · intro ok
    exact ((prefix_spec h x 4).1 ok).1

/-- The endpoint in a successful block is reached by strictly positive physical time. -/
theorem four_sweeps_reach {h x : ℕ} (ok : Good h x 4) :
    ReachesPlus target (encode (entry h x)) (encode (entry (credit h x 4).toNat (house x))) := by
  have p := ((prefix_spec h x 3).1 ((good_succ h x 3).mp ok).1).2
  rw [← at_four]
  exact p.trans_plus (stage_reaches (i := 3) ok)

private theorem first_bad {h x n : ℕ} (bad : ¬ Good h x n) :
    ∃ i < n, Good h x i ∧ credit h x (i+1) < 0 := by
  induction n with
  | zero => exact False.elim (bad (fun j hj => by omega))
  | succ n ih =>
    by_cases prev : Good h x n
    · refine ⟨n, by omega, prev, ?_⟩
      have H : ¬ 0 ≤ credit h x (n+1) := fun hn => bad ((good_succ h x n).mpr ⟨prev, hn⟩)
      omega
    · obtain ⟨i, hi, hp, hn⟩ := ih prev
      exact ⟨i, by omega, hp, hn⟩

/-- On failure, `i` is the number of successful sweeps before the first negative balance.
The tape really reaches the start of the failed sweep; its partial rule is `none`, and that
physical configuration reaches a halt. The later signed phases have no physical meaning. -/
theorem four_sweeps_first_underflow {h x : ℕ} (bad : ¬ Good h x 4) :
    run h x 4 = none ∧ ∃ i < 4, Good h x i ∧ credit h x (i+1) < 0 ∧
      run h x i = some (atState h x i) ∧ next (atState h x i) = none ∧
      ReachesStar target (encode (entry h x)) (encode (atState h x i)) ∧
      HaltsFrom target (encode (atState h x i)) := by
  obtain ⟨i, hi, prev, loss⟩ := first_bad bad
  obtain ⟨at_i, tape_i⟩ := (prefix_spec h x i).1 prev
  have stops : next (atState h x i) = none := by rw [next_at prev, ite_eq_right (by omega)]
  exact ⟨(prefix_spec h x 4).2 bad, i, hi, prev, loss, at_i, stops, tape_i,
    is_valid_acceleration.step_none _ stops⟩

/-- No claim about a successful block's later behavior is needed. -/
theorem four_sweeps_halts {h x : ℕ} (bad : ¬ Good h x 4) :
    HaltsFrom target (encode (entry h x)) := by
  obtain ⟨_, i, _, _, _, _, _, seen, halt⟩ := four_sweeps_first_underflow bad
  exact HaltsFrom.of_reachesStar seen halt

/-! ## Reading the published net-change rows without losing the guard -/

private theorem credit_base (h x i : ℕ) : credit h x i = (h:ℤ) + credit 0 x i := by
  induction i with
  | zero => simp [credit]
  | succ i ih => simp only [credit, ih, Int.add_assoc]

private def worstPrefix (r : ℕ) : ℤ := min 0 (min (credit 0 r 1)
  (min (credit 0 r 2) (min (credit 0 r 3) (credit 0 r 4))))
private def exceptional (r : ℕ) : Bool := r == 8 || r == 13 || r == 32 || r == 37

private theorem worstPrefix_rows : ∀ r : Fin 81, worstPrefix r =
    min (if exceptional r then -1 else 0) (credit 0 r 4) := by decide +kernel

/-- Exactly four rows can conceal an intermediate overdraft behind a solvent endpoint. -/
theorem good_four_iff_net {h x : ℕ} : Good h x 4 ↔ 0 ≤ credit h x 4 ∧
    ¬ (h=0 ∧ (x%81=8 ∨ x%81=13 ∨ x%81=32 ∨ x%81=37)) := by
  let r := x%81
  have bal (i : ℕ) (hi : i ≤ 4) : credit h x i = (h:ℤ) + credit 0 r i := by
    rw [credit_row h x i hi, credit_base]
  have guards : Good h x 4 ↔ -(h:ℤ) ≤ worstPrefix r := by
    simp only [worstPrefix, le_min_iff]
    constructor
    · intro ok
      have bound (j : ℕ) (hj : j < 4) : -(h:ℤ) ≤ credit 0 r (j+1) := by
        have v := ok j hj; rw [bal _ (by omega)] at v; omega
      exact ⟨by omega, bound 0 (by decide), bound 1 (by decide), bound 2 (by decide), bound 3 (by decide)⟩
    · rintro ⟨_,h1,h2,h3,h4⟩ j hj
      rw [bal _ (by omega)]
      have : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
      rcases this with e|e|e|e <;> subst j <;> simp only [Nat.reduceAdd] <;> omega
  have z := worstPrefix_rows ⟨r,by dsimp [r]; omega⟩
  change worstPrefix r = min (if exceptional r then -1 else 0) (credit 0 r 4) at z
  rw [guards,z, le_min_iff, bal 4 (by decide)]
  change (_ ≤ (if exceptional r then _ else _) ∧ _) ↔ _
  by_cases E : exceptional r = true
  · have := E; simp [exceptional,r] at this; rw [ite_eq_left E]; omega
  · have := E; simp [exceptional,r] at this; rw [ite_eq_right E]; omega

/-- At size 8 the ghost returns to reserve zero but the third sweep overdrafts. -/
theorem zero_eight :
    (credit 0 8 1, credit 0 8 2, credit 0 8 3, credit 0 8 4) = (0, 0, -1, 0) ∧
    HaltsFrom target (encode (entry 0 8)) := by
  refine ⟨by decide +kernel, four_sweeps_halts ?_⟩
  intro ok
  exact (by decide +kernel : ¬ 0 ≤ credit 0 8 3) (ok 2 (by decide))

end Bigfoot
