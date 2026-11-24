module

public import BusyBeaver.BB33.M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA

/-! # A guarded sweep of the ternary Bigfoot machine

In the accelerated state `.A h b c` of the pinned DeepMind formalization,
Ligocki's two run counts are `b + 1` and `c + 2`. Thus the House section
`A(h, 2*x + 1, 2)` is `raw h (2*x, 0)`. The geometry may be continued
numerically after an underflow; `next_raw` is where the physical guard enters.
-/

@[expose] public section
namespace Bigfoot
open BusyBeaver BusyBeaver.M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA

/-- Shifted run lengths `(b,c)` as stored by the DeepMind acceleration. -/
abbrev Shape := ℕ × ℕ

/-- Next shape on the numerical continuation, including the hypothetical loss row. -/
def ghost (s : Shape) : Shape :=
  let q := s.1 / 6
  let r := s.1 % 6
  if r = 0 then (8*q + s.2, 1)
  else if r = 1 then (8*q + s.2 + 4, 0)
  else if r = 2 then (8*q + s.2 + 2, 3)
  else if r = 3 then (8*q + s.2 + 4, 0)
  else if r = 4 then (8*q + s.2 + 6, 1)
  else (8*q + s.2 + 8, 0)

/-- Signed reserve change of one sweep, indexed by the shifted first run length. -/
def delta (s : Shape) : ℤ :=
  if s.1 % 6 = 0 then 1
  else if s.1 % 6 = 1 then -1
  else if s.1 % 6 = 3 then 1
  else 0

/-- The upstream accelerated state, not an independent tape model. -/
def raw (h : ℕ) (s : Shape) : State := .A h s.1 s.2

/-- The literal House tape `(12)^h (11)^(2*x+1) <A (11)^2`. The left half
of `headLeft` is stored nearest the head first, hence its pair is `[2,1]`. -/
theorem encode_house (h x : ℕ) : encode (raw h (2*x, 0)) =
    Cfg.headLeft ThreeState.A
      ((default <+ ([2,1] : List (Fin 3)) ^ h) <+ ([1,1] : List (Fin 3)) ^ (2*x+1))
      (([1,1] : List (Fin 3)) ^ (2 : ℕ) +> default) := by
  simp only [raw, encode, pair_pow_eq_singleton_pow_two_mul,
    show 2 * (2*x+1) = 2*(2*x)+2 by omega]

/-- Each of the six accelerated rows is exactly the signed update when legal. -/
theorem next_raw (h : ℕ) (s : Shape) :
    next (raw h s) = if 0 ≤ (h : ℤ) + delta s then
      some (raw (((h : ℤ) + delta s).toNat) (ghost s)) else none := by
  rcases s with ⟨b,c⟩
  have hb : b % 6 = 0 ∨ b % 6 = 1 ∨ b % 6 = 2 ∨ b % 6 = 3 ∨ b % 6 = 4 ∨ b % 6 = 5 := by omega
  rcases hb with r|r|r|r|r|r <;> cases h <;>
    simp [raw, next, delta, ghost, r] <;> omega

/-- The very next successful sweep reaches the specified physical tape in positive time. -/
theorem sweep_reaches (h : ℕ) (s : Shape) (guard : 0 ≤ (h : ℤ) + delta s) :
    ReachesPlus target (encode (raw h s))
      (encode (raw (((h : ℤ) + delta s).toNat) (ghost s))) :=
  is_valid_acceleration.step_some _ _ (by simp only [next_raw, guard, ↓reduceIte])

/-- An attempted loss from zero halts from this physical checkpoint. -/
theorem sweep_underflow (h : ℕ) (s : Shape) (bad : (h : ℤ) + delta s < 0) :
    HaltsFrom target (encode (raw h s)) :=
  is_valid_acceleration.step_none _ (by simp only [next_raw, not_le.mpr bad, ↓reduceIte])

end Bigfoot
