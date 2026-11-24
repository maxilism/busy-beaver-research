module

public import BigfootBridge.HouseSweep
public import Mathlib.Logic.Function.Iterate

/-!
# House's four-sweep section in the shifted tape coordinates

`stage x i` is the reserve-free shape, not the assertion that sweep `i`
was reached.  House's paper residue is the *unshifted* left run length mod 6.
The 81 rows are computed by four calls to `ghost`, not assumed as a table.
Compare Morris, `Collatz/Bigfoot/Clock.lean`, `Dyn.step4_block` and
`Dyn.step4_legion` (commit `9bdf3ca4213ed3faf09bd0124ecf23e184d97c21`).
-/

@[expose] public section
namespace Bigfoot

/-- Ghost shape after `i` sweeps from House size `x`. -/
def stage (x i : ℕ) : Shape := ghost^[i] (2*x,0)

private theorem stage_succ (x i : ℕ) : stage x (i+1) = ghost (stage x i) :=
  Function.iterate_succ_apply' ghost i _

/-- Ligocki's left run length is one more than the stored one. -/
def paperLabel (s : Shape) : ℕ := (s.1+1)%6

/-- In residue order 0,...,5 the changes are `0,+1,-1,0,+1,0`. -/
def paperDelta (r : ℕ) : ℤ :=
  if r = 1 then 1 else if r = 2 then -1 else if r = 4 then 1 else 0

private theorem cases_six (b : ℕ) : b%6=0 ∨ b%6=1 ∨ b%6=2 ∨ b%6=3 ∨ b%6=4 ∨ b%6=5 := by omega

theorem delta_paperLabel (s : Shape) : delta s = paperDelta (paperLabel s) := by
  rcases s with ⟨b,c⟩
  have hadd : (b+1)%6 = (b%6+1)%6 := by omega
  rcases cases_six b with h|h|h|h|h|h <;> simp [delta,paperLabel,paperDelta,hadd,h]

private def bump (a : ℕ) (s : Shape) : Shape := (s.1+a,s.2)

private theorem ghost_bump (s : Shape) (k : ℕ) : ghost (bump (6*k) s) = bump (8*k) (ghost s) := by
  rcases s with ⟨b,c⟩
  have hr : (b+6*k)%6 = b%6 := by omega
  have hq : (b+6*k)/6 = b/6+k := by omega
  rcases cases_six b with h|h|h|h|h|h <;> simp [ghost,bump,hr,hq,h] <;> omega

/-- Shifts of the stored left run at the five boundaries for `x ↦ x+81`. -/
private def stride : ℕ → ℕ | 0 => 162 | 1 => 216 | 2 => 288 | 3 => 384 | _ => 512
private def units : ℕ → ℕ | 0 => 27 | 1 => 36 | 2 => 48 | _ => 64
private theorem stride_step (i : ℕ) (hi : i < 4) :
    stride i = 6 * units i ∧ stride (i+1) = 8 * units i := by
  have : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases this with h|h|h|h <;> subst i <;> decide

private theorem stage_shift (r k i : ℕ) (hi : i ≤ 4) :
    stage (r+81*k) i = bump (stride i*k) (stage r i) := by
  induction i with
  | zero =>
    change (2*(r+81*k),0) = (2*r+162*k,0)
    congr 1; omega
  | succ i ih =>
    obtain ⟨h1,h2⟩ := stride_step i (by omega)
    simp only [stage_succ, ih (by omega), h1,h2,Nat.mul_assoc,ghost_bump]

private theorem stage_mod (x i : ℕ) (hi : i ≤ 4) :
    stage x i = bump (stride i*(x/81)) (stage (x%81) i) := by
  simpa only [Nat.mod_add_div] using stage_shift (x%81) (x/81) i hi

/-- All four residue labels, in their original order, depend only on `x % 81`. -/
theorem stage_label (x i : ℕ) (hi : i < 4) :
    paperLabel (stage x i) = paperLabel (stage (x%81) i) := by
  rw [stage_mod x i (by omega)]
  simp only [paperLabel,bump,(stride_step i hi).1,Nat.mul_assoc]
  omega

theorem stage_delta (x i : ℕ) (hi : i < 4) :
    delta (stage x i) = delta (stage (x%81) i) := by
  rw [delta_paperLabel, stage_label x i hi, ← delta_paperLabel]

/-- The House row output at a residue (only `r < 81` is needed). -/
def row (r : ℕ) : ℕ := (stage r 4).1 / 2

/-- House's next size: use the finite row and the exact drift over an input period. -/
def house (x : ℕ) : ℕ := 256*(x/81)+row (x%81)

private theorem row_endpoints : ∀ r : Fin 81,
    (stage r 4).2 = 0 ∧ (stage r 4).1 % 4 = 0 := by decide +kernel

/-- The unguarded four-step endpoint is again on the House section; its
realization on the actual tape requires the prefix guards. -/
theorem ghost_four (x : ℕ) : ghost^[4] (2*x,0) = (2*house x,0) := by
  change stage x 4 = _
  rw [stage_mod x 4 (by decide)]
  obtain ⟨hc,hb⟩ := row_endpoints ⟨x%81, by omega⟩
  dsimp only [Fin.val_mk] at hc hb
  apply Prod.ext
  · simp only [bump,stride,house,row]
    omega
  · exact hc

/-- The first two paper residues are odd and the last two are even. -/
theorem ordered_phase (x : ℕ) :
    (paperLabel (stage x 0)%2, paperLabel (stage x 1)%2,
     paperLabel (stage x 2)%2, paperLabel (stage x 3)%2) = (1,1,0,0) := by
  have checked : ∀ r : Fin 81,
      (paperLabel (stage r 0)%2, paperLabel (stage r 1)%2,
       paperLabel (stage r 2)%2, paperLabel (stage r 3)%2) = (1,1,0,0) := by decide +kernel
  rw [stage_label x 0 (by decide),stage_label x 1 (by decide),
    stage_label x 2 (by decide),stage_label x 3 (by decide)]
  exact checked ⟨x%81,by omega⟩

/-- Every return size is even (whether or not the reserve would permit it). -/
theorem house_even (x : ℕ) : house x % 2 = 0 := by
  obtain ⟨_,h⟩ := row_endpoints ⟨x%81, by omega⟩
  dsimp only [Fin.val_mk] at h
  simp only [house,row]
  omega

/-- House's refined coordinate `x=2y`, with the same affine drift `256` per
81 input units.  This computes representative rows instead of copying a table. -/
theorem house_refined (y : ℕ) :
    house (2*y) = 2*(256*(y/81) + house (2*(y%81))/2) := by
  have e := house_even (2*(y%81))
  have q : (2*y)/81 = 2*(y/81) + (2*(y%81))/81 := by omega
  have r : (2*y)%81 = (2*(y%81))%81 := by omega
  simp only [house] at e ⊢
  rw [q,r]
  omega

end Bigfoot
