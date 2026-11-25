import CrossMachine
import CrossInduction
import BalancedCases
import Splice

/-! Both top-ranked cuts in census row 12,767,546. The length sampler uses
the D checkpoint from a conversion of an even number of zero tiles. The weighted
sampler uses an F checkpoint two steps into a fill reached by the corresponding
odd-length nesting. A one in the alternating right bank ends the helper call. -/
namespace CrossCases
open Balanced (Cell Tile Lead)
open BalancedTM (z o bank bits bits_succ bits_push top pop top_push pop_push z_zero)
open BalancedCases (encode)
open Cross (Cfg St F cp Path Fatal blank)
open Pilot (Sym)

/-- A tile list always ends in the nonblank sentinel. -/
private theorem encode_pos (s : List Tile) : 0 < encode s := by
  induction s with
  | nil => decide
  | cons a s ih => cases a <;> simp [encode, BalancedTM.push, Bool.toNat] <;> omega

private theorem lead_one {s : List Tile} (h : Lead s) : ∃ t, encode s = o t := by
  cases s with
  | nil => exact ⟨0, rfl⟩
  | cons x s => cases x with
    | Z => exact False.elim h
    | U => exact ⟨_,rfl⟩
    | T => exact ⟨_,rfl⟩

private theorem zeros (j : Nat) (s : List Tile) :
    encode (List.replicate j .Z ++ s) = bits false (2*j) (encode s) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [List.replicate_succ, List.cons_append, encode, ih, Nat.mul_succ, bits_succ]

private theorem ones (j : Nat) (s : List Tile) :
    encode (List.replicate j .U ++ s) = bits true (2*j) (encode s) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [List.replicate_succ, List.cons_append, encode, ih, Nat.mul_succ, bits_succ]

private def interprets (c : Cfg) : Cell → Prop
  | .live d s => Path c (cp d (encode s))
  | .halt => Fatal c

private theorem raw {c : Cfg} {a b : Cell} (h : Balanced.Step a b) :
    interprets c a → interprets c b := by
  intro p
  cases h with
  | push d s => exact p.trans (Cross.rowPush d (encode s) (Nat.ne_of_gt (encode_pos s)))
  | fill d s h =>
    obtain ⟨t, ht⟩ := lead_one h
    simp only [interprets, encode, ht] at p ⊢
    exact p.trans (Cross.rowFill d t)
  | shift d j s =>
    simp only [interprets, ones, zeros, Nat.mul_succ, encode] at p ⊢
    have q := Cross.rowShift d j (z (encode s))
    rw [bits_succ, ← bits_push] at q
    exact p.trans q
  | pop d j s h =>
    obtain ⟨t, ht⟩ := lead_one h
    simp only [interprets, ones, encode, ht] at p ⊢
    have q := Cross.rowPop d j t
    have a : bits true (2*j+1) (z (o t)) = bits true (2*j) (o (z (o t))) := by
      rw [bits_succ, bits_push]
    have b : bits true (2*j+5) t = bits true (2*(j+2)) (o t) := by
      rw [bits_push, show 2*j+5 = 2*(j+2)+1 by omega, bits_succ]
    rw [a,b] at q
    exact p.trans q
  | underflow j s h =>
    obtain ⟨t, ht⟩ := lead_one h
    simp only [interprets, ones, encode, ht] at p ⊢
    obtain ⟨q, path, halt⟩ := Cross.rowHalt j t
    rw [bits_succ, ← bits_push] at path
    exact ⟨q,p.trans path,halt⟩
  | margin d j =>
    have emptyOnes := ones j []
    have emptyZeros := zeros (j+1) []
    simp only [List.append_nil] at emptyOnes emptyZeros
    simp only [interprets, emptyOnes, emptyZeros, Nat.mul_succ, encode] at p ⊢
    have q := Cross.rowShift d j 0
    rw [z_zero, z_zero, bits_succ, ← bits_push] at q
    exact p.trans q

private theorem usePath (c : Cfg) {a b : Cell} (p : Balanced.Reach a b) :
    interprets c a → interprets c b :=
  p.inductAlong (interprets c) raw

private abbrev bankTail (k : Nat) := encode (List.replicate k Tile.T)

def dCut (a b : Nat) := cp a (bankTail b)
def fCut (a b : Nat) := F .F (bank (a+1)) (z (bankTail b))

theorem reachedD (n : Nat) : Path blank (dCut n n) := by
  have diag := Balanced.diagonal 0 n
  simp only [Nat.zero_add] at diag
  exact usePath blank diag Cross.blankA

theorem fatalD {a b : Nat} (h : a < b) : Fatal (dCut a b) :=
  usePath _ (Balanced.fatal a b h) (Cross.Path.nil _)

private theorem bankTail_one (k : Nat) : ∃ s, bankTail k = o s := by
  cases k with
  | zero => exact ⟨_,rfl⟩
  | succ k => exact ⟨z (bankTail k), by simp [bankTail, List.replicate_succ, encode]⟩

theorem reachedF (n : Nat) : Path blank (fCut n n) := by
  have p : Path blank (cp n (z (z (bankTail n)))) :=
    usePath blank (CrossInduction.fromBlankOdd n) Cross.blankA
  obtain ⟨r, hr⟩ := bankTail_one n
  rw [hr] at p
  simpa only [fCut, hr] using p.trans (Cross.fillStartF n r)

theorem fatalF {a b : Nat} (h : a < b) : Fatal (fCut a b) := by
  apply usePath _ (CrossInduction.fatalAfterFill a b h)
  change Path (F .F (bank (a+1)) (z (bankTail b))) (cp a (o (o (bankTail b))))
  obtain ⟨r, hr⟩ := bankTail_one b
  rw [hr]
  exact Cross.fillFinishF a r

/-- A right-pointing state marker before the scanned bit, even on an exterior zero. -/
def display (c : Cfg) : List Sym :=
  (Helix.cells c.l).reverse.map Sym.bit ++ [.mark c.q,.bit (top c.r)] ++
    (Helix.cells (pop c.r)).map Sym.bit

def leftWord : Nat → List Sym
  | 0 => []
  | k+1 => leftWord k ++ [.bit true, .bit false]

def rightWord : Nat → List Sym
  | 0 => []
  | k+1 => .bit false :: .bit true :: rightWord k

private theorem cellsPush (b : Bool) (l : Nat) (h : BalancedTM.push b l ≠ 0) :
    Helix.cells (BalancedTM.push b l) = b :: Helix.cells l := by
  change Helix.push b l ≠ 0 at h
  change Helix.cells (Helix.push b l) = _
  rw [Helix.cells]
  simp only [dite_eq_right h, Helix.top_push, Helix.pop_push]

private theorem nz1 (l : Nat) : o l ≠ 0 := by simp [BalancedTM.push, Bool.toNat]
private theorem nz0 (l : Nat) (h : l ≠ 0) : z l ≠ 0 := by
  simp only [BalancedTM.push, Bool.toNat_false, Nat.add_zero]
  omega

private theorem bankWord (k : Nat) : (Helix.cells (bank k)).reverse.map Sym.bit = leftWord k := by
  induction k with
  | zero => simp [leftWord,bank]
  | succ k ih =>
    simp only [bank, cellsPush false _ (nz0 _ (nz1 _)), cellsPush true _ (nz1 _), List.reverse_cons,
      List.map_append, List.map_cons, List.map_nil, List.append_assoc, leftWord, ih]
    simp

private theorem tailWord (k : Nat) :
    .bit false :: (Helix.cells (bankTail k)).map Sym.bit = rightWord (k+1) := by
  induction k with
  | zero =>
    change Sym.bit false :: (Helix.cells (o 0)).map Sym.bit = _
    rw [cellsPush true _ (nz1 _)]
    simp [rightWord]
  | succ k ih =>
    have hs : bankTail (k+1) = o (z (bankTail k)) := by simp [bankTail,List.replicate_succ,encode]
    rw [hs, cellsPush true _ (nz1 _), cellsPush false _ (nz0 _ (Nat.ne_of_gt (encode_pos _)))]
    change Sym.bit false :: Sym.bit true :: _ = _
    exact congrArg (fun t => Sym.bit false :: Sym.bit true :: t) ih

theorem dCutWord (a b : Nat) :
    display (dCut a b) = leftWord a ++ (.mark .D :: rightWord (b+1)) := by
  simp only [display, dCut, cp, F, top_push, pop_push, bankWord, List.append_assoc,
    List.cons_append, List.nil_append, tailWord]

theorem fCutWord (a b : Nat) :
    display (fCut a b) = leftWord (a+1) ++ (.mark .F :: rightWord (b+1)) := by
  simp only [display, fCut, F, top_push, pop_push, bankWord, List.append_assoc,
    List.cons_append, List.nil_append, tailWord]

def orbit (w : List Sym) : Prop := ∃ c, Path blank c ∧ display c = w
def halters (w : List Sym) : Prop := ∃ c, Fatal c ∧ display c = w

/-- The length-based search's rank-one family, (10)^n D (01)^(n+1). -/
theorem noSeparatorFromD : Splice.NoDFASeparator orbit halters :=
  Splice.noSeparator_of_slices leftWord (fun j => .mark .D :: rightWord (j+1))
    (fun i => ⟨_, reachedD i, dCutWord i i⟩)
    (fun _ _ h => Or.inl ⟨_, fatalD h, dCutWord _ _⟩)

/-- The weighted search's rank-one family, (10)^(n+1) F (01)^(n+1). -/
theorem noSeparatorFromF : Splice.NoDFASeparator orbit halters :=
  Splice.noSeparator_of_slices (fun i => leftWord (i+1)) (fun j => .mark .F :: rightWord (j+1))
    (fun i => ⟨_, reachedF i, fCutWord i i⟩)
    (fun _ _ h => Or.inl ⟨_, fatalF h, fCutWord _ _⟩)

end CrossCases

#print axioms CrossCases.noSeparatorFromF
#print axioms CrossCases.noSeparatorFromD
