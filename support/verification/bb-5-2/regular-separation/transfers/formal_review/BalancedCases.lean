import BalancedInduction
import BalancedMachine
import BalancedCatalog
import Splice

/-! The abstract tile proofs instantiate genuine paths on all twelve catalog
tables. The DFA argument uses the canonical word, with a state letter just
before the current bit; the split is reversed on the mirrored catalog table. -/
namespace BalancedCases

open Balanced BalancedTM

/-- Tiles on the right of the scanned zero, followed by one and the blank exterior. -/
def encode : List Tile → Nat
  | [] => o 0
  | .Z :: s => z (z (encode s))
  | .U :: s => o (o (encode s))
  | .T :: s => o (z (encode s))

private theorem lead_bit {s : List Tile} (h : Lead s) : ∃ t, encode s = o t := by
  cases s with
  | nil => exact ⟨0, rfl⟩
  | cons x s =>
    cases x with
    | Z => exact False.elim h
    | U => exact ⟨_, rfl⟩
    | T => exact ⟨_, rfl⟩

private theorem zeros_append (n : Nat) (s : List Tile) :
    encode (List.replicate n .Z ++ s) = bits false (2*n) (encode s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, encode, ih, Nat.mul_succ,
      bits_succ]

private theorem ones_append (n : Nat) (s : List Tile) :
    encode (List.replicate n .U ++ s) = bits true (2*n) (encode s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, encode, ih, Nat.mul_succ,
      bits_succ]

private theorem ones_rep (n : Nat) :
    encode (List.replicate n .U) = bits true (2*n) (o 0) := by
  simpa [encode] using ones_append n []

private theorem zeros_rep (n : Nat) :
    encode (List.replicate n .Z) = bits false (2*n) (o 0) := by
  simpa [encode] using zeros_append n []

/-- Primitive reachability, including an actual undefined instruction at
the end of a path represented abstractly by the halting cell. -/
def evidence (v : Variant) (start : Cfg) : Cell → Prop
  | .live d s => Path v start (cp d (encode s))
  | .halt => Fatal v start

private theorem raw_step (v : Variant) (start : Cfg) {a b : Cell}
    (h : Step a b) : evidence v start a → evidence v start b := by
  intro p
  cases h with
  | push d s => exact p.trans (rowPush v d (encode s))
  | fill d s lead =>
    obtain ⟨t, ht⟩ := lead_bit lead
    simp only [evidence, encode, ht] at p ⊢
    exact p.trans (rowFill v d t)
  | shift d j s =>
    simp only [evidence, ones_append, zeros_append, Nat.mul_succ, encode] at p ⊢
    have path := rowShift v d j (z (encode s))
    rw [bits_succ, ← bits_push] at path
    exact p.trans path
  | pop d j s lead =>
    obtain ⟨t, ht⟩ := lead_bit lead
    simp only [evidence, ones_append, encode, ht] at p ⊢
    have path := rowPop v d j t
    have hs : bits true (2*j+1) (z (o t)) = bits true (2*j) (o (z (o t))) := by
      rw [bits_succ, bits_push]
    have hd : bits true (2*j+5) t = bits true (2*(j+2)) (o t) := by
      rw [bits_push, show 2*j+5 = 2*(j+2)+1 by omega, bits_succ]
    rw [hs, hd] at path
    exact p.trans path
  | underflow j s lead =>
    obtain ⟨t, ht⟩ := lead_bit lead
    simp only [evidence, ones_append, encode, ht] at p ⊢
    obtain ⟨q, path, halt⟩ := rowHalt v j t
    rw [bits_succ, ← bits_push] at path
    exact ⟨q, p.trans path, halt⟩
  | margin d j =>
    simp only [evidence, ones_rep, zeros_rep, Nat.mul_succ] at p ⊢
    have path := rowShift v d j 0
    rw [z_zero, z_zero, bits_succ, ← bits_push] at path
    exact p.trans path

private theorem from_abstract (v : Variant) (c : Cfg) {a b : Cell}
    (h : Reach a b) : evidence v c a → evidence v c b :=
  Reach.inductAlong (evidence v c) (raw_step v c) h

/-- The finite-support configuration with a left bank of `a` pairs and right
bank of `b` pairs at the D checkpoint. -/
def checkpoint (a b : Nat) := cp a (encode (List.replicate b .T))

private def root (d : Bool) : St := if d then .D else .A

theorem reached (v : Variant) (d : Bool) (k : Nat) :
    Path v (blank (root d)) (checkpoint (d.toNat + k) k) := by
  apply from_abstract v _ (diagonal d.toNat k)
  cases d
  · exact blankA v
  · exact blankD v

theorem eventuallyHalts (v : Variant) {i j : Nat} (lt : i < j) : Fatal v (checkpoint i j) := by
  apply from_abstract v _ (fatal i j lt)
  exact Walk.nil _

/-- The usual canonical encoding includes the scanned bit even when it is zero. -/
inductive Symbol where
  | bit (x : Bool)
  | state (q : St)
  deriving DecidableEq

def side (n : Nat) : List Symbol :=
  if _h : n = 0 then [] else .bit (top n) :: side (pop n)
termination_by n
decreasing_by unfold pop; omega

def display (c : Cfg) : List Symbol :=
  (side c.l).reverse ++ [.state c.q, .bit (top c.r)] ++ side (pop c.r)

open BalancedCatalog

def orbit (v : Variant) (d : Bool) (w : List Symbol) : Prop :=
  ∃ c, Walk (catalogStep v d) (blank .A) c ∧ display c = w

def halters (v : Variant) (d : Bool) (w : List Symbol) : Prop :=
  ∃ c h, Walk (catalogStep v d) c h ∧ catalogStep v d h = none ∧ display c = w

private theorem actual_reached (v : Variant) (d : Bool) (k : Nat) :
    orbit v d (display (image v d (checkpoint (d.toNat + k) k))) := by
  refine ⟨_, ?_, rfl⟩
  have p := mapReach v d (reached v d k)
  simpa only [root, image_blank] using p

private theorem actual_halts (v : Variant) (d : Bool) {a b : Nat} (lt : a < b) :
    halters v d (display (image v d (checkpoint a b))) := by
  obtain ⟨h, p, q⟩ := eventuallyHalts v lt
  exact ⟨_, _, mapReach v d p, mapHalt v d q, rfl⟩

abbrev pairs (n : Nat) := encode (List.replicate n Tile.T)

def mark (v : Variant) (d : Bool) : List Symbol :=
  [.state (rename v d .D), .bit false]

private theorem view_direct (v : Variant) (d : Bool) (h : mirror v d = false) (a b : Nat) :
    display (image v d (checkpoint a b)) =
      (side (bank a)).reverse ++ (mark v d ++ side (pairs b)) := by
  simp [display, image, h, checkpoint, cp, pairs, mark, List.append_assoc]

private theorem view_reflected (v : Variant) (d : Bool) (h : mirror v d = true) (a b : Nat) :
    display (image v d (checkpoint a b)) =
      (side (pairs b)).reverse ++ (mark v d ++ side (bank a)) := by
  simp [display, image, h, checkpoint, cp, pairs, mark, List.append_assoc]

/-- Successive visits suffice at an A root. At a D root the first bank
starts one pair ahead, so select alternate visits. -/
def visitIndex (d : Bool) (i : Nat) := (d.toNat + 1) * i

private theorem stride (d : Bool) {i j : Nat} (h : i < j) :
    d.toNat + visitIndex d i < visitIndex d j := by
  cases d <;> simp [visitIndex, Bool.toNat] <;> omega

/-- Cut before the head marker in catalog orientation. Reflection exchanges
the two banks. -/
def sliceLeft (v : Variant) (d : Bool) (i : Nat) : List Symbol :=
  if mirror v d then (side (pairs (visitIndex d i))).reverse
  else (side (bank (d.toNat + visitIndex d i))).reverse

def sliceRight (v : Variant) (d : Bool) (j : Nat) : List Symbol :=
  mark v d ++
    if mirror v d then side (bank (d.toNat + visitIndex d j))
    else side (pairs (visitIndex d j))

theorem slice_properties (v : Variant) (d : Bool) :
    (∀ i, orbit v d (sliceLeft v d i ++ sliceRight v d i)) ∧
    (∀ i j, i < j → halters v d (sliceLeft v d i ++ sliceRight v d j) ∨
                    halters v d (sliceLeft v d j ++ sliceRight v d i)) := by
  cases h : mirror v d with
  | false =>
    simp only [sliceLeft, sliceRight, h, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro i
      simpa only [view_direct v d h] using actual_reached v d (visitIndex d i)
    · intro i j lt
      exact Or.inl (by simpa only [view_direct v d h] using actual_halts v d (stride d lt))
  | true =>
    simp only [sliceLeft, sliceRight, h, ↓reduceIte]
    constructor
    · intro i
      simpa only [view_reflected v d h] using actual_reached v d (visitIndex d i)
    · intro i j lt
      exact Or.inr (by simpa only [view_reflected v d h] using actual_halts v d (stride d lt))

/-- Every finite DFA accepting the canonical blank orbit accepts a canonical word
leading to a halt. BalancedCatalog.code and BalancedCatalog.machineId specify
the twelve literal choices. -/
theorem noSeparator (v : Variant) (d : Bool) :
    Splice.NoDFASeparator (orbit v d) (halters v d) := by
  obtain ⟨diag, off⟩ := slice_properties v d
  exact Splice.noSeparator_of_slices (sliceLeft v d) (sliceRight v d) diag off

/-- The same cuts preclude separators with nondeterminism and epsilon moves. -/
theorem noENFASeparator (v : Variant) (d : Bool) (n : Nat) (a : Splice.ENFA Symbol n) :
    ¬ ((∀ w, orbit v d w → a.accepts w) ∧ (∀ w, halters v d w → ¬ a.accepts w)) := by
  obtain ⟨diag, off⟩ := slice_properties v d
  exact Splice.noENFASeparator_of_slices (sliceLeft v d) (sliceRight v d) diag off a

private theorem accepts_path {v : Variant} {d : Bool} {n : Nat} {D : Splice.DFA Symbol n}
    (closed : ∀ c t, catalogStep v d c = some t → D.accepts (display c) → D.accepts (display t))
    {a b : Cfg} (p : Walk (catalogStep v d) a b) : D.accepts (display a) → D.accepts (display b) := by
  induction p with
  | nil => exact id
  | tick step _ ih => exact fun ha => ih (closed _ _ step ha)

/-- No DFA can contain the blank configuration, be closed under every actual step,
and exclude configurations with an undefined instruction. -/
theorem noInductiveSeparator (v : Variant) (d : Bool) (n : Nat) (D : Splice.DFA Symbol n) :
    ¬ (D.accepts (display (blank .A)) ∧
       (∀ c t, catalogStep v d c = some t → D.accepts (display c) → D.accepts (display t)) ∧
       (∀ c, catalogStep v d c = none → ¬ D.accepts (display c))) := by
  rintro ⟨initial, closed, safe⟩
  apply noSeparator v d n D
  constructor
  · rintro _ ⟨c, p, rfl⟩
    exact accepts_path closed p initial
  · rintro _ ⟨c, h, p, halt, rfl⟩ hc
    exact safe _ halt (accepts_path closed p hc)

end BalancedCases
