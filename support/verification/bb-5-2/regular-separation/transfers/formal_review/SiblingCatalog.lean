import SiblingCases

/-! The two catalog tables and the reflection used to read the B and E starts of
the cubic helix. The Boolean index is false for 5377178 and true for 7138511.
The scanned bit stays with the head when the tape is reflected. -/
namespace SiblingCatalog

open Helix

def catalogId (s : Bool) : Nat := if s then 7138511 else 5377178

def rename : Bool → St → St
  | false, .A => .D | false, .B => .A | false, .C => .B
  | false, .D => .C | false, .E => .E
  | true, .A => .E | true, .B => .B | true, .C => .C
  | true, .D => .D | true, .E => .A

/-- In catalog ordering the two literal tables are
    1RB0RE_0RC0RA_1LD---_1LA0LB_1RA0LC and
    1RB0LD_1RC0RA_0RD0RB_1LE---_1LB0LC. -/
def table : Bool → St → Bool → Option (Bool × Dir × St)
  | false, .A, false => some (true, .R, .B)
  | false, .A, true  => some (false, .R, .E)
  | false, .B, false => some (false, .R, .C)
  | false, .B, true  => some (false, .R, .A)
  | false, .C, false => some (true, .L, .D)
  | false, .C, true  => none
  | false, .D, false => some (true, .L, .A)
  | false, .D, true  => some (false, .L, .B)
  | false, .E, false => some (true, .R, .A)
  | false, .E, true  => some (false, .L, .C)
  | true, .A, false => some (true, .R, .B)
  | true, .A, true  => some (false, .L, .D)
  | true, .B, false => some (true, .R, .C)
  | true, .B, true  => some (false, .R, .A)
  | true, .C, false => some (false, .R, .D)
  | true, .C, true  => some (false, .R, .B)
  | true, .D, false => some (true, .L, .E)
  | true, .D, true  => none
  | true, .E, false => some (true, .L, .B)
  | true, .E, true  => some (false, .L, .C)

private def codeState : St → String
  | .A => "A" | .B => "B" | .C => "C" | .D => "D" | .E => "E"

private def codeInstruction : Option (Bool × Dir × St) → String
  | none => "---"
  | some (bit, dir, target) =>
    (if bit then "1" else "0") ++ (match dir with | .L => "L" | .R => "R") ++ codeState target

def catalogCode (s : Bool) : String :=
  String.intercalate "_" ([St.A, .B, .C, .D, .E].map
    (fun q => codeInstruction (table s q false) ++ codeInstruction (table s q true)))

theorem literal5377178 :
    catalogCode false = "1RB0RE_0RC0RA_1LD---_1LA0LB_1RA0LC" := by decide

theorem literal7138511 :
    catalogCode true = "1RB0LD_1RC0RA_0RD0RB_1LE---_1LB0LC" := by decide

def step (s : Bool) (c : Cfg) : Option Cfg :=
  match table s c.q c.x with
  | none => none
  | some (w, .L, q) => some (K q c.l (push w c.r))
  | some (w, .R, q) => some (F q (push w c.l) c.r)

/-- The stacks are nearest-cell first on both sides. -/
def mirror (s : Bool) (c : Cfg) : Cfg := ⟨rename s c.q, c.r, c.x, c.l⟩

private def renameBack : Bool → St → St
  | false, .A => .B | false, .B => .C | false, .C => .D
  | false, .D => .A | false, .E => .E
  | true, q => rename true q

def unmirror (s : Bool) (c : Cfg) : Cfg := ⟨renameBack s c.q, c.r, c.x, c.l⟩

@[simp] theorem unmirror_mirror (s : Bool) (c : Cfg) : unmirror s (mirror s c) = c := by
  rcases c with ⟨q,l,b,r⟩
  cases s <;> cases q <;> rfl

@[simp] theorem mirror_unmirror (s : Bool) (c : Cfg) : mirror s (unmirror s c) = c := by
  rcases c with ⟨q,l,b,r⟩
  cases s <;> cases q <;> rfl

theorem stepMirror (s : Bool) (c : Cfg) :
    step s (mirror s c) = (Helix.step c).map (mirror s) := by
  rcases c with ⟨q,l,b,r⟩
  cases s <;> cases q <;> cases b <;> rfl

inductive Reach (s : Bool) : Cfg → Cfg → Prop where
  | refl (c) : Reach s c c
  | cons {c d e} : step s c = some d → Reach s d e → Reach s c e

theorem reachMirror (s : Bool) {c d : Cfg} (run : Helix.Reach c d) :
    Reach s (mirror s c) (mirror s d) := by
  induction run with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (by rw [stepMirror,h]; rfl) ih

theorem reachUnmirror (s : Bool) {c d : Cfg} (run : Reach s c d) :
    Helix.Reach (unmirror s c) (unmirror s d) := by
  induction run with
  | refl => exact .refl _
  | @cons c d e h _ ih =>
    have eqv := stepMirror s (unmirror s c)
    rw [mirror_unmirror, h] at eqv
    cases raw : Helix.step (unmirror s c) with
    | none => simp [raw] at eqv
    | some v =>
      have hd : d = mirror s v := by simpa [raw] using eqv
      exact .cons (by simpa [hd] using raw) ih

theorem reachMirror_iff (s : Bool) (c d : Cfg) :
    Reach s (mirror s c) (mirror s d) ↔ Helix.Reach c d :=
  ⟨fun h => by simpa using reachUnmirror s h, reachMirror s⟩

theorem haltMirror (s : Bool) {c : Cfg} (h : Halted c) :
    step s (mirror s c) = none := by
  rw [stepMirror, h]; rfl

def Orbit (s : Bool) (w : List Sym) : Prop :=
  ∃ c, Reach s blank c ∧ display c = w

def Fatal (s : Bool) (w : List Sym) : Prop :=
  ∃ c h, display c = w ∧ Reach s c h ∧ step s h = none

/-- Split the actual reflected word immediately after the head cell. The left
part depends only on the original right block, even when exterior zeros trim. -/
def reflectedPrefix (s : Bool) (c : Nat) : List Sym :=
  (cells (z (ones c))).reverse.map Sym.bit ++ [.mark (rename s .D), .bit false]

def reflectedSuffix (f : Wd) : List Sym := (cells (left f)).map Sym.bit

theorem displayMirrorQ (s : Bool) (f : Wd) (c : Nat) :
    display (mirror s (Q f 0 c)) = reflectedPrefix s c ++ reflectedSuffix f := by
  simp [display, mirror, Q, F, oz, reflectedPrefix, reflectedSuffix]

/-- At a reflected cut, a shorter left word supplies the original right bank
and a longer right word supplies the original left bank. -/
private theorem noSeparatorFromCheckpoints (s : Bool) (baseBlank : Cfg)
    (start : mirror s baseBlank = blank) (leftBank : Nat → Wd) (count : Nat → Nat)
    (diag : ∀ i, Helix.Reach baseBlank (Q (leftBank i) 0 (count i)))
    (cross : ∀ i j, i < j → ∃ h, Helix.Reach (Q (leftBank j) 0 (count i)) h ∧ Halted h) :
    Splice.NoDFASeparator (Orbit s) (Fatal s) := by
  apply Splice.noSeparator_of_slices (fun i => reflectedPrefix s (count i))
    (fun j => reflectedSuffix (leftBank j))
  · intro i
    exact ⟨_, start ▸ reachMirror s (diag i), displayMirrorQ s _ _⟩
  · intro i j hlt
    obtain ⟨h, reachable, halted⟩ := cross i j hlt
    exact Or.inl ⟨_, mirror s h, displayMirrorQ s _ _, reachMirror s reachable, haltMirror s halted⟩

/-- In each literal table, the canonical blank-orbit words and all canonical
words from configurations that eventually halt are regularly inseparable. -/
theorem noSeparator (s : Bool) : Splice.NoDFASeparator (Orbit s) (Fatal s) := by
  apply noSeparatorFromCheckpoints s (Siblings.root s) (by cases s <;> rfl)
    (fun i => Obstruction.ext0 (Siblings.w s ++ [true]) (6*(i+1))) (fun i => 6*(i+1))
  · exact Siblings.reachesX s
  · intro i j h
    exact Siblings.haltsX s h

theorem noSeparator5377178 : Splice.NoDFASeparator (Orbit false) (Fatal false) :=
  noSeparator false

theorem noSeparator7138511 : Splice.NoDFASeparator (Orbit true) (Fatal true) :=
  noSeparator true

end SiblingCatalog
