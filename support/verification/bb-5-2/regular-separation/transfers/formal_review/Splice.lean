import Std

/-! A cut-state proof of ordinary regular inseparability on words over any alphabet.
The finite version uses just one more diagonal than the number of states. Either
orientation of a mixed word may be forbidden. -/
namespace Splice

/-- Among `n+1` cuts in an `n`-state automaton, two ordered indices share a state. -/
theorem repeatCut {n : Nat} (cut : Fin (n+1) → Fin n) :
    ∃ i j : Fin (n+1), i < j ∧ cut i = cut j := by
  classical
  apply Classical.byContradiction
  intro h
  have nd : (List.ofFn cut).Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hi' : i < n+1 := by simpa using hi
    have hj' : j < n+1 := by simpa using hj
    intro eqv
    apply h
    exact ⟨⟨i, hi'⟩, ⟨j, hj'⟩, hij, by simpa only [List.getElem_ofFn] using eqv⟩
  have le := nd.length_le_of_subset (l₂ := List.finRange n)
    (fun {s} _ => List.mem_finRange s)
  simp only [List.length_ofFn, List.length_finRange] at le
  omega

structure DFA (α : Type) (n : Nat) where
  start : Fin n
  move : Fin n → α → Fin n
  final : Fin n → Prop

def DFA.accepts (d : DFA α n) (w : List α) : Prop := d.final (w.foldl d.move d.start)

/-- An `n`-state NFA also has a cut state, chosen from an accepting path for
each diagonal. Prefix and suffix relations can include arbitrary ε-moves. -/
structure CutLanguage (α : Type) (n : Nat) where
  accepts : List α → Prop
  left : List α → Fin n → Prop
  right : Fin n → List α → Prop
  split : ∀ u v, accepts (u ++ v) ↔ ∃ s, left u s ∧ right s v

def DFA.cuts (d : DFA α n) : CutLanguage α n where
  accepts := d.accepts
  left := fun u s => u.foldl d.move d.start = s
  right := fun s v => d.final (v.foldl d.move s)
  split := by intro u v; simp [DFA.accepts, List.foldl_append]

/-- Multiple initial states and ε-moves are permitted. -/
structure ENFA (α : Type) (n : Nat) where
  start : Fin n → Prop
  edge : Fin n → Option α → Fin n → Prop
  final : Fin n → Prop

namespace ENFA

variable (a : ENFA α n)

inductive Silent : Fin n → Fin n → Prop where
  | refl (p) : Silent p p
  | step : a.edge p none q → Silent q r → Silent p r

theorem Silent.trans {p q r} (h : a.Silent p q) (g : a.Silent q r) : a.Silent p r := by
  induction h with
  | refl => exact g
  | step he _ ih => exact .step he (ih g)

def reads : List α → Fin n → Fin n → Prop
  | [], p, q => a.Silent p q
  | x :: xs, p, q =>
    ∃ s t, a.Silent p s ∧ a.edge s (some x) t ∧ reads xs t q

private theorem prefixSilent {u : List α} {p q r : Fin n}
    (h : a.Silent p q) (g : a.reads u q r) : a.reads u p r := by
  cases u with
  | nil => exact h.trans _ g
  | cons x xs =>
    obtain ⟨s, t, eps, e, rest⟩ := g
    exact ⟨s, t, h.trans _ eps, e, rest⟩

theorem reads_append (u v : List α) (p q : Fin n) :
    a.reads (u ++ v) p q ↔ ∃ s, a.reads u p s ∧ a.reads v s q := by
  induction u generalizing p with
  | nil =>
    constructor
    · exact fun h => ⟨p, Silent.refl p, h⟩
    · rintro ⟨s, eps, rest⟩
      exact a.prefixSilent eps rest
  | cons x xs ih =>
    constructor
    · rintro ⟨s, t, eps, e, rest⟩
      obtain ⟨k, pre, post⟩ := (ih t).mp rest
      exact ⟨k, ⟨s, t, eps, e, pre⟩, post⟩
    · rintro ⟨k, ⟨s, t, eps, e, pre⟩, post⟩
      exact ⟨s, t, eps, e, (ih t).mpr ⟨k, pre, post⟩⟩

def accepts (w : List α) : Prop := ∃ p q, a.start p ∧ a.reads w p q ∧ a.final q

def cuts : CutLanguage α n where
  accepts := a.accepts
  left := fun u s => ∃ p, a.start p ∧ a.reads u p s
  right := fun s v => ∃ q, a.reads v s q ∧ a.final q
  split := by
    intro u v
    constructor
    · rintro ⟨p, q, start, h, final⟩
      obtain ⟨s, left, right⟩ := (a.reads_append u v p q).mp h
      exact ⟨s, ⟨p, start, left⟩, ⟨q, right, final⟩⟩
    · rintro ⟨s, ⟨p, start, left⟩, ⟨q, right, final⟩⟩
      exact ⟨p, q, start, (a.reads_append u v p q).mpr ⟨s, left, right⟩, final⟩

end ENFA

/-- Both crosswords have accepting paths, since each side of either path can
be followed or preceded by the matching path for the other diagonal. -/
theorem acceptedSplices {n : Nat} (L : CutLanguage α n)
    (left right : Fin (n+1) → List α)
    (accept : ∀ i, L.accepts (left i ++ right i)) :
    ∃ i j : Fin (n+1), i < j ∧
      L.accepts (left i ++ right j) ∧ L.accepts (left j ++ right i) := by
  classical
  have states (i) := (L.split (left i) (right i)).mp (accept i)
  let cut := fun i => Classical.choose (states i)
  have paths (i) : L.left (left i) (cut i) ∧ L.right (cut i) (right i) :=
    Classical.choose_spec (states i)
  obtain ⟨i, j, lt, eqv⟩ := repeatCut cut
  refine ⟨i, j, lt, (L.split ..).mpr ⟨cut i, (paths i).1, ?_⟩,
    (L.split ..).mpr ⟨cut j, (paths j).1, ?_⟩⟩
  · rw [eqv]; exact (paths j).2
  · rw [← eqv]; exact (paths i).2

/-- The standard notion on finite words: a finite deterministic automaton must
accept every member of `orbit` and may accept no member of `halts`. -/
def NoDFASeparator (orbit halts : List α → Prop) : Prop :=
  ∀ (n : Nat) (d : DFA α n),
    ¬ ((∀ w, orbit w → d.accepts w) ∧ (∀ w, halts w → ¬ d.accepts w))

theorem noCutSeparator {orbit halts : List α → Prop} {n : Nat}
    (L : CutLanguage α n) (left right : Fin (n+1) → List α)
    (diag : ∀ i, orbit (left i ++ right i))
    (off : ∀ i j, i < j → halts (left i ++ right j) ∨ halts (left j ++ right i)) :
    ¬ ((∀ w, orbit w → L.accepts w) ∧ (∀ w, halts w → ¬ L.accepts w)) := by
  intro sep
  obtain ⟨i, j, lt, h₁, h₂⟩ := acceptedSplices L left right (fun i => sep.1 _ (diag i))
  rcases off i j lt with bad | bad
  · exact sep.2 _ bad h₁
  · exact sep.2 _ bad h₂

theorem noSeparator_of_slices {orbit halts : List α → Prop}
    (left right : Nat → List α)
    (diag : ∀ i, orbit (left i ++ right i))
    (off : ∀ i j, i < j → halts (left i ++ right j) ∨ halts (left j ++ right i)) :
    NoDFASeparator orbit halts := by
  intro n d
  exact noCutSeparator d.cuts (fun i => left i.val) (fun i => right i.val)
    (fun i => diag i.val) (fun i j h => off i.val j.val h)

theorem noENFASeparator_of_slices {orbit halts : List α → Prop}
    (left right : Nat → List α)
    (diag : ∀ i, orbit (left i ++ right i))
    (off : ∀ i j, i < j → halts (left i ++ right j) ∨ halts (left j ++ right i))
    (a : ENFA α n) :
    ¬ ((∀ w, orbit w → a.accepts w) ∧ (∀ w, halts w → ¬ a.accepts w)) :=
  noCutSeparator a.cuts (fun i => left i.val) (fun i => right i.val)
    (fun i => diag i.val) (fun i j h => off i.val j.val h)


end Splice
