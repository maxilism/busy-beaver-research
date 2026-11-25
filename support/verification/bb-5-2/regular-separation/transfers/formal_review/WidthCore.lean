import Splice

/-! Finite-span promises on canonical tapes. Each word has one additional
letter for its marked state and one bit per physical cell, including the
scanned cell on a blank tape. -/
namespace Width

def SeparatesThrough (W : Nat) (orbit halts accepts : List α → Prop) : Prop :=
  (∀ w, w.length - 1 ≤ W → orbit w → accepts w) ∧
  (∀ w, w.length - 1 ≤ W → halts w → ¬ accepts w)

theorem SeparatesThrough.mono {small large : Nat} {orbit halts accepts : List α → Prop}
    (h : small ≤ large) (sep : SeparatesThrough large orbit halts accepts) :
    SeparatesThrough small orbit halts accepts :=
  ⟨fun w hw => sep.1 w (Nat.le_trans hw h), fun w hw => sep.2 w (Nat.le_trans hw h)⟩

/-- It suffices that the n+1 diagonals and all their crosswords fit the
promise. The orientation of the halting crossword can vary between pairs. -/
theorem noSeparatorOfSlices {orbit halts : List α → Prop}
    (n W : Nat) (L : Splice.CutLanguage α n) (left right : Nat → List α)
    (diag : ∀ i, orbit (left i ++ right i))
    (off : ∀ i j, i < j → halts (left i ++ right j) ∨ halts (left j ++ right i))
    (width : ∀ i j : Fin (n+1), (left i.val ++ right j.val).length ≤ W+1) :
    ¬ SeparatesThrough W orbit halts L.accepts := by
  intro sep
  have fits (i j : Fin (n+1)) : (left i.val ++ right j.val).length - 1 ≤ W := by
    have := width i j
    omega
  obtain ⟨i,j,lt,xy,yx⟩ := Splice.acceptedSplices L (fun i => left i.val) (fun j => right j.val)
    (fun i => sep.1 _ (fits i i) (diag i.val))
  rcases off i.val j.val lt with bad | bad
  · exact sep.2 _ (fits i j) bad xy
  · exact sep.2 _ (fits j i) bad yx

end Width
