import BalancedInduction

/-! A visit just before the fill rule, inside the odd-length conversion.
Its intermediate F state on the literal seven-state tape gives the first
weighted search candidate. -/

namespace CrossInduction

open Balanced

/-- Starting with 2k+1 zero tiles exposes one zero tile before k T tiles
at depth d+k. The tail is arbitrary and stays attached. -/
theorem oddNested (d k : Nat) (s : List Tile) :
    Reach (.live d (List.replicate (2*k+1) .Z ++ s))
      (.live (d+k) (.Z :: (List.replicate k .T ++ s))) := by
  induction k generalizing d s with
  | zero => exact .refl _
  | succ k ih =>
    let m := 2*k
    have ar : 2*(k+1)+1 = (m+1)+2 := by dsimp [m]; omega
    rw [ar, List.replicate_succ, List.replicate_succ (n := m+1),
      List.cons_append, List.cons_append]
    apply Reach.cons (Step.push d (List.replicate (m+1) Tile.Z ++ s))
    rw [rep_snoc Tile.Z m s]
    have hs := slide (d+1) m 0 m (.Z :: s) (by omega)
      (fun j _ t ht => convert j (d+1) t ht)
    apply Reach.trans (by simpa only [Nat.zero_add, List.replicate_zero, List.nil_append] using hs)
    apply Reach.cons (Step.shift (d+1) m s)
    rw [rep_snoc Tile.T k s]
    simpa only [m, show d+1+k=d+(k+1) by omega] using ih (d+1) (.T :: s)

/-- The A-start abstract orbit reaches the source of the selected fill row. -/
theorem fromBlankOdd (k : Nat) :
    Reach (.live 0 []) (.live k (.Z :: List.replicate k .T)) := by
  apply Reach.trans (roundStart 0 (2*k+1))
  simpa only [List.append_nil, Nat.zero_add] using oddNested 0 k []

/-- The remaining pops in a right-heavy word force an underflow, even with
the extra U tile introduced by the fill. -/
theorem fatalAfterFill (a b : Nat) (h : a < b) :
    Reach (.live a (.U :: List.replicate b .T)) .halt :=
  manyPops a b 1 h

end CrossInduction
