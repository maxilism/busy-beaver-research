import Helix.BlankSafe

/-! Safety of the blank run and its right edges, in a form convenient for
composing the positive checkpoint repair paths. `blank_safe` uses unbounded
stack values on the orbit; `safe_of_reaches_safe` uses determinism. -/
namespace Helix.Obstruction

def Safe (c : Cfg) := ∀ t, Reach c t → ¬ Halted t

theorem safePre {c d : Cfg} (p : Reach c d) (hd : Safe d) : Safe c :=
  safe_of_reaches_safe p hd

theorem blankSafe : Safe blank := fun _ h => blank_safe h

theorem edgeSafe (j : Nat) : Safe (T [] (3*j+2)) :=
  fun t p => blankSafe t ((rightEdges j).trans p)

end Helix.Obstruction
