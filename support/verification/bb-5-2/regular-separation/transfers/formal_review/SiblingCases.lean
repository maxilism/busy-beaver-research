import SiblingPaths
import Splice
import Helix.Tape

/-! Ordinary regular inseparability for the B and E starts of the original
cubic-helix table. Both visit all positive multiples of three on the same
diagonal, with a different fixed prefix. The splice uses every second visit. -/
namespace Helix.Siblings
open Obstruction

/-- False selects the B start; true selects the E start. -/
def w (s : Bool) : Wd := if s then [true,false] else []
def root (s : Bool) : Cfg := F (if s then .E else .B) 0 0

private theorem startup (s : Bool) : Reach (root s) (T (w s ++ [false]) 1) := by
  cases s
  · exact reach_run 7 rfl
  · exact reach_run 21 rfl

/-- The extra fourteen single steps of the E-start entry, with the complete
unscanned right context kept symbolic. -/
private theorem finishE (r : Nat) :
    Reach (K .B (o (left [true,false,false])) r)
          (F .D (left [true,false,true,false]) (z (o (z r)))) := by
  change Reach (K .B (o (z (z (o 0)))) r) (F .D (z (o (z (o 0)))) (z (o (z r))))
  fixed 14

private theorem siblingEntry (s : Bool) (m : Nat) :
    Reach (T (w s ++ [false]) m) (P (w s ++ [true,false]) (m+1) 1) := by
  cases s
  · exact entryBlank m
  · exact (entryScan [true,false,false] m).trans (finishE (oz m (z (o 0))))

private theorem appendOneZero (f : Wd) (k : Nat) :
    ext0 (f ++ [false]) k = ext0 f (k+1) := by
  simp [ext0, List.replicate_succ, List.append_assoc]

private theorem firstDiagonal (s : Bool) (m : Nat) :
    Reach (T (w s ++ [false]) m) (Q (ext0 (w s ++ [true]) (m+2)) 0 (m+2)) := by
  have p := (siblingEntry s m).trans (downAll (w s ++ [true,false]) (m+1) 1)
  rw [show w s ++ [true,false] = (w s ++ [true]) ++ [false] by simp,
      appendOneZero] at p
  simpa only [show 1+(m+1)=m+2 by omega] using p

private theorem nextEdge (s : Bool) (i : Nat) :
    Reach (Q (ext0 (w s ++ [true]) (3*i)) 0 (3*i)) (T (w s ++ [false]) (3*i+1)) := by
  have u := upAll (w s ++ [true]) i 0 0
  simp only [Nat.zero_add] at u
  have d := (entryOne (w s) (3*i)).trans (downAll (w s ++ [false]) (3*i) 1)
  have u' := upAll (w s ++ [false]) i 0 1
  rw [Nat.zero_add] at u'
  exact u.trans ((exitZero _ _).trans (d.trans (u'.trans (exitOne _ _))))

private theorem edges (s : Bool) (i : Nat) :
    Reach (root s) (T (w s ++ [false]) (3*i+1)) := by
  induction i with
  | zero => exact startup s
  | succ i ih =>
    have d := firstDiagonal s (3*i+1)
    rw [show 3*i+1+2=3*(i+1) by omega] at d
    exact ih.trans (d.trans (nextEdge s (i+1)))

/-- Each positive multiple of three occurs as the size of both banks. -/
theorem reachesDiagonal (s : Bool) (i : Nat) :
    Reach (root s) (Q (ext0 (w s ++ [true]) (3*(i+1))) 0 (3*(i+1))) := by
  have d := (edges s i).trans (firstDiagonal s (3*i+1))
  simpa only [show 3*i+1+2=3*(i+1) by omega] using d

/-- The hybrid made from the left prefix of visit i and the right suffix of
visit j. Six-step spacing in block size keeps the mixed excess at least six. -/
def X (s : Bool) (i j : Nat) : Cfg := Q (ext0 (w s ++ [true]) (6*(i+1))) 0 (6*(j+1))

theorem reachesX (s : Bool) (i : Nat) : Reach (root s) (X s i i) := by
  simpa only [X, show 3*(2*i+1+1)=6*(i+1) by omega] using reachesDiagonal s (2*i+1)

theorem haltsX (s : Bool) {i j : Nat} (h : i<j) :
    ∃ t, Reach (X s j i) t ∧ Halted t := by
  have p := hybridHalts (w s ++ [true]) (2*(i+1)) (6*(j-i)) (by omega)
  rw [show 3*(2*(i+1))+6*(j-i)=6*(j+1) by omega,
      show 3*(2*(i+1))=6*(i+1) by omega] at p
  exact p

def leftWord (s : Bool) (i : Nat) : List Sym :=
  (ext0 (w s ++ [true]) (6*(i+1))).map Sym.bit

def suffix (j : Nat) : List Sym :=
  [Sym.mark .D, Sym.bit false, Sym.bit false] ++ List.replicate (6*(j+1)) (Sym.bit true)

theorem displayX (s : Bool) (i j : Nat) : display (X s i j) = leftWord s i ++ suffix j := by
  have h : 6*(j+1) = (6*j+5)+1 := by omega
  cases s <;> simp only [X, leftWord, suffix, h, w, Bool.false_eq_true, ↓reduceIte,
    List.nil_append, ext0, List.cons_append, displayQ0, List.append_assoc]

def orbitWords (s : Bool) (word : List Sym) : Prop :=
  ∃ c, Reach (root s) c ∧ display c = word

def fatalWords (word : List Sym) : Prop :=
  ∃ c t, display c = word ∧ Reach c t ∧ Halted t

theorem noSeparator (s : Bool) : Splice.NoDFASeparator (orbitWords s) fatalWords := by
  apply Splice.noSeparator_of_slices (leftWord s) suffix
  · intro i; exact ⟨_, reachesX s i, displayX s i i⟩
  · intro i j h
    obtain ⟨t, reaches, halts⟩ := haltsX s h
    exact Or.inr ⟨_, t, displayX s j i, reaches, halts⟩

end Helix.Siblings
