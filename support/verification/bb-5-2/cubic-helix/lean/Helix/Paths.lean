import Helix.Raw

/-!
# Composed machine paths for the cubic helix obstruction

All paths below compose the literal machine reachability lemmas of `Helix.Raw`.
The DFA substitutions in `Helix.Proof` are separate; they are not machine steps.
-/
namespace Helix.Obstruction

/-- Extend a prefix (in reading order) by `n` blanks. -/
def ext0 (f : Wd) (n : Nat) : Wd := f ++ List.replicate n false
private theorem ext0_add (f : Wd) (n m : Nat) :
    ext0 (ext0 f n) m = ext0 f (n+m) := by simp [ext0]
private theorem ext0_zero (f : Wd) : ext0 f 0 = f := by simp [ext0]

/-- In `b` down sweeps all `b` alternating pairs move into the two counters. -/
theorem downAll (f : Wd) (b c : Nat) :
    Reach (P f b c) (Q (ext0 f b) 0 (c+b)) := by
  induction b generalizing f c with
  | zero => simp only [ext0_zero, Nat.add_zero, pqZero]; exact Reach.refl _
  | succ b ih =>
    have a := (down f b c).trans (ih (f++[false]) (c+1))
    change Reach _ (Q (ext0 (ext0 f 1) b) 0 (c+1+b)) at a
    rw [ext0_add] at a
    simpa only [Nat.add_comm 1 b, Nat.add_assoc c 1 b] using a

/-- `i` ordinary up sweeps remove `3*i` zeros and ones. -/
theorem upAll (f : Wd) (i b c : Nat) :
    Reach (Q (ext0 f (3*i)) b (c+3*i)) (Q f (b+3*i) c) := by
  induction i generalizing b with
  | zero => simp [ext0_zero, Reach.refl]
  | succ i ih =>
    have a := (upThree (ext0 f (3*i)) b (c+3*i)).trans (ih (b+3))
    change Reach (Q (ext0 (ext0 f (3*i)) 3) b (c+3*i+3)) _ at a
    rw [ext0_add] at a
    simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm 3 (3*i)] using a

/-- Four-zero entry, followed by all down sweeps. -/
private theorem entryFourDown (h : Wd) (m : Nat) :
    Reach (T (h++[false,false,false,false]) m)
          (Q (ext0 (h++[true]) (m+2)) 0 (m+2)) := by
  have a := (entryFour h m).trans (downAll (h++[true,false]) (m+1) 1)
  have e : h++[true,false] = ext0 (h++[true]) 1 := by simp [ext0]
  rw [e, ext0_add] at a
  simpa only [show 1+(m+1) = m+2 by omega] using a

private theorem entryOneDown (h : Wd) (m : Nat) :
    Reach (T (h++[true]) m) (Q (ext0 h (m+1)) 0 (m+1)) := by
  have a := (entryOne h m).trans (downAll (h++[false]) m 1)
  change Reach _ (Q (ext0 (ext0 h 1) m) 0 (1+m)) at a
  rwa [ext0_add, Nat.add_comm 1 m] at a

/-- All blank-orbit right edges generate a checkpoint with equal counters. -/
theorem diagonal (m : Nat) :
    Reach (T [] m) (Q (ext0 [true] (m+2)) 0 (m+2)) := by
  have a := (entryBlank m).trans (downAll [true,false] (m+1) 1)
  change Reach _ (Q (ext0 (ext0 [true] 1) (m+1)) 0 (1+(m+1))) at a
  rwa [ext0_add, show 1+(m+1)=m+2 by omega] at a

/-- Exactly matched counters up to a residual left prefix and `c` right ones. -/
private theorem upTail (f : Wd) (g i c : Nat) :
    Reach (Q (ext0 f (g+3*i)) 0 (c+3*i)) (Q (ext0 f g) (3*i) c) := by
  simpa only [ext0_add, Nat.zero_add] using upAll (ext0 f g) i 0 c

def gap (g m : Nat) : Cfg := T (ext0 [true] g) m

/-- The up sweeps and exit on a balanced diagonal. -/
theorem edgeAfterDiag (j : Nat) :
    Reach (Q (ext0 [true] (3*j+2+2)) 0 (3*j+2+2)) (T [] (3*(j+1)+2)) := by
  rw [show 3*j+2+2 = 1+3*(j+1) by omega]
  have x := exitOne [true,false] (3*(j+1))
  rw [tTen] at x
  exact (upTail [true] 1 (j+1) 1).trans x

/-- Each diagonal return increments the right-edge exponent by three. -/
theorem rightEdges (j : Nat) : Reach blank (T [] (3*j+2)) := by
  induction j with
  | zero => exact blankReachR2
  | succ j ih => exact ih.trans ((diagonal (3*j+2)).trans (edgeAfterDiag j))

/-- Two successive entry/return cycles repair three excess zeros. -/
theorem repair (g i : Nat) :
    Reach (gap (g+4) (3*i+1)) (gap (g+1) (3*i+4)) := by
  let h := ext0 [true] g
  have d := entryFourDown h (3*i+1)
  have e : 3*i+1+2 = 3*(i+1) := by omega
  rw [e] at d
  have u := upAll (h++[true]) (i+1) 0 0
  simp only [Nat.zero_add] at u
  have d' := entryOneDown h (3*(i+1))
  have u' := upTail h 1 (i+1) 1
  rw [Nat.add_comm 1 (3*(i+1))] at u'
  have path := d.trans (u.trans ((exitZero _ _).trans (d'.trans (u'.trans (exitOne _ _)))))
  change Reach (T (ext0 h 4) (3*i+1)) (T (ext0 h 1) (3*(i+1)+1)) at path
  simpa only [gap, h, ext0_add, show 3*(i+1)+1=3*i+4 by omega] using path

/-- Repair until gap seven, stopping deliberately before the next repair. -/
theorem repairToSeven (r i : Nat) :
    Reach (gap (3*r+7) (3*i+1)) (gap 7 (3*i+1+3*r)) := by
  induction r generalizing i with
  | zero => exact Reach.refl _
  | succ r ih =>
    have d := repair (3*r+6) i
    rw [show 3*r+6+4=3*(r+1)+7 by omega, show 3*i+4=3*(i+1)+1 by omega] at d
    have u := ih (i+1)
    rw [show 3*(i+1)+1+3*r=3*i+1+3*(r+1) by omega] at u
    exact d.trans u

def dangerPrefix : Wd := [true,false,false,false,true]

/-- Pumped first diagonal leads to a checkpoint whose fixed left prefix is `10001`. -/
theorem forceSecondSite (i r : Nat) :
    Reach (Q (ext0 [true] (3*i+1+(3*r+6))) 0 (3*i+1))
          (Q (ext0 dangerPrefix (3*i+1+3*r+2)) 0 (3*i+1+3*r+2)) := by
  have u := upTail [true] (3*r+7) i 1
  rw [show 3*r+7+3*i=3*i+1+(3*r+6) by omega, Nat.add_comm 1 (3*i)] at u
  have x := exitOne (ext0 [true] (3*r+7)) (3*i)
  have d := entryFourDown [true,false,false,false] (3*i+1+3*r)
  exact u.trans (x.trans ((repairToSeven r i).trans d))

/-- Removing the period's worth of zeros at the forced checkpoint leaves
    enough ones for a final genuine up-scan into `D1`. -/
theorem secondSiteHalts (j r : Nat) :
    ∃ t, Reach (Q (ext0 dangerPrefix (3*j)) 0 (3*j+(3*r+6))) t ∧ Halted t := by
  have u := upAll dangerPrefix j 0 (3*r+6)
  rw [Nat.add_comm (3*r+6) (3*j), Nat.zero_add] at u
  obtain ⟨t, h, bad⟩ := up_partial_10001 (3*j) (3*r+6) (by omega)
  exact ⟨t, u.trans h, bad⟩

end Helix.Obstruction
