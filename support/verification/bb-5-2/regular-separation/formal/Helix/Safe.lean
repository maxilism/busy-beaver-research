import Helix.Nonhalt

/-! Section 3 checkpoint rejoin. The imbalanced cases differ: surplus left zeros
are repaired across *two* entries per triple; surplus right ones consume the
blank left margin without changing the visible prefix `10`. -/
namespace Helix.Obstruction
private theorem extplus (f : Wd) (a b : Nat) : ext0 (ext0 f a) b = ext0 f (a+b) := by
  simp [ext0]
private theorem upSome (g i b c : Nat) :
    Reach (Q (ext0 [true] (g+3*i)) b (c+3*i)) (Q (ext0 [true] g) (b+3*i) c) := by
  simpa only [extplus] using upAll (ext0 [true] g) i b c
private theorem marginAll (i b c : Nat) :
    Reach (Q [true,false] b (c+3*i)) (Q [true,false] (b+3*i) c) := by
  induction i generalizing b with
  | zero => exact .refl _
  | succ i ih =>
    have h := (upMargin b (c+3*i)).trans (ih (b+3))
    simpa only [show c+3*i+3=c+3*(i+1) by omega, show b+3+3*i=b+3*(i+1) by omega] using h

/-- Exhaust exactly the surplus left triples, keeping the exponent sum fixed. -/
theorem repairAll (g j : Nat) : Reach (gap (3*g+1) (3*j+1)) (T [] (3*g+3*j+2)) := by
  induction g generalizing j with
  | zero =>
    simp only [Nat.mul_zero,Nat.zero_add]
    change Reach (T [true,false] (3*j+1)) (T [] (3*j+2))
    rw [tTen]; exact Reach.refl _
  | succ g ih =>
    have r := repair (3*g) j
    rw [show 3*j+4=3*(j+1)+1 by omega] at r
    have h := r.trans (ih (j+1))
    simpa only [show 3*g+4=3*(g+1)+1 by omega,
                show 3*g+3*(j+1)+2=3*(g+1)+3*j+2 by omega] using h

private theorem rejoinLeft (g i j : Nat) :
    Reach (Q (ext0 [true] (3*g+1+3*i)) (3*j) (1+3*i))
          (T [] (3*g+3*j+3*i+2)) := by
  have u := upSome (3*g+1) i (3*j) 1
  have e := exitOne (ext0 [true] (3*g+1)) (3*j+3*i)
  rw [show 3*j+3*i=3*(j+i) by omega] at e u
  have h := u.trans (e.trans (repairAll g (j+i)))
  simpa only [show 3*(j+i)=3*j+3*i by omega,
              show 3*g+(3*j+3*i)+2=3*g+3*j+3*i+2 by omega] using h
private theorem rejoinRight (g i j : Nat) :
    Reach (Q (ext0 [true] (1+3*i)) (3*j) (1+3*g+3*i))
          (T [] (3*j+3*g+3*i+2)) := by
  have u := upSome 1 i (3*j) (1+3*g)
  have m := marginAll g (3*j+3*i) 1
  have e := exitOne [true,false] (3*j+3*i+3*g)
  rw [tTen] at e
  have h := u.trans (m.trans e)
  simpa only [show 3*j+3*i+3*g+1+1=3*j+3*g+3*i+2 by omega] using h

/-- Every Q in the *entire* paper family reaches the indicated edge, whether
its left counter is smaller, equal, or larger. -/
theorem Q_rejoin (a b c : Nat) (ha : a%3=1) (hb : b%3=0) (hc : c%3=1) :
    Reach (Q (ext0 [true] a) b c) (T [] (1+b+max a c)) := by
  by_cases h : c ≤ a
  · have p := rejoinLeft ((a-c)/3) (c/3) (b/3)
    simpa only [show 3*((a-c)/3)+1+3*(c/3)=a by omega,
                show 3*(b/3)=b by omega, show 1+3*(c/3)=c by omega,
                show 3*((a-c)/3)+b+3*(c/3)+2=1+b+max a c by omega] using p
  · have p := rejoinRight ((c-a)/3) (a/3) (b/3)
    simpa only [show 1+3*(a/3)=a by omega, show 3*(b/3)=b by omega,
                show 1+3*((c-a)/3)+3*(a/3)=c by omega,
                show b+3*((c-a)/3)+3*(a/3)+2=1+b+max a c by omega] using p

/-- Down sweeps preserve `b+max a c`; no positivity assumption is needed
in addition to the two residues, though the checkpoint language has it. -/
theorem P_rejoin (a b c : Nat) (ha : (a+b)%3=1) (hc : (c+b)%3=1) :
    Reach (P (ext0 [true] a) b c) (T [] (1+b+max a c)) := by
  have d := downAll (ext0 [true] a) b c
  rw [extplus] at d
  have h := d.trans (Q_rejoin (a+b) 0 (c+b) ha rfl hc)
  simpa only [show 1+0+max (a+b) (c+b)=1+b+max a c by omega] using h

/-- Precisely the union S in the checkpoint-family display of the manuscript (all residues mod 3). -/
inductive Checkpoint : Cfg → Prop where
  | edge (m : Nat) : m%3=2 → Checkpoint (T [] m)
  | downPhase (a b c : Nat) : 1≤a → 1≤c → (a+b)%3=1 → (c+b)%3=1 →
      Checkpoint (P (ext0 [true] a) b c)
  | upPhase (a b c : Nat) : a%3=1 → b%3=0 → c%3=1 → Checkpoint (Q (ext0 [true] a) b c)

private theorem target2 {n : Nat} (hn : n%3=2) : n=3*(n/3)+2 := by omega
/-- For *every* checkpoint, not just a checkpoint seen in experiments, exhibit
an actual blank-orbit edge to which its forward path rejoins. -/
theorem checkpointRejoin {s : Cfg} (hs : Checkpoint s) :
    ∃ j, Reach s (T [] (3*j+2)) ∧ Reach blank (T [] (3*j+2)) := by
  cases hs with
  | edge m hm => exact ⟨m/3, by rw [←target2 hm]; exact .refl _, rightEdges _⟩
  | downPhase a b c _ _ ha hc =>
    have h := P_rejoin a b c ha hc
    rw [target2 (n:=1+b+max a c) (by omega)] at h
    exact ⟨_,h,rightEdges _⟩
  | upPhase a b c ha hb hc =>
    have h := Q_rejoin a b c ha hb hc
    rw [target2 (n:=1+b+max a c) (by omega)] at h
    exact ⟨_,h,rightEdges _⟩

theorem checkpointSafe {s : Cfg} (hs : Checkpoint s) : Safe s := by
  obtain ⟨_,h,_⟩ := checkpointRejoin hs
  exact safePre h (edgeSafe _)
end Helix.Obstruction
