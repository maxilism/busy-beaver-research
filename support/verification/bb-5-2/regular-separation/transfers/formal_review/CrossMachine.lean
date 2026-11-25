import BalancedMachine
import PilotMachine

/-! Seven-state census row 12,767,546. This uses the same nearest-bit-first
integer stacks as the balanced machines. F and G guard the E0 instruction. -/
namespace Cross

open BalancedTM (Dir push z o top pop bits bits_push bits_succ bank)
abbrev St := Pilot.St

structure Cfg where
  q : St
  l : Nat
  r : Nat
  deriving DecidableEq, Repr

abbrev F (q : St) (l r : Nat) : Cfg := ⟨q,l,r⟩
def K (q : St) (l r : Nat) : Cfg := F q (pop l) (push (top l) r)

def instruction : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true,.R,.B)
  | .A, true  => some (true,.R,.A)
  | .B, false => some (true,.L,.C)
  | .B, true  => some (true,.L,.B)
  | .C, false => some (false,.R,.D)
  | .C, true  => some (false,.L,.C)
  | .D, false => some (true,.R,.E)
  | .D, true  => none
  | .E, false => some (false,.R,.F)
  | .E, true  => some (true,.L,.A)
  | .F, false => some (true,.R,.F)
  | .F, true  => some (true,.L,.G)
  | .G, false => some (false,.R,.A)
  | .G, true  => some (false,.L,.G)

private def letter : St → String
  | .A => "A" | .B => "B" | .C => "C" | .D => "D"
  | .E => "E" | .F => "F" | .G => "G"

private def actionString (q : St) (x : Bool) : String :=
  match instruction q x with
  | none => "---"
  | some (b,d,p) => (if b then "1" else "0") ++ (if d == .R then "R" else "L") ++ letter p

theorem literal12767546 :
    String.intercalate "_" ([Pilot.St.A,.B,.C,.D,.E,.F,.G].map fun q =>
      actionString q false ++ actionString q true) =
    "1RB1RA_1LC1LB_0RD0LC_1RE---_0RF1LA_1RF1LG_0RA0LG" := by decide

def step (c : Cfg) : Option Cfg := do
  let (w,d,q) ← instruction c.q (top c.r)
  match d with
  | .R => return F q (push w c.l) (pop c.r)
  | .L => return K q c.l (push w (pop c.r))

inductive Path : Cfg → Cfg → Prop where
  | nil (c) : Path c c
  | tick {a b c} : step a = some b → Path b c → Path a c

theorem Path.trans {a b c : Cfg} (p : Path a b) (q : Path b c) : Path a c := by
  induction p with
  | nil => exact q
  | tick st _ ih => exact .tick st (ih q)

def run : Nat → Cfg → Option Cfg
  | 0,c => some c
  | n+1,c => (step c).bind (run n)
theorem ofRun (n) {a b : Cfg} (h : run n a = some b) : Path a b := by
  induction n generalizing a with
  | zero => cases h; exact .nil _
  | succ n ih =>
    cases st : step a with
    | none => simp [run,st] at h
    | some k => exact .tick st (ih (by simpa [run,st] using h))

macro "crossSteps" n:num : tactic => `(tactic|
  (apply Cross.ofRun $n
   simp [Cross.run,Cross.step,Cross.instruction,Cross.K]))

def cp (d s : Nat) := F .D (bank d) (z s)
def blank := F .A 0 0
def Fatal (c : Cfg) := ∃ h, Path c h ∧ step h = none

theorem o_ne_zero (r : Nat) : o r ≠ 0 := by simp [o,push,Bool.toNat]
theorem z_ne_zero {r : Nat} (h : r ≠ 0) : z r ≠ 0 := by simp [z,push,Bool.toNat]; omega

private theorem firstOne {r : Nat} (nz : r ≠ 0) : ∃ k s, r = bits false k (o s) := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    have un := BalancedTM.push_parts r
    cases hx : top r with
    | true => exact ⟨0,pop r, by simpa only [BalancedTM.bits_zero,hx] using un.symm⟩
    | false =>
      rw [hx] at un
      change z (pop r) = r at un
      have lt : pop r < r := by unfold pop; omega
      have hn : pop r ≠ 0 := by intro eq; rw [eq] at un; exact nz un.symm
      obtain ⟨k,s,hs⟩ := ih (pop r) lt hn
      exact ⟨k+1,s,by rw [bits_succ,← hs]; exact un.symm⟩

private theorem scanRestore (k l r : Nat) :
    Path (F .F l (bits false k (o r))) (K .G l (bits false k (o r))) := by
  induction k generalizing l with
  | zero => change Path (F .F l (o r)) (K .G l (o r)); crossSteps 1
  | succ k ih =>
    have enter : Path (F .F l (z (bits false k (o r)))) (F .F (o l) (bits false k (o r))) := by crossSteps 1
    apply enter.trans ((ih (o l)).trans ?_)
    crossSteps 1

/-- F searches arbitrary distance for the first one. G undoes its marks up
to the zero left by E0 and re-enters A on the original F cell. -/
theorem scanReturn (l r : Nat) (h : r ≠ 0) : Path (F .F (z l) r) (F .A (z l) r) := by
  obtain ⟨k,s,rfl⟩ := firstOne h
  apply (scanRestore k (z l) s).trans
  crossSteps 1

theorem emptyScan (k l : Nat) : run k (F .F l 0) = some (F .F (bits true k l) 0) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih => simpa [run,step,instruction,bits_push] using ih (o l)

/-- Each E0 checkpoint reaches the helper's entry in two literal steps. -/
theorem enterF (d r : Nat) : Path (cp d (z r)) (F .F (bank (d+1)) r) := by
  unfold cp
  apply ofRun 2
  simp [run,step,instruction,bank]

private theorem startZero (d r : Nat) (nz : r ≠ 0) :
    Path (cp d (z r)) (F .A (bank (d+1)) r) :=
  (enterF d r).trans (scanReturn _ r nz)

private theorem startOne (d r : Nat) : Path (cp d (o r)) (F .A (o (o (bank d))) r) := by
  unfold cp
  crossSteps 4

private theorem aPair (l r : Nat) :
    Path (F .A l (o (o r))) (F .A (o (o l)) r) := by
  crossSteps 2

private theorem bPair (l r : Nat) :
    Path (K .B (o (o l)) r) (K .B l (o (o r))) := by
  crossSteps 2

private theorem cOne (l r : Nat) :
    Path (K .C (o l) r) (K .C l (z r)) := by
  apply ofRun 1
  simp [run,step,instruction,K]

private theorem aSweep (j l r : Nat) :
    Path (F .A l (bits true (2*j) r)) (F .A (bits true (2*j) l) r) := by
  induction j generalizing l with
  | zero => exact .nil _
  | succ j ih =>
    rw [show 2*(j+1)=2*j+2 by omega]
    simp only [bits_succ]
    exact (aPair _ _).trans (by simpa only [bits_push] using ih (o (o l)))

private theorem bSweep (j l r : Nat) :
    Path (K .B (bits true (2*j) l) r) (K .B l (bits true (2*j) r)) := by
  induction j generalizing r with
  | zero => exact .nil _
  | succ j ih =>
    rw [show 2*(j+1)=2*j+2 by omega]
    simp only [bits_succ]
    exact (bPair _ _).trans (by simpa only [bits_push] using ih (o (o r)))

private theorem cSweep (j l r : Nat) :
    Path (K .C (bits true j l) r) (K .C l (bits false j r)) := by
  induction j generalizing r with
  | zero => exact .nil _
  | succ j ih =>
    exact (cOne _ _).trans (by simpa only [bits_succ,bits_push] using ih (z r))

theorem rowPush (d s : Nat) (h : s ≠ 0) :
    Path (cp d (z (z (z (z s))))) (cp (d+1) (o (z s))) := by
  apply (startZero d _ (z_ne_zero (z_ne_zero (z_ne_zero h)))).trans
  apply ofRun 4
  simp [run,step,instruction,K,cp,bank]

theorem fillStartF (d s : Nat) :
    Path (cp d (z (z (o s)))) (F .F (bank (d+1)) (z (o s))) :=
  enterF d (z (o s))

theorem fillFinishF (d s : Nat) :
    Path (F .F (bank (d+1)) (z (o s))) (cp d (o (o (o s)))) := by
  apply (scanReturn (o (bank d)) (z (o s)) (z_ne_zero (o_ne_zero s))).trans
  apply ofRun 6
  cases d <;> simp [run,step,instruction,K,cp,bank]

theorem rowFill (d s : Nat) :
    Path (cp d (z (z (o s)))) (cp d (o (o (o s)))) :=
  (fillStartF d s).trans (fillFinishF d s)

theorem rowShift (d j s : Nat) :
    Path (cp d (bits true (2*j+1) (z (z s))))
      (cp d (bits false (2*j+2) (o s))) := by
  apply (startOne d _).trans
  apply (aSweep j _ _).trans
  have cross : Path (F .A (bits true (2*j) (o (o (bank d)))) (z (z s)))
      (K .C (bits true (2*j+3) (bank d)) (o s)) := by
    apply ofRun 2
    simp [run,step,instruction,K,bits_push]
  apply cross.trans
  apply (cSweep (2*j+3) _ _).trans
  cases d <;> apply ofRun 1 <;> simp [run,step,instruction,K,cp,bank]

private theorem popPrefix (d j s : Nat) :
    Path (cp d (bits true (2*j+1) (z (o s))))
      (K .B (bank d) (bits true (2*j+4) s)) := by
  apply (startOne d _).trans
  apply (aSweep j _ _).trans
  have cross : Path (F .A (bits true (2*j) (o (o (bank d)))) (z (o s)))
      (K .B (bits true (2*j+4) (bank d)) s) := by
    apply ofRun 1
    simp [run,step,instruction,K,bits_push]
  apply cross.trans
  simpa only [show 2*(j+2)=2*j+4 by omega] using bSweep (j+2) (bank d) s

theorem rowPop (d j s : Nat) :
    Path (cp (d+1) (bits true (2*j+1) (z (o s)))) (cp d (bits true (2*j+5) s)) := by
  apply (popPrefix (d+1) j s).trans
  cases d <;> apply ofRun 3 <;> simp [run,step,instruction,K,cp,bank]

theorem rowHalt (j s : Nat) :
    Fatal (cp 0 (bits true (2*j+1) (z (o s)))) := by
  refine ⟨F .D 0 (o (bits true (2*j+4) s)), (popPrefix 0 j s).trans ?_, ?_⟩
  · apply ofRun 2
    simp [run,step,instruction,K,bank]
  · simp [step,instruction]

theorem blankA : Path blank (cp 0 (o 0)) := by
  apply ofRun 4
  simp [run,step,instruction,blank,K,cp,bank]


end Cross
