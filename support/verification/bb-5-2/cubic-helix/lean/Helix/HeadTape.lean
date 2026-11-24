import Helix.Tape

/-! Representation theorem: the implementation by two naturals is exactly the
ordinary finite-support, two-way tape **with coordinates relative to the head**.
Reading an absolute cell at `head+i` eliminates precisely global translations.
`step_view` checks every shift and write against this coordinate semantics. -/
namespace Helix.Pointed

/-- Zero-extended interpretation of a binary stack. -/
def atDepth (s : Nat) : Nat → Bool
  | 0 => top s
  | i+1 => atDepth (pop s) i
private theorem bitBeyond (s i : Nat) (h : s ≤ i) : atDepth s i = false := by
  induction i generalizing s with
  | zero => have hs : s=0 := by omega
            subst s; rfl
  | succ i ih => apply ih; unfold pop; omega
private def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k+1 => push (f 0) (pack (fun i => f (i+1)) k)
private theorem bitPack {k : Nat} {f : Nat → Bool} (h : ∀ i, k≤i → f i=false) (i : Nat) :
    atDepth (pack f k) i = f i := by
  induction k generalizing i f with
  | zero => rw [h i (by omega)]; exact bitBeyond 0 i (by omega)
  | succ k ih =>
    cases i with
    | zero => simp [pack,atDepth]
    | succ i => simp only [pack,atDepth,pop_push]; exact ih (fun i hi => h (i+1) (by omega)) i
private theorem packBits (s k : Nat) (h : s ≤ k) : pack (atDepth s) k = s := by
  induction k generalizing s with
  | zero => have hs : s=0 := by omega
            subst s; rfl
  | succ k ih => change push (top s) (pack (atDepth (pop s)) k) = s
                 rw [ih _ (by unfold pop; omega), push_unpack]
private theorem depthInj (a b : Nat) (h : ∀ i, atDepth a i = atDepth b i) : a=b := by
  rw [←packBits a (max a b) (by omega), show atDepth a = atDepth b from funext h,
      packBits b _ (by omega)]

@[ext] structure Tape where
  q : St
  bit : Int → Bool

def FiniteSupport (t : Tape) : Prop :=
  ∃ k : Nat, ∀ i : Nat, k≤i → t.bit (.negSucc i) = false ∧ t.bit (.ofNat (i+1)) = false
/-- Head at coordinate zero. Negative offsets index the left stack; positive
    ones index the right stack. -/
def view (c : Cfg) : Tape := ⟨c.q, fun i => match i with
  | .ofNat 0 => c.x
  | .ofNat (i+1) => atDepth c.r i
  | .negSucc i => atDepth c.l i⟩

theorem view_finite (c : Cfg) : FiniteSupport (view c) :=
  ⟨max c.l c.r,fun i hi => ⟨bitBeyond _ _ (by omega),bitBeyond _ _ (by omega)⟩⟩

theorem view_injective {a b : Cfg} (h : view a = view b) : a=b := by
  have hq : a.q=b.q := congrArg Tape.q h
  have hx : a.x=b.x := congrArg (fun t : Tape => t.bit 0) h
  have hl := depthInj a.l b.l (fun i => congrArg (fun t : Tape => t.bit (.negSucc i)) h)
  have hr := depthInj a.r b.r (fun i => congrArg (fun t : Tape => t.bit (.ofNat (i+1))) h)
  cases a; cases b; congr

theorem view_surjective {t : Tape} (h : FiniteSupport t) : ∃ c, view c=t := by
  obtain ⟨k,h⟩ := h
  let c : Cfg := ⟨t.q,pack (fun i => t.bit (.negSucc i)) k,t.bit 0,
                          pack (fun i => t.bit (.ofNat (i+1))) k⟩
  refine ⟨c,?_⟩
  cases t with | mk q bits =>
    refine Tape.ext ?_ ?_
    <;> try rfl
    funext i
    cases i with
    | negSucc i => exact bitPack (fun j hj => (h j hj).1) _
    | ofNat i => cases i with
                 | zero => rfl
                 | succ i => exact bitPack (fun j hj => (h j hj).2) _

/-- True mathematical translation-invariant one-step semantics: first write
    at old origin, then translate the head to the adjacent cell. -/
def overwrite (f : Int → Bool) (w : Bool) (i : Int) : Bool := if i=0 then w else f i
def shift (d : Dir) (i : Int) := match d with | .R => i+1 | .L => i-1
def tapeStep (t : Tape) : Option Tape :=
  match instruction t.q (t.bit 0) with
  | none => none
  | some (w,d,q) => some ⟨q,fun i => overwrite t.bit w (shift d i)⟩
private theorem moveR (c : Cfg) (w : Bool) (q : St) :
    view (F q (push w c.l) c.r) = ⟨q,fun i => overwrite (view c).bit w (i+1)⟩ := by
  refine Tape.ext ?_ ?_
    <;> try rfl
  funext i
  cases i with
  | negSucc i => cases i with
                 | zero => exact top_push w c.l
                 | succ j => simp [view,F,atDepth,overwrite, show Int.negSucc (j+1)+1=Int.negSucc j by omega]
  | ofNat i => cases i <;> rfl
private theorem moveL (c : Cfg) (w : Bool) (q : St) :
    view (K q c.l (push w c.r)) = ⟨q,fun i => overwrite (view c).bit w (i-1)⟩ := by
  refine Tape.ext ?_ ?_
    <;> try rfl
  funext i
  cases i with
  | negSucc i => rfl
  | ofNat i => cases i with
               | zero => rfl
               | succ i => cases i with
                          | zero => simp [view,K,atDepth,overwrite]
                          | succ j =>
                            change atDepth (pop (push w c.r)) j = overwrite _ w (Int.ofNat (j+1+1)-1)
                            have e : Int.ofNat (j+1+1)-1=Int.ofNat (j+1) := by
                              simp
                            rw [e]; change _ = atDepth c.r j; rw [pop_push]
/-- Literal stacks faithfully simulate every cell, not just the checkpoints.
    Combined with `view_surjective`/`view_injective` this is a conjugacy. -/
theorem step_view (c : Cfg) : (step c).map view = tapeStep (view c) := by
  unfold step tapeStep; change _ = match instruction c.q c.x with | none => none | some (w,d,q) => _
  cases h : instruction c.q c.x with
  | none => rfl
  | some ins => rcases ins with ⟨w,d,q⟩; cases d with
                | L => exact congrArg some (moveL c w q)
                | R => exact congrArg some (moveR c w q)

/-- Ordinary absolute coordinates (no normalization). -/
structure Placed where
  q : St
  head : Int
  bit : Int → Bool

def center (a : Placed) : Tape := ⟨a.q,fun i => a.bit (a.head+i)⟩
def translated (a b : Placed) : Prop :=
  ∃ k : Int, a.q=b.q ∧ b.head=a.head+k ∧ ∀ i, a.bit i=b.bit (i+k)

/-- Centering identifies exactly translation and nothing else. -/
theorem center_eq_iff_translated (a b : Placed) : center a = center b ↔ translated a b := by
  constructor
  · intro h
    refine ⟨b.head-a.head,congrArg Tape.q h,by omega,?_⟩
    intro i
    have he := congrArg (fun t : Tape => t.bit (i-a.head)) h
    change a.bit (a.head+(i-a.head))=b.bit (b.head+(i-a.head)) at he
    simpa only [show a.head+(i-a.head)=i by omega,
                show b.head+(i-a.head)=i+(b.head-a.head) by omega] using he
  · rintro ⟨k,hq,hh,hc⟩
    refine Tape.ext hq ?_
    funext i; change a.bit (a.head+i) = b.bit (b.head+i)
    rw [hc,hh,show a.head+i+k=a.head+k+i by omega]

theorem center_surjective (t : Tape) : ∃ a, center a = t := by
  refine ⟨⟨t.q,0,t.bit⟩, Tape.ext rfl ?_⟩
  funext i; exact congrArg t.bit (Int.zero_add i)

/-- The finite side word used in the DFA display really is the observed
sequence of cells (with zero supplied off its far end). -/
theorem displayedBit (s i : Nat) : (cells s)[i]?.getD false = atDepth s i := by
  induction s using Nat.strongRecOn generalizing i with
  | ind s ih =>
    by_cases h : s=0
    · subst s; rw [cells0,bitBeyond 0 i (by omega)]; simp
    · rw [cells,dite_eq_right h]; cases i with
      | zero => rfl
      | succ i => exact ih (pop s) (by unfold pop; omega) i

/-- Any displayed side is empty or ends in a one. Thus its far boundary is
minimal, and the scanned cell itself is never trimmed by `display`. -/
theorem displayedEdge (s : Nat) : cells s=[] ∨ ∃ f, cells s=f++[true] := by
  induction s using Nat.strongRecOn with
  | ind s ih =>
    by_cases hs : s=0
    · subst s; exact .inl cells0
    · right; rw [cells,dite_eq_right hs]
      rcases ih (pop s) (by unfold pop; omega) with hz | ⟨f,hf⟩
      · have hp : pop s=0 := by simpa [hz] using (cellsValue (pop s)).symm
        have hb : top s=true := by
          have e := push_unpack s
          rw [hp] at e
          cases h : top s with
          | true => rfl
          | false => rw [h] at e; exact (hs e.symm).elim
        exact ⟨[],by rw [hz,hb]; rfl⟩
      · exact ⟨top s::f, by rw [hf]; rfl⟩
end Helix.Pointed
