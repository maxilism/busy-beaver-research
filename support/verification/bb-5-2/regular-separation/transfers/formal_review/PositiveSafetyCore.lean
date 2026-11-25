import Helix.Safe
import Helix.Tape

/-! Local one-step checks for a regular separator that can exit only at safe
sources. The same exit conditions also give blank coverage when there is an
independent invariant excluding those sources. -/
namespace PositiveSafetyCore
open Helix

def wordOf (l : Wd) (q : St) (x : Bool) (r : Wd) : List Sym :=
  l.map Sym.bit ++ [Sym.mark q, Sym.bit x] ++ r.map Sym.bit

def cfgOf (l : Wd) (q : St) (x : Bool) (r : Wd) : Cfg :=
  ⟨q, left l, x, r.foldr push 0⟩

theorem leftSnoc (l : Wd) (b : Bool) : left (l ++ [b]) = push b (left l) := by
  simp [left, List.foldl_append]

theorem leftReverse (l : Wd) : left l.reverse = l.foldr push 0 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [leftSnoc, List.reverse_cons, ih]

theorem cfgOfCanonical (c : Cfg) :
    cfgOf (cells c.l).reverse c.q c.x (cells c.r) = c := by
  cases c; simp [cfgOf, leftReverse, cellsValue]

private theorem cellsEncode (r : Wd) :
    ∃ n, r = cells (r.foldr push 0) ++ List.replicate n false := by
  induction r with
  | nil => exact ⟨0, by simp⟩
  | cons b r ih =>
    obtain ⟨n, hn⟩ := ih
    by_cases hz : push b (r.foldr push 0) = 0
    · have tail : r.foldr push 0 = 0 := by
        change 2 * r.foldr push 0 + b.toNat = 0 at hz; omega
      have hb : b = false := by
        cases b <;> simp_all [push, Bool.toNat]
      simp [hb, tail, cells0] at hn ⊢
      exact ⟨n+1, by rw [hn, List.replicate_succ]; simp [push, Bool.toNat]⟩
    · refine ⟨n, ?_⟩
      have hc : cells (push b (r.foldr push 0)) =
          b :: cells (r.foldr push 0) := by
        rw [cells, dite_eq_right hz]; simp
      simpa only [List.foldr_cons, hc, List.cons_append,
        List.cons.injEq, true_and] using hn

theorem paddedCanonical (l : Wd) (q : St) (x : Bool) (r : Wd) :
    ∃ i j, wordOf l q x r = List.replicate i (.bit false) ++
      display (cfgOf l q x r) ++ List.replicate j (.bit false) := by
  obtain ⟨i, hi⟩ := cellsEncode l.reverse
  have hval : l.reverse.foldr push 0 = left l := by
    simpa using (leftReverse l.reverse).symm
  rw [hval] at hi
  have hleft := congrArg List.reverse hi
  simp only [List.reverse_reverse, List.reverse_append, List.reverse_replicate] at hleft
  obtain ⟨j,hj⟩ := cellsEncode r
  refine ⟨i,j,?_⟩
  simp only [wordOf, display, cfgOf, List.append_assoc]
  conv => lhs; rw [hleft, hj]
  simp [List.map_append,List.append_assoc]

structure CutRules (K H : List Sym → Prop) : Prop where
  stepRight (l r : Wd) (q : St) (x b w : Bool) (t : St) :
    instruction q x = some (w,.R,t) →
    K (wordOf l q x (b::r)) → H (wordOf l q x (b::r)) ∨ K (wordOf (l++[w]) t b r)
  stepLeft (l r : Wd) (q : St) (x b w : Bool) (t : St) :
    instruction q x = some (w,.L,t) →
    K (wordOf (l++[b]) q x r) → H (wordOf (l++[b]) q x r) ∨ K (wordOf l t b (w::r))
  terminal (l r : Wd) (q : St) (x : Bool) :
    instruction q x = none → K (wordOf l q x r) → H (wordOf l q x r)

def CutConfig (H : List Sym → Prop) (c : Cfg) : Prop :=
  ∃ l q x r, cfgOf l q x r = c ∧ H (wordOf l q x r)

private theorem withNeighbors (c : Cfg) : ∃ (l r : Wd) (a b : Bool),
    cfgOf (l++[a]) c.q c.x (b::r) = c := by
  refine ⟨(cells (pop c.l)).reverse, cells (pop c.r), top c.l, top c.r, ?_⟩
  cases c
  simp [cfgOf,leftSnoc,leftReverse,cellsValue,push_unpack]

theorem oneStep {K H : List Sym → Prop} {P : Cfg → Prop} (rules : CutRules K H)
    (decode : ∀ l q x r, K (wordOf l q x r) ↔ P (cfgOf l q x r))
    (c : Cfg) (pc : P c) :
    CutConfig H c ∨ ∃ d, step c = some d ∧ P d := by
  obtain ⟨l,r,a,b,hc⟩ := withNeighbors c
  have hk := (decode _ _ _ _).mpr (hc ▸ pc)
  cases h : instruction c.q c.x with
  | none => exact Or.inl ⟨_,_,_,_,hc,rules.terminal _ _ _ _ h hk⟩
  | some tr =>
    obtain ⟨w,dir,t⟩ := tr
    cases dir with
    | R =>
      rcases rules.stepRight _ _ _ _ _ _ _ h hk with cut | after
      · exact Or.inl ⟨_,_,_,_,hc,cut⟩
      · refine Or.inr ⟨_, ?_, (decode _ _ _ _).mp after⟩
        have hcL := congrArg Cfg.l hc
        have hcR := congrArg Cfg.r hc
        simp only [cfgOf, List.foldr_cons] at hcL hcR
        simp only [step, h, F, cfgOf, leftSnoc, ← hcL, ← hcR, top_push, pop_push]
    | L =>
      rcases rules.stepLeft _ _ _ _ _ _ _ h hk with cut | after
      · exact Or.inl ⟨_,_,_,_,hc,cut⟩
      · refine Or.inr ⟨_, ?_, (decode _ _ _ _).mp after⟩
        have hcL := congrArg Cfg.l hc
        have hcR := congrArg Cfg.r hc
        simp only [cfgOf, leftSnoc, List.foldr_cons] at hcL hcR
        simp only [step,h,Helix.K,cfgOf,← hcL,← hcR,top_push,pop_push,List.foldr_cons]

theorem safety {H : List Sym → Prop} {P : Cfg → Prop}
    (each : ∀ c, P c → CutConfig H c ∨ ∃ d, step c = some d ∧ P d)
    (cutSafe : ∀ c, CutConfig H c → Helix.Obstruction.Safe c) :
    ∀ c, P c → Helix.Obstruction.Safe c := by
  intro c pc t path
  induction path with
  | refl c =>
    rcases each c pc with e | ⟨_,h,_⟩
    · exact cutSafe c e c (.refl _)
    · simp [Halted,h]
  | cons h path ih =>
    rcases each _ pc with e | ⟨_,hs,p⟩
    · exact cutSafe _ e _ (.cons h path)
    · rw [h] at hs
      cases hs
      exact ih p

theorem coverage {H : List Sym → Prop} {P J : Cfg → Prop}
    (each : ∀ c, P c → CutConfig H c ∨ ∃ d, step c = some d ∧ P d)
    (initial : P blank) (ji : J blank)
    (jc : ∀ c d, J c → step c = some d → J d)
    (exclusive : ∀ c, CutConfig H c → ¬ J c) :
    ∀ c, Reach blank c → P c := by
  intro c path
  have both : J c ∧ P c := Reach.closed (S := fun e => J e ∧ P e) (by
    intro s t st move
    refine ⟨jc s t st.1 move, ?_⟩
    rcases each s st.2 with e | ⟨u,m,pu⟩
    · exact False.elim (exclusive _ e st.1)
    · rw [move] at m; cases m; exact pu) path ⟨ji,initial⟩
  exact both.2

end PositiveSafetyCore
