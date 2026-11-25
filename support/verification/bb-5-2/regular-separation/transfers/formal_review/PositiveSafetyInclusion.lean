import PositiveSafetyProjection
import PositiveSafetyPadding
import Helix.HeadTape

/-! Agreement between the published machine and the automaton on padded tapes. -/

namespace PositiveSafetyInclusion
open Helix PositiveSafetyProjection

private theorem run_after (s : PositiveSafetyAuto.State) (w : List Sym)
    (hs : s ≠ PositiveSafetyAuto.start) :
    proj (PositiveSafetyAuto.read s w) = PositiveDFA.read (proj s) w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    change proj (PositiveSafetyAuto.read (PositiveSafetyAuto.move s a) w) =
      PositiveDFA.read (PositiveDFA.move (proj s) a) w
    rw [ih _ (move_ne_start _ _ (Or.inl hs)), proj_move _ _ (Or.inl hs)]

private theorem left_agrees (n : Nat) :
    proj (PositiveSafetyAuto.read PositiveSafetyAuto.start ((cells n).reverse.map Sym.bit)) =
      PositiveDFA.read PositiveDFA.start ((cells n).reverse.map Sym.bit) := by
  rcases Pointed.displayedEdge n with empty | ⟨body, last⟩
  · simpa only [empty, List.reverse_nil, List.map_nil, PositiveSafetyAuto.read, PositiveDFA.read, List.foldl_nil] using proj_start
  · simp only [last, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.map_cons]
    change proj (PositiveSafetyAuto.read (PositiveSafetyAuto.move PositiveSafetyAuto.start (.bit true)) _) =
      PositiveDFA.read (PositiveDFA.move PositiveDFA.start (.bit true)) _
    have first : Sym.bit true ≠ .bit false := by decide
    rw [run_after _ _ (move_ne_start _ _ (Or.inr first)), proj_move _ _ (Or.inr first), proj_start]

private theorem read_append (s : PositiveSafetyAuto.State) (u v : List Sym) :
    PositiveSafetyAuto.read s (u ++ v) =
      PositiveSafetyAuto.read (PositiveSafetyAuto.read s u) v := List.foldl_append

/-- On a minimally displayed tape the padded automaton and source DFA agree. -/
theorem canonical_iff (c : Cfg) : PositiveSafetyAuto.K (display c) ↔ PositiveDFA.accepts c := by
  let l := (cells c.l).reverse.map Sym.bit
  let s := PositiveSafetyAuto.read PositiveSafetyAuto.start l
  have hp : proj s = PositiveDFA.read PositiveDFA.start l := left_agrees c.l
  suffices eq : PositiveSafetyAuto.final (PositiveSafetyAuto.read PositiveSafetyAuto.start (display c)) =
      PositiveDFA.final (PositiveDFA.read PositiveDFA.start (display c)) by
    unfold PositiveSafetyAuto.K PositiveDFA.accepts PositiveDFA.acceptsWord
    rw [eq]
  change PositiveSafetyAuto.final (PositiveSafetyAuto.read PositiveSafetyAuto.start
      (l ++ [Sym.mark c.q, Sym.bit c.x] ++ (cells c.r).map Sym.bit)) =
    PositiveDFA.final (PositiveDFA.read PositiveDFA.start
      (l ++ [Sym.mark c.q, Sym.bit c.x] ++ (cells c.r).map Sym.bit))
  rcases Pointed.displayedEdge c.r with empty | ⟨body, last⟩
  · simp only [empty, List.map_nil, List.append_nil, read_append, PositiveDFA.read_append]
    change PositiveSafetyAuto.final (PositiveSafetyAuto.move (PositiveSafetyAuto.move s _) _) =
      PositiveDFA.final (PositiveDFA.move (PositiveDFA.move (PositiveDFA.read PositiveDFA.start l) _) _)
    rw [final_head, hp]
  · simp only [last, List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
      read_append, PositiveDFA.read_append]
    let mark := Sym.mark c.q
    let h := PositiveSafetyAuto.move s mark
    have marker : mark ≠ .bit false := by unfold mark; intro e; cases e
    have hstart : h ≠ PositiveSafetyAuto.start := move_ne_start _ _ (Or.inr marker)
    have hm : proj h = PositiveDFA.move (PositiveDFA.read PositiveDFA.start l) mark := by
      rw [← hp]; exact proj_move _ _ (Or.inr marker)
    change PositiveSafetyAuto.final (PositiveSafetyAuto.move
        (PositiveSafetyAuto.read (PositiveSafetyAuto.move h (.bit c.x)) (body.map Sym.bit)) (.bit true)) =
      PositiveDFA.final (PositiveDFA.move
        (PositiveDFA.read (PositiveDFA.move (PositiveDFA.move (PositiveDFA.read PositiveDFA.start l) mark)
          (.bit c.x)) (body.map Sym.bit)) (.bit true))
    rw [final_one, run_after _ _ (move_ne_start _ _ (Or.inl hstart)),
      proj_move _ _ (Or.inl hstart), hm]

/-- Any number of displayed blank cells on either side preserves the same decision. -/
theorem pad_display_iff (i j : Nat) (c : Cfg) :
    PositiveSafetyAuto.K (List.replicate i (.bit false) ++ display c ++ List.replicate j (.bit false)) ↔
    PositiveDFA.accepts c :=
  (PositiveSafetyPadding.pad_iff i j c).trans (canonical_iff c)

end PositiveSafetyInclusion
