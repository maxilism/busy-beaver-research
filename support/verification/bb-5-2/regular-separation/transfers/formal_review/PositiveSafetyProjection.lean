import PositiveSafetyAuto

/-! The padded automaton tracks the shipped state after the first nonzero
symbol. It can also remember an accepting trailing zero extension. On the
last one of a tape, or immediately after the marked head and scanned bit,
its acceptance agrees with the shipped state. -/
namespace PositiveSafetyProjection

open Helix


set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Byte i is the canonical state underlying padded state i. -/
private def projectionBytes : Nat := 0xafaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b588a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a29282726262524232221201f1e1d1c1b1ab0191817161514131211100f0e0d0c0bb00a09080706050403020100
def proj (s : PositiveSafetyAuto.State) : PositiveDFA.State :=
  Fin.ofNat 177 ((projectionBytes >>> (8 * s.val)) &&& 255)

theorem proj_start : proj PositiveSafetyAuto.start = PositiveDFA.start := rfl

private theorem zero_ne (s : PositiveSafetyAuto.State) :
    s ≠ PositiveSafetyAuto.start → PositiveSafetyAuto.move s (.bit false) ≠ PositiveSafetyAuto.start := by revert s; decide +kernel

private theorem pos_ne (s : PositiveSafetyAuto.State) : PositiveSafetyAuto.move s (.bit true) ≠ PositiveSafetyAuto.start := by
  revert s; decide +kernel

private theorem mark_ne (s : PositiveSafetyAuto.State) (q : St) : PositiveSafetyAuto.move s (.mark q) ≠ PositiveSafetyAuto.start := by
  cases q <;> revert s <;> decide +kernel

theorem move_ne_start (s : PositiveSafetyAuto.State) (a : Sym) (h : s ≠ PositiveSafetyAuto.start ∨ a ≠ .bit false) :
    PositiveSafetyAuto.move s a ≠ PositiveSafetyAuto.start := by
  cases a with
  | bit b => cases b with
    | false => exact zero_ne s (h.resolve_right (fun f => f rfl))
    | true => exact pos_ne s
  | mark q => exact mark_ne s q

private theorem proj_zero (s : PositiveSafetyAuto.State) :
    s ≠ PositiveSafetyAuto.start → proj (PositiveSafetyAuto.move s (.bit false)) = PositiveDFA.move (proj s) (.bit false) := by
  revert s; decide +kernel

private theorem proj_one (s : PositiveSafetyAuto.State) :
    proj (PositiveSafetyAuto.move s (.bit true)) = PositiveDFA.move (proj s) (.bit true) := by
  revert s; decide +kernel

private theorem proj_mark (s : PositiveSafetyAuto.State) (q : St) :
    proj (PositiveSafetyAuto.move s (.mark q)) = PositiveDFA.move (proj s) (.mark q) := by
  cases q <;> revert s <;> decide +kernel

theorem proj_move (s : PositiveSafetyAuto.State) (a : Sym) (h : s ≠ PositiveSafetyAuto.start ∨ a ≠ .bit false) :
    proj (PositiveSafetyAuto.move s a) = PositiveDFA.move (proj s) a := by
  cases a with
  | bit b => cases b with
    | false => exact proj_zero s (h.resolve_right (fun f => f rfl))
    | true => exact proj_one s
  | mark q => exact proj_mark s q

theorem final_one (s : PositiveSafetyAuto.State) :
    PositiveSafetyAuto.final (PositiveSafetyAuto.move s (.bit true)) = PositiveDFA.final (PositiveDFA.move (proj s) (.bit true)) := by
  revert s; decide +kernel

theorem final_head (s : PositiveSafetyAuto.State) (q : St) (x : Bool) :
    PositiveSafetyAuto.final (PositiveSafetyAuto.move (PositiveSafetyAuto.move s (.mark q)) (.bit x)) =
    PositiveDFA.final (PositiveDFA.move (PositiveDFA.move (proj s) (.mark q)) (.bit x)) := by
  cases q <;> cases x <;> revert s <;> decide +kernel

end PositiveSafetyProjection
