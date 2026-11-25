import Helix.Safe
import Helix.Tape

/-! A complete description of the accepted words at which the 176-state
separator can lose acceptance in one step. Each such configuration occurs
three steps after a gap configuration that rejoins the blank orbit. -/
namespace PositiveSafetyGap
open Helix Helix.Obstruction

def gapWord (i j : Nat) : List Sym :=
  ([true] ++ List.replicate (4+3*i) false ++ [true] ++
    (List.replicate (3*j) [false,true]).flatten ++ [false]).map Sym.bit ++
      [.mark .B, .bit true, .bit false, .bit true]

private def gapCfg (i j : Nat) : Cfg :=
  ⟨.B, zo (3*j+1) (left (ext0 [true] (4+3*i))), true, z (o 0)⟩

private theorem gapSafe (i j : Nat) : Safe (gapCfg i j) := by
  let f := ext0 [true] (4+3*i)
  have repair := repairAll (i+1) j
  rw [show 3*(i+1)+1 = 4+3*i by omega,
      show 3*(i+1)+3*j+2 = 3*(i+j+1)+2 by omega] at repair
  have source := safePre repair (edgeSafe (i+j+1))
  have last : Reach (T f (3*j+1)) (gapCfg i j) := by
    apply reach_run 3
    simp [run, step, instruction, T, F, K, gapCfg, f, show top 0 = false from rfl,
      show pop 0 = 0 from rfl]
  exact fun t h => source t (last.trans h)

private theorem left_append (f g : Wd) : left (f++g) = g.foldl (fun n b => push b n) (left f) :=
  List.foldl_append

private theorem zo_left (f : Wd) (n : Nat) :
    zo n (left f) = left (f ++ (List.replicate n [true,false]).flatten) := by
  induction n with
  | zero => simp [zo]
  | succ n ih =>
    rw [List.replicate_succ',List.flatten_append, List.flatten_cons, List.flatten_nil]
    simp only [List.append_nil, ← List.append_assoc]
    rw [left_append (f ++ _)]
    simp only [zo, List.foldl_cons, List.foldl_nil, ih]

private theorem rotatePairs (n : Nat) :
    (List.replicate (n+1) [true,false]).flatten =
    true :: ((List.replicate n [false,true]).flatten ++ [false]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ (n:=n+1), List.flatten_cons]
    rw [ih]
    simp [List.replicate_succ]

private theorem gapDisplay (i j : Nat) : display (gapCfg i j) = gapWord i j := by
  simp only [display,gapCfg,zo_left,ext0]
  rw [show [true] ++ List.replicate (4+3*i) false ++
      (List.replicate (3*j+1) [true,false]).flatten = true ::
      (List.replicate (4+3*i) false ++ (List.replicate (3*j+1) [true,false]).flatten) by rfl,
      cellsLeft, rotatePairs]
  have tail : cells (z (o 0)) = [false,true] := by
    change cells 2 = _
    rw [cells, cells]
    simp [pop,top]
  simp [gapWord,tail,List.append_assoc]

private def decode (l : Nat) : List Sym → Option Cfg
  | .bit b :: xs => decode (push b l) xs
  | .mark q :: .bit x :: xs =>
      let r := xs.foldr (fun s n => match s with | .bit b => push b n | .mark _ => n) 0
      some ⟨q,l,x,r⟩
  | _ => none

private theorem decodeBits (w : Wd) (l : Nat) (s : List Sym) :
    decode l (w.map Sym.bit ++ s) = decode (w.foldl (fun v b => push b v) l) s := by
  induction w generalizing l with
  | nil => rfl
  | cons a w ih => exact ih (push a l)

private theorem decodeDisplay (c : Cfg) : decode 0 (display c) = some c := by
  rcases c with ⟨q,l,x,r⟩
  simp only [display,List.append_assoc,decodeBits,List.cons_append,List.nil_append,decode]
  simp only [List.foldl_reverse, List.foldr_map]
  rw [cellsValue,cellsValue]

theorem displayInjective : Function.Injective display := by
  intro c d eq
  have h := congrArg (decode 0) eq
  rwa [decodeDisplay, decodeDisplay, Option.some.injEq] at h

theorem wordGapSafe {c : Cfg} (i j : Nat) (h : display c = gapWord i j) : Safe c := by
  rw [← gapDisplay i j] at h
  exact displayInjective h ▸ gapSafe i j

end PositiveSafetyGap
