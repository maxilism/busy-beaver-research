import PositiveSafetyGap

/-! Recognizer for the exceptional successor pattern, with arbitrary blank
padding at either exterior. The missing transitions lead to state 16. -/
namespace PositiveSafetyGapDFA

open Helix

abbrev State := Fin 17
def start : State := 0

def move (s : State) (a : Sym) : State :=
  match s.val, a with
  | 0, .bit false => 0
  | 0, .bit true => 1
  | 1, .bit false => 2
  | 2, .bit false => 3
  | 3, .bit false => 4
  | 4, .bit false => 5
  | 5, .bit false => 3
  | 5, .bit true => 6
  | 6, .bit false => 7
  | 7, .bit true => 8
  | 7, .mark .B => 12
  | 8, .bit false => 9
  | 9, .bit true => 10
  | 10, .bit false => 11
  | 11, .bit true => 6
  | 12, .bit true => 13
  | 13, .bit false => 14
  | 14, .bit true => 15
  | 15, .bit false => 15
  | _, _ => 16

def final (s : State) := s == 15

def accepts (w : List Sym) : Prop := final (w.foldl move start) = true

private abbrev z := Sym.bit false
private abbrev o := Sym.bit true
private def gap (u k : Nat) : List Sym :=
  List.replicate u z ++ [o] ++ List.replicate k z
private def core (u i j : Nat) : List Sym :=
  gap u (4+3*i) ++ [o] ++ (List.replicate (3*j) [z,o]).flatten

private theorem gap_snoc (u k : Nat) : gap u k ++ [z] = gap u (k+1) := by
  simp [gap,List.replicate_succ',List.append_assoc]

private theorem core_snoc (u i j : Nat) :
    core u i j ++ [z,o,z,o,z,o] = core u i (j+1) := by
  rw [core, core, Nat.mul_succ]
  rw [← List.replicate_append_replicate]
  simp only [List.flatten_append]
  simp [List.append_assoc]

/-- The exact shape of the prefix in each live state. -/
private inductive Prefix : State → List Sym → Prop where
  | p0 (u) : Prefix 0 (List.replicate u z)
  | p1 (u) : Prefix 1 (gap u 0)
  | p2 (u) : Prefix 2 (gap u 1)
  | p3 (u i) : Prefix 3 (gap u (2+3*i))
  | p4 (u i) : Prefix 4 (gap u (3+3*i))
  | p5 (u i) : Prefix 5 (gap u (4+3*i))
  | p6 (u i j) : Prefix 6 (core u i j)
  | p7 (u i j) : Prefix 7 (core u i j ++ [z])
  | p8 (u i j) : Prefix 8 (core u i j ++ [z,o])
  | p9 (u i j) : Prefix 9 (core u i j ++ [z,o,z])
  | p10 (u i j) : Prefix 10 (core u i j ++ [z,o,z,o])
  | p11 (u i j) : Prefix 11 (core u i j ++ [z,o,z,o,z])
  | p12 (u i j) : Prefix 12 (core u i j ++ [z,.mark .B])
  | p13 (u i j) : Prefix 13 (core u i j ++ [z,.mark .B,o])
  | p14 (u i j) : Prefix 14 (core u i j ++ [z,.mark .B,o,z])
  | p15 (u i j v) : Prefix 15 (core u i j ++ [z,.mark .B,o,z,o] ++ List.replicate v z)
  | dead (w) : Prefix 16 w

private theorem next {s w} (h : Prefix s w) (a : Sym) : Prefix (move s a) (w ++ [a]) := by
  cases h <;> cases a <;> rename_i d <;> cases d
  all_goals try exact Prefix.dead _
  all_goals try (apply Prefix.p7)
  all_goals try
    simp only [List.append_assoc]
    first
    | apply Prefix.p8
    | apply Prefix.p9
    | apply Prefix.p10
    | apply Prefix.p11
    | apply Prefix.p12
    | apply Prefix.p13
    | apply Prefix.p14
  case p0.bit.false u =>
    change Prefix 0 _
    simpa only [List.replicate_succ', z] using Prefix.p0 (u+1)
  case p0.bit.true u =>
    change Prefix 1 _
    simpa [gap, z, o] using Prefix.p1 u
  case p1.bit.false u =>
    rw [gap_snoc]
    exact Prefix.p2 u
  case p2.bit.false u =>
    rw [gap_snoc]
    exact Prefix.p3 u 0
  case p3.bit.false u i =>
    rw [gap_snoc, show 2+3*i+1=3+3*i by omega]
    exact Prefix.p4 u i
  case p4.bit.false u i =>
    rw [gap_snoc, show 3+3*i+1=4+3*i by omega]
    exact Prefix.p5 u i
  case p5.bit.false u i =>
    rw [gap_snoc, show 4+3*i+1=2+3*(i+1) by omega]
    exact Prefix.p3 u (i+1)
  case p5.bit.true u i =>
    change Prefix 6 _
    simpa [core, z, o] using Prefix.p6 u i 0
  case p11.bit.true u i j =>
    rw [List.append_assoc]
    change Prefix 6 (core u i j ++ [z,o,z,o,z,o])
    rw [core_snoc]
    exact Prefix.p6 u i (j+1)
  case p14.bit.true u i j =>
    change Prefix 15 _
    simpa [z, o, List.append_assoc] using Prefix.p15 u i j 0
  case p15.bit.false u i j v =>
    change Prefix 15 _
    simpa [z, o, List.replicate_succ',List.append_assoc] using Prefix.p15 u i j (v+1)

private theorem run {s : State} {pre : List Sym} (h : Prefix s pre) (w : List Sym) :
    Prefix (w.foldl move s) (pre ++ w) := by
  induction w generalizing s pre with
  | nil => simpa using h
  | cons a w ih => simpa [List.append_assoc] using ih (next h a)

theorem decode {w : List Sym} (h : accepts w) :
    ∃ u i j v : Nat, w = List.replicate u (.bit false) ++ PositiveSafetyGap.gapWord i j ++
      List.replicate v (.bit false) := by
  have p : Prefix (w.foldl move start) w := by simpa [start] using run (Prefix.p0 0) w
  have fin : w.foldl move start = 15 := (beq_iff_eq).mp h
  rw [fin] at p
  cases p with
  | p15 u i j v =>
    refine ⟨u,i,j,v,?_⟩
    simp [core, gap, PositiveSafetyGap.gapWord, List.append_assoc]

end PositiveSafetyGapDFA
