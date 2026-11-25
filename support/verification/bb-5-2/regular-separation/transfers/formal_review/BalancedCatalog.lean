import BalancedMachine

/-! The twelve literal catalog tables. The comparison below checks every named entry
(including the halt) against the six normalized step functions, and transports
arbitrary computations. Reflection keeps the scanned bit fixed and exchanges the
two tape halves strictly outside the head. -/
namespace BalancedCatalog
open BalancedTM

def machineId (v : Variant) (dRoot : Bool) : Nat :=
  match v, dRoot with
  | .m8210683, false => 8210683  | .m8210683, true => 321080
  | .m8210684, false => 8210684  | .m8210684, true => 523280
  | .m8210685, false => 8210685  | .m8210685, true => 472097
  | .m8226493, false => 8226493  | .m8226493, true => 572659
  | .m10818491, false => 10818491 | .m10818491, true => 320969
  | .m10818510, false => 10818510 | .m10818510, true => 1465912

def code (v : Variant) (dRoot : Bool) : String :=
  match v, dRoot with
  | .m8210683, false  => "1RB1RA_1LC1LB_0RD0LC_1RE---_0RA1RA"
  | .m8210683, true   => "1RB---_0RC1RC_1RD1RC_1LE1LD_0RA0LE"
  | .m8210684, false  => "1RB1RA_1LC1LB_0RD0LC_1RE---_0RA1LA"
  | .m8210684, true   => "1RB---_0RC1LC_1RD1RC_1LE1LD_0RA0LE"
  | .m8210685, false  => "1RB1RA_1LC1LB_0RD0LC_1RE---_0RA1LE"
  | .m8210685, true   => "1RB---_0RC1LB_1RD1RC_1LE1LD_0RA0LE"
  | .m8226493, false  => "1RB1RA_1LC1LE_0RD0LC_1RE---_0RA1LB"
  | .m8226493, true   => "1RB---_0RC1LD_1RD1RC_1LE1LB_0RA0LE"
  | .m10818491, false => "1RB1RE_1LC1LB_0RD0LC_1RE---_0RA1RA"
  | .m10818491, true  => "1RB---_0RC1RC_1RD1RB_1LE1LD_0RA0LE"
  | .m10818510, false => "1RB1RE_1LC1LB_0RD0LC_1LE---_0RA1RA"
  | .m10818510, true  => "1RB---_0LC1LC_1LD1LB_1RE1RD_0LA0RE"

private def stateNo : St → Nat
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4

private def stateOf : Char → Option St
  | 'A' => some .A | 'B' => some .B | 'C' => some .C
  | 'D' => some .D | 'E' => some .E | _ => none

private def parseAction : List Char → Action
  | [w,d,q] => do
    let bit ← if w == '1' then some true else if w == '0' then some false else none
    let dir ← if d == 'L' then some Dir.L else if d == 'R' then some Dir.R else none
    return (bit, dir, ← stateOf q)
  | _ => none

def catalogInstruction (v : Variant) (dRoot : Bool) (q : St) (b : Bool) : Action :=
  let offset := 7 * stateNo q + 3 * b.toNat
  parseAction (((code v dRoot).toList.drop offset).take 3)

private def printAction : Action → String
  | none => "---"
  | some (b,d,q) => String.ofList [
      if b then '1' else '0', if d == .L then 'L' else 'R',
      match q with | .A => 'A' | .B => 'B' | .C => 'C' | .D => 'D' | .E => 'E' ]

private def printTable (m : St → Bool → Action) : String :=
  String.intercalate "_" ([St.A,.B,.C,.D,.E].map fun q => printAction (m q false) ++ printAction (m q true))

/-- An invalid triple or misplaced separator could not round-trip unchanged. -/
theorem catalog_roundtrip (v : Variant) (dRoot : Bool) :
    printTable (catalogInstruction v dRoot) = code v dRoot := by
  cases v <;> cases dRoot <;> decide

def rename (_ : Variant) (dRoot : Bool) (q : St) : St :=
  if dRoot then
    match q with | .A => .C | .B => .D | .C => .E | .D => .A | .E => .B
  else q

def mirror (v : Variant) (dRoot : Bool) : Bool := dRoot && (v == .m10818510)

private def mapDir (reflected : Bool) (d : Dir) : Dir :=
  if reflected then (match d with | .L => .R | .R => .L) else d

def image (v : Variant) (dRoot : Bool) (c : Cfg) : Cfg :=
  if mirror v dRoot then
    F (rename v dRoot c.q) (pop c.r) (push (top c.r) c.l)
  else
    F (rename v dRoot c.q) c.l c.r

private theorem instruction_image (v : Variant) (dRoot : Bool) (q : St) (b : Bool) :
    catalogInstruction v dRoot (rename v dRoot q) b =
      (instruction v q b).map (fun (w,d,p) => (w, mapDir (mirror v dRoot) d, rename v dRoot p)) := by
  cases v <;> cases dRoot <;> cases q <;> cases b <;> decide

abbrev catalogStep (v : Variant) (dRoot : Bool) := machineStep (catalogInstruction v dRoot)

theorem step_image (v : Variant) (dRoot : Bool) (c : Cfg) :
    catalogStep v dRoot (image v dRoot c) = (step v c).map (image v dRoot) := by
  rcases c with ⟨q,l,r⟩
  cases h : mirror v dRoot <;> simp only [catalogStep,step,machineStep,image,h, F,
        Bool.false_eq_true,ite_false,ite_true,top_push,pop_push,instruction_image]
  all_goals
    cases instruction v q (top r) with
    | none => rfl
    | some entry =>
      rcases entry with ⟨w,d,p⟩
      cases d <;> simp [mapDir,image,h,K,F]

theorem mapReach (v : Variant) (dRoot : Bool) {c t : Cfg} (path : Path v c t) :
    Walk (catalogStep v dRoot) (image v dRoot c) (image v dRoot t) := by
  induction path with
  | nil => exact .nil _
  | tick h _ ih =>
    exact .tick (by rw [step_image, h]; rfl) ih

theorem mapHalt (v : Variant) (dRoot : Bool) {c : Cfg} (h : step v c = none) :
    catalogStep v dRoot (image v dRoot c) = none := by rw [step_image,h]; rfl

@[simp] theorem image_blank (v : Variant) (dRoot : Bool) :
    image v dRoot (blank (if dRoot then St.D else St.A)) = blank .A := by
  cases v <;> cases dRoot <;> rfl

end BalancedCatalog
