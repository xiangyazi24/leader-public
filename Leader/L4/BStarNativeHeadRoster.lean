import Leader.L4.BStarCmpReceipt

namespace L4.BStarNativeHeadRoster
open BStarCmpReceipt BStarLongArithmetic BStarLongSignatures
open L4.Compiler.Native

set_option maxRecDepth 4096

/-- The non-alias code families physically visited by the owner. -/
inductive Family
  | load | const | mask | mux | add | sub | shift | cmp | scan
  | neg | both | either | boolMux | phase
  deriving DecidableEq

def family : Code → Option Family
  | .load _ _ => some .load
  | .const _ => some .const
  | .maskB _ => some .mask
  | .mux _ _ _ => some .mux
  | .add _ _ => some .add
  | .sub _ _ => some .sub
  | .shl3 _ => some .shift
  | .cmp _ _ => some .cmp
  | .scan5 _ => some .scan
  | .not _ => some .neg
  | .and _ _ => some .both
  | .or _ _ => some .either
  | .bmux _ _ _ => some .boolMux
  | .phaseEq _ _ => some .phase
  | _ => none

def boolHead (c : Code) : Bool :=
  match family c with
  | some .neg | some .both | some .either | some .boolMux | some .phase => true
  | _ => false

def count (f : Family) : Nat := (literal.filter (fun c => decide (family c=some f))).length

def loadCount (q : Fin 3) : Nat :=
  (literal.filter fun c => match c with
    | .load s _ => s==q
    | _ => false).length

def constCount (v : ConstId) : Nat :=
  (literal.filter fun c => match c with
    | .const c => c==v
    | _ => false).length

/-- The full, non-overlapping literal head census in physical order. -/
theorem counts :
    ([.load,.const,.mask,.mux,.add,.sub,.shift,.cmp,.scan,
      .neg,.both,.either,.boolMux,.phase] : List Family).map count =
    [27,7,20,109,11,6,2,50,1,18,36,11,91,6] := by
  decide +kernel

theorem loads : ([0,1,2] : List (Fin 3)).map loadCount=[9,9,9] := by decide +kernel

theorem constants :
    ([.zero,.one,.p,.bm1,.max,.eight] : List ConstId).map constCount=[1,1,1,1,1,2] := by
  decide +kernel

theorem bool_heads : (literal.filter boolHead).length=162 := by
  decide +kernel

/-- Every physically scheduled compiler opcode has an accepted
nonalias code and a unique head family. -/
theorem dispatch {op : Nat} (lo : 13≤op) (hi : op<408) :
    ∃ i c f, nodeOf op=some i ∧ get i=some c ∧ family c=some f := by
  have L : tourNodes.length=395 := by decide +kernel
  have t : op-13<tourNodes.length := by rw [L]; omega
  let i := tourNodes[op-13]'t
  have T : tourNodes[op-13]?=some i := List.getElem?_eq_getElem t
  have N : nodeOf op=some i := by simpa only [nodeOf,if_neg (Nat.not_lt.mpr lo)] using T
  have M : i∈tourNodes := List.getElem_mem t
  rw [physical_table] at M
  have Ph := (List.mem_filter.mp M).2
  cases C : get i with
  | none => simp [C] at Ph
  | some c =>
    simp only [C,Option.map_some,Option.getD_some] at Ph
    have K : (family c).isSome=true := by
      cases c <;> simp_all [family,physical]
    cases D : family c with
    | none => simp [D] at K
    | some f => exact ⟨i,c,f,N,C,D⟩

end L4.BStarNativeHeadRoster
