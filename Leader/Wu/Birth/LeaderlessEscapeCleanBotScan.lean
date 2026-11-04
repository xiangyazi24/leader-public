import Leader.Wu.Birth.LeaderlessEscapeCleanBotRepairs

set_option autoImplicit false
set_option Elab.async false

namespace ZZJamScanB8

open PPLL PPLLRepair
open ZZRepairAll8
open ZZRepairAllProj

private def ring2 : DirectedRing 2 := ⟨by decide⟩

private def prot7 : PopulationProtocol where
  Q := AgentState 2
  Y := LeaderOutput
  transition := ZZRepairAll8.ppllIntegratedRepairAll5 (ψ := 2) (by decide) 2
  output := AgentState.outputFn

private abbrev RawCfg := prot7.Configuration 2

private def hasLeader (C : RawCfg) : Bool :=
  (C (0 : Fin 2)).leader || (C (1 : Fin 2)).leader

private def escapesAux : Nat → RawCfg → Bool
  | 0, C => hasLeader C
  | k + 1, C =>
      hasLeader C ||
      escapesAux k (prot7.step ring2 C (0 : Fin 2)) ||
      escapesAux k (prot7.step ring2 C (1 : Fin 2))

private def labels : List (Fin 2) := [(0 : Fin 2), (1 : Fin 2)]
private def paths : List PathInfo :=
  [PathInfo.bot, PathInfo.some 0 0, PathInfo.some 1 0]
private def path2s : List (Option Path2Info) :=
  [none, some { label := 0, bit := 0, position := 0, action := 0 },
   some { label := 0, bit := 0, position := 0, action := 4 }]
private def path3s : List (Option Path3Info) :=
  [none, some { label := 0, bit := 0, flag := 0 }]
private def paths4 : List (Option (Int × Nat)) := [none, some ((-1 : Int), 1)]
private def paths5 : List (Option (Int × Nat)) := [none, some ((-1 : Int), 1)]

def cells : List (AgentState 2) :=
  labels.flatMap (fun lab =>
    paths.flatMap (fun p =>
      path2s.flatMap (fun p2 =>
        path3s.flatMap (fun p3 =>
          paths4.flatMap (fun p4 =>
            paths5.map (fun p5 =>
              ({ BoundedAgentState.erase Q16405.s with
                  leader := false, state := MainState.depart, wait := true,
                  label := lab, path := p, path2 := p2, path3 := p3,
                  path4 := p4, path5 := p5 } : AgentState 2)))))))

def stuck : List (AgentState 2) :=
  cells.filter (fun u => !(escapesAux 8 (fun _ => u)))

def escaped : List (AgentState 2) :=
  cells.filter (fun u => escapesAux 8 (fun _ => u))

def pathCode (p : PathInfo) : Nat :=
  match p with
  | .bot => 0
  | .some l b => if l = 0 ∧ b = 0 then 1 else if l = 1 ∧ b = 0 then 2 else 3

def p2Code (p : Option Path2Info) : Nat :=
  match p with
  | none => 0
  | some i => if i.action = 0 then 1 else 2

def p3Code (p : Option Path3Info) : Nat :=
  match p with
  | none => 0
  | some _ => 1

def p4Code (p : Option (Int × Nat)) : Nat :=
  match p with
  | none => 0
  | some _ => 1

def code (u : AgentState 2) : Nat :=
  u.label.val * 100000 + pathCode u.path * 10000 + p2Code u.path2 * 1000 +
    p3Code u.path3 * 100 + p4Code u.path4 * 10 + p4Code u.path5


end ZZJamScanB8
