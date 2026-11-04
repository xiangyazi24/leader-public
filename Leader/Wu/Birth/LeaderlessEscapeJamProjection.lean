import Leader.Wu.Birth.LeaderlessEscapeRepairs

set_option autoImplicit false
set_option Elab.async false

namespace ZZRepairAllProj

structure KeyFields6 (ψ : Nat) where
  leader : Bool
  label  : Fin ψ
  state  : MainState
  path   : BoundedPathInfo ψ
  probe  : Bool
  wait   : Bool
  deriving DecidableEq, Repr

def proj6 {ψ κ : Nat} (u : BoundedAgentState ψ κ) : KeyFields6 ψ :=
  { leader := u.leader
    label  := u.label
    state  := u.state
    path   := u.path
    probe  := u.probe
    wait   := u.wait }

private def ring2 : DirectedRing 2 := ⟨by decide⟩

private abbrev RawCfg :=
  ZZRepairAll.protocolAll.Configuration 2

def eraseCfg
    (C : Fin 2 → BoundedAgentState 2 2) : RawCfg :=
  fun i => BoundedAgentState.erase (C i)

def hasLeaderBool (C : RawCfg) : Bool :=
  (C (0 : Fin 2)).leader || (C (1 : Fin 2)).leader

/-- Existential scheduler search, prefix-sensitive, with at most fuel steps. -/
def escapesAux : Nat → RawCfg → Bool
  | 0, C => hasLeaderBool C
  | fuel + 1, C =>
      hasLeaderBool C ||
      escapesAux fuel
        (ZZRepairAll.protocolAll.step ring2 C (0 : Fin 2)) ||
      escapesAux fuel
        (ZZRepairAll.protocolAll.step ring2 C (1 : Fin 2))

def escapesBool
    (C : Fin 2 → BoundedAgentState 2 2) : Bool :=
  escapesAux 8 (eraseCfg C)




def jam0 : BoundedAgentState 2 2 :=
  { Q16405.s with
      leader := false
      probe := false
      phase := true
      bit := false
      wait := true
      state := .depart
      label := (0 : Fin 2)
      path := .some (1 : Fin 2) (0 : Fin 2)
      path2 := none
      path3 := none
      path4 := none
      path5 := none }

def jam1 : BoundedAgentState 2 2 :=
  { Q16405.s with
      leader := false
      probe := false
      phase := true
      bit := false
      wait := true
      state := .depart
      label := (1 : Fin 2)
      path := .some (0 : Fin 2) (0 : Fin 2)
      path2 := none
      path3 := none
      path4 := none
      path5 := none }

def jamCfg (i : Fin 2) : BoundedAgentState 2 2 :=
  if i = (0 : Fin 2) then jam0 else jam1

def clean0 : BoundedAgentState 2 2 :=
  { jam0 with
      path5 := some (CleaningLabel.clean, (1 : Fin 2)) }

def clean1 : BoundedAgentState 2 2 :=
  { jam1 with
      path4 := some (CleaningLabel.clean, (1 : Fin 2)) }

def cleanCfg (i : Fin 2) : BoundedAgentState 2 2 :=
  if i = (0 : Fin 2) then clean0 else clean1

theorem same_six_field_projection :
    ∀ i : Fin 2, proj6 (jamCfg i) = proj6 (cleanCfg i) := by
  decide +kernel

theorem jam_does_not_escape :
    escapesBool jamCfg = false := by
  decide +kernel

theorem clean_sentinels_escape :
    escapesBool cleanCfg = true := by
  decide +kernel

theorem six_field_counterexample :
    (∀ i : Fin 2, proj6 (jamCfg i) = proj6 (cleanCfg i)) ∧
      escapesBool jamCfg ≠ escapesBool cleanCfg := by
  exact ⟨same_six_field_projection, by
    rw [jam_does_not_escape, clean_sentinels_escape]
    decide⟩

theorem not_escape_depends_only_on_proj6 :
    ¬ (∀ C C' : Fin 2 → BoundedAgentState 2 2,
        (∀ i, proj6 (C i) = proj6 (C' i)) →
        escapesBool C = escapesBool C') := by
  intro h
  have heq :=
    h jamCfg cleanCfg same_six_field_projection
  exact six_field_counterexample.2 heq

#print axioms ZZRepairAllProj.same_six_field_projection
#print axioms ZZRepairAllProj.jam_does_not_escape
#print axioms ZZRepairAllProj.clean_sentinels_escape
#print axioms ZZRepairAllProj.not_escape_depends_only_on_proj6

end ZZRepairAllProj

#print axioms ZZRepairAllProj.same_six_field_projection
#print axioms ZZRepairAllProj.jam_does_not_escape
#print axioms ZZRepairAllProj.clean_sentinels_escape
#print axioms ZZRepairAllProj.six_field_counterexample
#print axioms ZZRepairAllProj.not_escape_depends_only_on_proj6
