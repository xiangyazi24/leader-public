import Leader.Wu.Entrance.CoreHostLaws
import Leader.Wu.Birth.ShortWait

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6K2WaitSeeds

open B6EntranceV2

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide

/-- The literal width-two R1 row at the B6 parameters. -/
def r1Host3 : B9Host.HostRow (Phys 3 3 48) :=
  B9Host.r1Host (kappa := 3) (tau := 48) h3 h23

/-- The deliberately too-weak local WAIT condition. -/
def LocalWaitDormant {psi kappa tau : Nat}
    (q : Phys psi kappa tau) : Prop :=
  let u := B6Sanitation.rawCell q
  u.wait = true ∧ u.count < kappa

/-- Exactly the source cleanliness relevant here: follower, reset/echo clear,
comparison clean, and empty stationary-writer payload. -/
def SourceCleanCell {psi kappa tau : Nat}
    (q : Phys psi kappa tau) : Prop :=
  let u := B6Sanitation.rawCell q
  u.leader = false ∧
    ResetEchoClearCell q ∧
    ComparisonCleanCell q ∧
    B6WriterSilence.EmptyWriter u

/-- Stall one is intentional: the same R1 service may create `.produce`, and
endpoint expiry then decrements the old positive stall instead of erasing that
fresh comparison state. -/
private def mkSeedCell
    (label : Fin 3) (count : Fin 4)
    (wait hField carry : Bool) : Phys 3 3 48 :=
  let b : BoundedAgentState 3 3 := {
    leader := false
    probe := false
    phase := false
    bit := false
    wait := wait
    state := .none
    path := .bot
    reset := false
    carry := carry
    count := count
    label := label
    h_field := hField
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := 0
    bullet := 0
    shield := false
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false
  }
  ⟨⟨b, false⟩, 1⟩

/-! ## Seed (a): already at the width-two WAIT cap -/

def capLeft : Phys 3 3 48 :=
  mkSeedCell (0 : Fin 3) (0 : Fin 4) true false false

def capRight : Phys 3 3 48 :=
  mkSeedCell (1 : Fin 3) (3 : Fin 4) true false false

def capAfter : Phys 3 3 48 × Phys 3 3 48 :=
  r1Host3.row capLeft capRight

private theorem mkSeedCell_source_clean
    (label : Fin 3) (count : Fin 4)
    (wait hField carry : Bool) :
    SourceCleanCell (mkSeedCell label count wait hField carry) := by
  unfold SourceCleanCell
  dsimp only
  refine ⟨rfl, ?_, ?_, ?_⟩
  · unfold ResetEchoClearCell B6Sanitation.rawCell mkSeedCell
    exact ⟨rfl, rfl⟩
  · unfold ComparisonCleanCell B6Sanitation.rawCell mkSeedCell
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rfl

private theorem mkSeedCell_localWaitDormant
    (label : Fin 3) (count : Fin 4)
    (hField carry : Bool) (hcount : count.val < 3) :
    LocalWaitDormant (mkSeedCell label count true hField carry) := by
  unfold LocalWaitDormant B6Sanitation.rawCell mkSeedCell
  exact ⟨rfl, hcount⟩

theorem capSeed_clean :
    SourceCleanCell capLeft ∧ SourceCleanCell capRight := by
  exact ⟨
    mkSeedCell_source_clean (0 : Fin 3) (0 : Fin 4) true false false,
    mkSeedCell_source_clean (1 : Fin 3) (3 : Fin 4) true false false⟩


theorem capSeed_fields :
    (B6Sanitation.rawCell capLeft).label = (0 : Fin 3) ∧
    (B6Sanitation.rawCell capLeft).wait = true ∧
    (B6Sanitation.rawCell capLeft).path = .bot ∧
    (B6Sanitation.rawCell capRight).label = (1 : Fin 3) ∧
    (B6Sanitation.rawCell capRight).wait = true ∧
    (B6Sanitation.rawCell capRight).count = 3 ∧
    (B6Sanitation.rawCell capRight).path = .bot := by
  decide +kernel

/- Width-two WAIT sees the responder already at cap, releases/moves WAIT,
and the same R1 row starts GEN.  This is deliberately a field projection of
the completed physical row. -/
theorem capAfter_produce :
    (B6Sanitation.rawCell capAfter.2).state = .produce := by
  decide +kernel

/-! ## Seed (b): locally dormant, but one carry reaches the cap -/

def carryLeft : Phys 3 3 48 :=
  mkSeedCell (0 : Fin 3) (0 : Fin 4) true false true

def carryRight : Phys 3 3 48 :=
  mkSeedCell (1 : Fin 3) (2 : Fin 4) true true false

def carryAfter : Phys 3 3 48 × Phys 3 3 48 :=
  r1Host3.row carryLeft carryRight

theorem carrySeed_clean_dormant :
    SourceCleanCell carryLeft ∧ SourceCleanCell carryRight ∧
    LocalWaitDormant carryLeft ∧ LocalWaitDormant carryRight := by
  exact ⟨
    mkSeedCell_source_clean (0 : Fin 3) (0 : Fin 4) true false true,
    mkSeedCell_source_clean (1 : Fin 3) (2 : Fin 4) true true false,
    mkSeedCell_localWaitDormant
      (0 : Fin 3) (0 : Fin 4) false true (by decide),
    mkSeedCell_localWaitDormant
      (1 : Fin 3) (2 : Fin 4) true false (by decide)⟩


theorem carrySeed_fields :
    (B6Sanitation.rawCell carryLeft).label = (0 : Fin 3) ∧
    (B6Sanitation.rawCell carryLeft).wait = true ∧
    (B6Sanitation.rawCell carryLeft).carry = true ∧
    (B6Sanitation.rawCell carryRight).label = (1 : Fin 3) ∧
    (B6Sanitation.rawCell carryRight).wait = true ∧
    (B6Sanitation.rawCell carryRight).count = 2 ∧
    (B6Sanitation.rawCell carryRight).h_field = true := by
  decide +kernel

/- The carry/h-field handshake advances the width-two terminal count 2 -> 3;
WAIT then releases in that same call and GEN starts in the same R1 row. -/
theorem carryAfter_produce :
    (B6Sanitation.rawCell carryAfter.2).state = .produce := by
  decide +kernel

private theorem comparisonClean_not_of_produce
    {psi kappa tau : Nat} (q : Phys psi kappa tau)
    (hp : (B6Sanitation.rawCell q).state = .produce) :
    ¬ ComparisonCleanCell q := by
  intro hc
  unfold ComparisonCleanCell at hc
  dsimp only at hc
  have hn : (B6Sanitation.rawCell q).state = .none := hc.1
  have hbad : MainState.produce = MainState.none := hp.symm.trans hn
  exact (by decide : MainState.produce ≠ MainState.none) hbad

theorem capSeed_not_clean_after_one_service :
    SourceCleanCell capLeft ∧ SourceCleanCell capRight ∧
    ¬ ComparisonCleanCell capAfter.2 := by
  exact ⟨capSeed_clean.1, capSeed_clean.2,
    comparisonClean_not_of_produce capAfter.2 capAfter_produce⟩

/-- `wait = true ∧ count < kappa` is not enough even on both endpoints:
the source pair is otherwise clean, but its live carry/h-field can reach the
cap, release WAIT, and re-arm GEN before the row finishes. -/
theorem localWaitDormant_not_enough :
    SourceCleanCell carryLeft ∧ SourceCleanCell carryRight ∧
    LocalWaitDormant carryLeft ∧ LocalWaitDormant carryRight ∧
    ¬ ComparisonCleanCell carryAfter.2 := by
  refine ⟨carrySeed_clean_dormant.1,
    carrySeed_clean_dormant.2.1,
    carrySeed_clean_dormant.2.2.1,
    carrySeed_clean_dormant.2.2.2, ?_⟩
  exact comparisonClean_not_of_produce carryAfter.2 carryAfter_produce

end B6K2WaitSeeds
