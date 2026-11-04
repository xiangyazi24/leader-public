import Leader.Wu.Entrance.StageBudget

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceK2BudgetAudit

open B6EntranceV2 B6EntranceV2K2
open B6EntranceK2Mass4
open B6EntranceK2Budget

variable {n psi : Nat}

@[simp] theorem c4Budget_writerL (n psi : Nat) :
    (c4Budget n psi).writer.L = 0 := rfl
@[simp] theorem c4Budget_trafficL (n psi : Nat) :
    (c4Budget n psi).traffic.L = 0 := rfl
@[simp] theorem c4Budget_expiryL (n psi : Nat) :
    (c4Budget n psi).expiry.L = 0 := rfl
@[simp] theorem c4Budget_k2L (n psi : Nat) :
    (c4Budget n psi).k2.L = k2DrainLength psi := rfl
@[simp] theorem c4Budget_rulerL (n psi : Nat) :
    (c4Budget n psi).ruler.L = 0 := rfl
@[simp] theorem c4Budget_routeL (n psi : Nat) :
    (c4Budget n psi).route.L = 0 := rfl

def auditStageBudget (n L M : Nat) : StageBudget where
  L := L
  M := M
  B := 2 * n * L
  Q := (4 * M) ^ L

theorem auditStageBudget_valid
    (n L M : Nat) (hM : 1 <= M) :
    (auditStageBudget n L M).Valid n := by
  change B6EntranceCompose.EscapeBudget
    n L M (2 * n * L) ((4 * M) ^ L)
  exact ⟨hM, Nat.one_le_pow L (4 * M) (by omega),
    rfl, Nat.le_refl _⟩

def rebudgetPostL
    (psi Lt Le Lr Lroute : Nat) : Nat :=
  (((Lt + Le) + k2DrainLength psi) + Lr) + Lroute

def rebudgetTotalL
    (psi Lw Lt Le Lr Lroute : Nat) : Nat :=
  Lw + rebudgetPostL psi Lt Le Lr Lroute

/-- Exact arithmetic floor once the five semantic word bounds are known. -/
def rebudget
    (n psi Lw Lt Le Lr Lroute : Nat) : EntranceBudgets where
  writer := auditStageBudget n Lw (envelopeTouchBound psi)
  traffic := auditStageBudget n Lt (envelopeTouchBound psi)
  expiry := auditStageBudget n Le (envelopeTouchBound psi)
  k2 := auditStageBudget n (k2DrainLength psi) (envelopeTouchBound psi)
  ruler := auditStageBudget n Lr (envelopeTouchBound psi)
  route := auditStageBudget n Lroute (envelopeTouchBound psi)

@[simp] theorem rebudget_postWriterL
    (n psi Lw Lt Le Lr Lroute : Nat) :
    postWriterL (rebudget n psi Lw Lt Le Lr Lroute) =
      rebudgetPostL psi Lt Le Lr Lroute := rfl

@[simp] theorem rebudget_totalL
    (n psi Lw Lt Le Lr Lroute : Nat) :
    c4TotalL (rebudget n psi Lw Lt Le Lr Lroute) =
      rebudgetTotalL psi Lw Lt Le Lr Lroute := rfl

@[simp] theorem rebudget_postWriterQ
    (n psi Lw Lt Le Lr Lroute : Nat) :
    postWriterQ (rebudget n psi Lw Lt Le Lr Lroute) =
      (4 * envelopeTouchBound psi) ^
        rebudgetPostL psi Lt Le Lr Lroute := by
  simp [rebudget, auditStageBudget, postWriterQ,
    rebudgetPostL, ← Nat.pow_add]

@[simp] theorem rebudget_entranceQ
    (n psi Lw Lt Le Lr Lroute : Nat) :
    entranceQ (rebudget n psi Lw Lt Le Lr Lroute) =
      (4 * envelopeTouchBound psi) ^
        rebudgetTotalL psi Lw Lt Le Lr Lroute := by
  unfold entranceQ
  rw [rebudget_postWriterQ]
  change (4 * envelopeTouchBound psi) ^ Lw *
      (4 * envelopeTouchBound psi) ^
        rebudgetPostL psi Lt Le Lr Lroute = _
  rw [← Nat.pow_add]
  rfl

theorem rebudget_valid
    (n psi Lw Lt Le Lr Lroute : Nat) :
    (rebudget n psi Lw Lt Le Lr Lroute).Valid n psi := by
  have hE := one_le_envelopeTouchBound psi
  unfold EntranceBudgets.Valid
  refine ⟨auditStageBudget_valid n Lw _ hE, ?_,
    auditStageBudget_valid n Lt _ hE,
    auditStageBudget_valid n Le _ hE,
    auditStageBudget_valid n (k2DrainLength psi) _ hE,
    auditStageBudget_valid n Lr _ hE,
    auditStageBudget_valid n Lroute _ hE, ?_, ?_⟩
  · exact Nat.le_refl _
  · rw [rebudget_postWriterQ]
    exact Nat.one_le_pow _ _ (by omega)
  · rw [rebudget_postWriterL, rebudget_postWriterQ]
    exact Nat.le_refl _

def rebudgetCoeff
    (psi Q2 Lw Lt Le Lr Lroute : Nat) : Nat :=
  6 *
    (((4 * envelopeTouchBound psi) ^
      rebudgetTotalL psi Lw Lt Le Lr Lroute) * Q2) *
    (rebudgetTotalL psi Lw Lt Le Lr Lroute + (psi - 1))

@[simp] theorem c4LeafCoeff_rebudget
    (n psi Q2 Lw Lt Le Lr Lroute : Nat) :
    c4LeafCoeff psi (rebudget n psi Lw Lt Le Lr Lroute) Q2 =
      rebudgetCoeff psi Q2 Lw Lt Le Lr Lroute := by
  unfold c4LeafCoeff rebudgetCoeff
  rw [rebudget_entranceQ, rebudget_totalL]

theorem rebudgetCoeff_zero (psi Q2 : Nat) :
    rebudgetCoeff psi Q2 0 0 0 0 0 =
      B6EntranceK2Budget.B6EntranceK2Budget.c4FrozenCoeff psi Q2 := by
  simp [rebudgetCoeff, rebudgetTotalL, rebudgetPostL,
    B6EntranceK2Budget.B6EntranceK2Budget.c4FrozenCoeff]

end B6EntranceK2BudgetAudit
