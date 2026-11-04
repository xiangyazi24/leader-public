import Leader.Wu.Entrance.StageRebudget

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceStageLengths

open B6EntranceV2 B6EntranceV2K2
open B6LocalReverseFill
open B6EntranceK2Mass4
open B6EntranceK2BudgetAudit

variable {n psi : Nat}

def envSweepL (psi : Nat) : Nat := envelopeWidth psi - 1
def writerTargetL (psi : Nat) : Nat := envSweepL psi
def trafficTargetL (psi : Nat) : Nat := 2 * envSweepL psi
def expiryTargetL (psi : Nat) : Nat := (16 * psi + 1) * envSweepL psi
def rulerTargetL (psi : Nat) : Nat := (coreWidth psi - 2) * coreWidth psi
def routeTargetL (psi : Nat) : Nat := coreWidth psi - 1

def forwardEnvWord (ring : DirectedRing n) (X : Workspace ring psi) :
    List (Fin n) :=
  B6WriterSilentGuarded.forwardWord ring X.env.I

def reverseWord (ring : DirectedRing n) (I : Interval ring) :
    List (Fin n) :=
  (List.range (I.size - 1)).reverse.map
    (fun k => BirthCheckChainR1Ring.cell ring I.first k)

private theorem internal_append {ring : DirectedRing n} (I : Interval ring)
    {u v : List (Fin n)} (hu : InternalWord I u) (hv : InternalWord I v) :
    InternalWord I (u ++ v) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hu e he
  · exact hv e he

@[simp] theorem reverseWord_length
    (ring : DirectedRing n) (I : Interval ring) :
    (reverseWord ring I).length = I.size - 1 := by
  simp [reverseWord]

theorem reverseWord_internal
    (ring : DirectedRing n) (I : Interval ring) :
    InternalWord I (reverseWord ring I) := by
  intro e he
  rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
  have hk' : k < I.size - 1 := by
    exact List.mem_range.mp (by simpa using hk)
  apply (internal_iff I _).2
  constructor
  · exact support_cell I (by omega)
  · rw [BirthCheckChainR1Ring.right_cell]
    exact support_cell I (by omega)

@[simp] theorem forwardEnvWord_length
    (ring : DirectedRing n) (X : Workspace ring psi) :
    (forwardEnvWord ring X).length = envSweepL psi := by
  unfold forwardEnvWord envSweepL
  rw [B6WriterSilentGuarded.forwardWord_length, X.env.size_eq]

theorem forwardEnvWord_internal
    (ring : DirectedRing n) (X : Workspace ring psi) :
    InternalWord X.env.I (forwardEnvWord ring X) := by
  exact B6WriterSilentGuarded.forwardWord_internal ring X.env.I

def trafficTargetWord (ring : DirectedRing n) (X : Workspace ring psi) :
    List (Fin n) := forwardEnvWord ring X ++ reverseWord ring X.env.I

@[simp] theorem trafficTargetWord_length
    (ring : DirectedRing n) (X : Workspace ring psi) :
    (trafficTargetWord ring X).length = trafficTargetL psi := by
  simp [trafficTargetWord, trafficTargetL, envSweepL, Nat.two_mul,
    X.env.size_eq]

theorem trafficTargetWord_internal
    (ring : DirectedRing n) (X : Workspace ring psi) :
    InternalWord X.env.I (trafficTargetWord ring X) := by
  exact internal_append X.env.I
    (forwardEnvWord_internal ring X) (reverseWord_internal ring X.env.I)

def repeatWord {α : Type} : Nat → List α → List α
  | 0, _ => []
  | k + 1, w => w ++ repeatWord k w

@[simp] theorem repeatWord_length {α : Type} (m : Nat) (w : List α) :
    (repeatWord m w).length = m * w.length := by
  induction m with
  | zero => simp [repeatWord]
  | succ m ih => simp [repeatWord, ih, Nat.succ_mul, Nat.add_comm]

theorem repeatWord_internal {ring : DirectedRing n} (I : Interval ring) (m : Nat)
    (w : List (Fin n)) (hw : InternalWord I w) :
    InternalWord I (repeatWord m w) := by
  induction m with
  | zero => intro e he; simp [repeatWord] at he
  | succ m ih => exact internal_append I hw ih

def expiryTargetWord (ring : DirectedRing n) (X : Workspace ring psi) :
    List (Fin n) := repeatWord (16 * psi + 1) (forwardEnvWord ring X)

@[simp] theorem expiryTargetWord_length
    (ring : DirectedRing n) (X : Workspace ring psi) :
    (expiryTargetWord ring X).length = expiryTargetL psi := by
  simp [expiryTargetWord, expiryTargetL]

theorem expiryTargetWord_internal
    (ring : DirectedRing n) (X : Workspace ring psi) :
    InternalWord X.env.I (expiryTargetWord ring X) := by
  exact repeatWord_internal X.env.I (16 * psi + 1)
    (forwardEnvWord ring X) (forwardEnvWord_internal ring X)

theorem coreInternal_envInternal {ring : DirectedRing n} (X : Workspace ring psi)
    {w : List (Fin n)} (hw : InternalWord X.core.J w) :
    InternalWord X.env.I w := by
  intro e he
  have hc := (internal_iff X.core.J e).1 (hw e he)
  exact (internal_iff X.env.I e).2
    ⟨X.core.subset e hc.1, X.core.subset (ring.rightNeighbor e) hc.2⟩

def routeTargetWord (ring : DirectedRing n) (X : Workspace ring psi) :
    List (Fin n) := reverseWord ring X.core.J

@[simp] theorem routeTargetWord_length
    (ring : DirectedRing n) (X : Workspace ring psi) :
    (routeTargetWord ring X).length = routeTargetL psi := by
  unfold routeTargetWord routeTargetL
  rw [reverseWord_length, X.core.size_eq]

theorem routeTargetWord_internal
    (ring : DirectedRing n) (X : Workspace ring psi) :
    InternalWord X.core.J (routeTargetWord ring X) ∧
      InternalWord X.env.I (routeTargetWord ring X) := by
  have hc := reverseWord_internal ring X.core.J
  exact ⟨hc, coreInternal_envInternal X hc⟩



open B6EntranceV2 B6EntranceV2K2 B6LocalReverseFill
open B6EntranceK2Mass4 B6EntranceK2BudgetAudit

variable {n psi : Nat}

theorem rulerTarget_schedule
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi))) :
    ∃ w : List (Fin n),
      InternalWord X.core.J w ∧ InternalWord X.env.I w ∧
      w.length <= rulerTargetL psi ∧
      B6LocalRuler.RulerSuccess hpsi ring X.core.J
        (runR hpsi h2 ring w C) := by
  have hp : 1 <= psi := by omega
  have hW : 2 <= X.core.J.size := by
    rw [X.core.size_eq]
    unfold coreWidth
    calc
      2 <= 4 * psi := by
        have h := Nat.mul_le_mul_left 4 hp
        omega
      _ <= 4 * psi * psi := Nat.le_mul_of_pos_right _ hp
  obtain ⟨w, hw, hlen, hs⟩ :=
    B6LocalRulerWord.local_ruler_word_sharp
      hpsi h2 ring X.core.J hW C
  refine ⟨w, hw, coreInternal_envInternal X hw, ?_, hs⟩
  rw [X.core.size_eq] at hlen
  simpa [rulerTargetL] using hlen

def stageTargetBudget (n psi : Nat) : EntranceBudgets :=
  rebudget n psi
    (writerTargetL psi) (trafficTargetL psi) (expiryTargetL psi)
    (rulerTargetL psi) (routeTargetL psi)

def stageTargetT (psi : Nat) : Nat :=
  rebudgetTotalL psi
    (writerTargetL psi) (trafficTargetL psi) (expiryTargetL psi)
    (rulerTargetL psi) (routeTargetL psi)

theorem stageTargetBudget_valid (n psi : Nat) :
    (stageTargetBudget n psi).Valid n psi := by
  exact rebudget_valid n psi
    (writerTargetL psi) (trafficTargetL psi) (expiryTargetL psi)
    (rulerTargetL psi) (routeTargetL psi)

@[simp] theorem stageTargetBudget_totalL (n psi : Nat) :
    c4TotalL (stageTargetBudget n psi) = stageTargetT psi := by
  simp [stageTargetBudget, stageTargetT]

def stageTargetCoeff (psi Q2 : Nat) : Nat :=
  rebudgetCoeff psi Q2
    (writerTargetL psi) (trafficTargetL psi) (expiryTargetL psi)
    (rulerTargetL psi) (routeTargetL psi)

@[simp] theorem stageTargetCoeff_eq (n psi Q2 : Nat) :
    c4LeafCoeff psi (stageTargetBudget n psi) Q2 =
      stageTargetCoeff psi Q2 := by
  simp [stageTargetBudget, stageTargetCoeff]

end B6EntranceStageLengths
