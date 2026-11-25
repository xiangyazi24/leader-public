import Leader.L4.ReportFastNominationBridge
import Leader.L4.ReportFastRawRelift

namespace L4.ReportFastAllowedCredit
open ReportFastNominationBridge ReportAdaptiveFibre ReportFastKernel

variable {X : Type} {n : Nat}

/-- Local credit proofs need the literal progress laws only for labels
in the steering image. The raw observer restarts separately on a banned
ordinary label (ReportFastRawRelift). A nomination may itself be banned. -/
structure Rows (step : X→Fin n→X) (Good hit : X→Prop)
    (rank : X→Nat) (ban : X→Fin n→Option (Fin n))
    (Nom Spent : X→Fin n→Prop) : Prop where
  pairs : ∀ x,Good x→DisjointPairs (ban x)
  closed : ∀ x e,Good x→ban x e=none→Good (step x e)
  sticky : ∀ x e,Good x→ban x e=none→hit x→hit (step x e)
  idle : ∀ x e,Good x→ban x e=none→¬hit x→rank (step x e)≤rank x
  exists_nom : ∀ x,Good x→¬hit x→∃ q,Nom x q
  pays : ∀ x q,Good x→ban x q=none→¬hit x→Nom x q→rank (step x q)<rank x
  hold : ∀ x q e,Good x→ban x e=none→¬hit x→Nom x q→
    rank (step x e)=rank x→Nom (step x e) q
  mate : ∀ x q a,Good x→¬hit x→ban x q=some a→Spent (step x a) q
  spent_hold : ∀ x q e,Good x→ban x e=none→¬hit x→
    Spent x q→e≠q→Spent (step x e) q
  free : ∀ x q,Good x→¬hit x→Spent x q→ban x q=none

theorem start_good (step : X→Fin n→X) (Good hit : X→Prop)
    (rank : X→Nat) (bar : X→Fin n→Option (Fin n))
    (Nom Spent : X→Fin n→Prop) (R : Rows step Good hit rank bar Nom Spent)
    (x : X) (q : Fin n) (H : Good x) :
    GoodTrack Good hit Nom Spent (start Nom x q) := by
  exact ⟨H,fun L=>⟨chooseNom_spec Nom x q (R.exists_nom x H L),fun E=>by cases E⟩⟩

theorem track_step
    (step : X→Fin n→X) (Good hit : X→Prop)
    (rank : X→Nat) (bar : X→Fin n→Option (Fin n))
    (Nom Spent : X→Fin n→Prop) (R : Rows step Good hit rank bar Nom Spent)
    (z : Track X n) (e : Fin n) (H : GoodTrack Good hit Nom Spent z)
    (A : bar z.base e=none) :
    GoodTrack Good hit Nom Spent (next step rank bar Nom z e) := by
  classical
  let y := step z.base e
  have Y : Good y := R.closed z.base e H.1 A
  by_cases D : rank y<rank z.base
  · change GoodTrack Good hit Nom Spent
      (if rank y<rank z.base then ⟨y,chooseNom Nom y z.pending,true⟩
       else ⟨y,z.pending,if bar z.base z.pending=some e then false else z.unspent⟩)
    rw [if_pos D]
    exact ⟨Y,fun L=>⟨chooseNom_spec Nom y z.pending (R.exists_nom y Y L),fun E=>by cases E⟩⟩
  · change GoodTrack Good hit Nom Spent
      (if rank y<rank z.base then ⟨y,chooseNom Nom y z.pending,true⟩
       else ⟨y,z.pending,if bar z.base z.pending=some e then false else z.unspent⟩)
    rw [if_neg D]
    refine ⟨Y,?_⟩
    intro L
    have OLD : ¬hit z.base := fun K=>L (R.sticky z.base e H.1 A K)
    obtain ⟨N0,W⟩ := H.2 OLD
    have Eq : rank y=rank z.base :=
      Nat.le_antisymm (R.idle z.base e H.1 A OLD) (Nat.le_of_not_gt D)
    refine ⟨R.hold z.base z.pending e H.1 A OLD N0 Eq,?_⟩
    by_cases E : bar z.base z.pending=some e
    · intro _
      exact R.mate z.base z.pending e H.1 OLD E
    · intro F0
      have B : z.unspent=false := by simpa [E] using F0
      have NE : e≠z.pending := by
        intro K
        subst e
        exact D (R.pays z.base z.pending H.1 A OLD N0)
      exact R.spent_hold z.base z.pending e H.1 A OLD (W B) NE

theorem driver_rank_idle
    (step : X→Fin n→X) (Good hit : X→Prop)
    (rank : X→Nat) (bar : X→Fin n→Option (Fin n))
    (Nom Spent : X→Fin n→Prop) (R : Rows step Good hit rank bar Nom Spent)
    (z : Track X n) (e : Fin n) (H : GoodTrack Good hit Nom Spent z)
    (L : ¬hit z.base) :
    let a := mergeSide (bar z.base) e
    let y := next step rank bar Nom z a
    eventRank (rank y.base) y.unspent≤eventRank (rank z.base) z.unspent := by
  dsimp only
  let a := mergeSide (bar z.base) e
  apply eventRank_idle
  · rw [next_base]
    exact R.idle z.base a H.1 (ReportFastRawRelift.allowed_after_merge _ (R.pairs _ H.1) e) L
  · intro E
    rw [next_base] at E
    rw [credit_plateau step rank bar Nom z a E]
    split
    · exact Nat.zero_le _
    · exact Nat.le_refl _

theorem driver_rank_nominate
    (step : X→Fin n→X) (Good hit : X→Prop)
    (rank : X→Nat) (bar : X→Fin n→Option (Fin n))
    (Nom Spent : X→Fin n→Prop) (R : Rows step Good hit rank bar Nom Spent)
    (z : Track X n) (H : GoodTrack Good hit Nom Spent z) (L : ¬hit z.base) :
    ∃ a e,mergeSide (bar z.base) e=a ∧
      eventRank (rank (next step rank bar Nom z a).base)
        (next step rank bar Nom z a).unspent<eventRank (rank z.base) z.unspent := by
  classical
  obtain ⟨N0,W⟩ := H.2 L
  let q := z.pending
  cases E : bar z.base q with
  | none =>
    refine ⟨q,q,easy_allowed _ q E,?_⟩
    apply eventRank_progress
    left
    rw [next_base]
    exact R.pays z.base q H.1 E L N0
  | some a =>
    refine ⟨a,q,desired_hit _ q a E,?_⟩
    have A := (R.pairs z.base H.1).allowed_target q a E
    have I := R.idle z.base a H.1 A L
    by_cases K : rank (step z.base a)<rank z.base
    · apply eventRank_progress
      left
      simpa only [next_base] using K
    · have Eq : rank (step z.base a)=rank z.base := by omega
      have C : z.unspent=true := by
        cases F : z.unspent
        · have G := R.free z.base q H.1 L (W F)
          rw [E] at G
          contradiction
        · rfl
      apply eventRank_progress
      right
      refine ⟨by simpa only [next_base] using Eq,C,?_⟩
      rw [credit_plateau step rank bar Nom z a Eq]
      exact if_pos E

#print axioms start_good
#print axioms track_step
#print axioms driver_rank_idle
#print axioms driver_rank_nominate

end L4.ReportFastAllowedCredit
