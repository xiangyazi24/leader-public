import Leader.L4.ReportFastFreshReset
import Leader.L4.ReportFastOwnerSupport
import Leader.L4.ReportFastGateRaw
import Leader.L4.ReportFastLeaseSupport
import Leader.L4.ReportGatePairs

namespace L4.ReportFastNominationBridge
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportOwnerCommandRail ReportOwnerSerial
open ReportByteRows ReportFastGateRaw ReportFastOwnerSupport ReportFastNoRearm
open ReportOwnerForwardLocations ReportOwnerForwardControl ReportOwnerReverseShape ReportOwnerReverseControl
open ReportFastLeaseSupport ReportGateGeometry ReportAdaptiveFibre ReportFastKernel
variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop}

def Spent (d : Sheet) (C : Fin 5→Chart h) (x : Raw s n) (q : Fin n) : Prop :=
  ∃ j : Fin 5,∃ side : Bool,
    q=label (center (C j)) (!side) ∧
    healthyAdmit (params d s) (tok d (C j) x ((C j).a+2)) ∧
    (tok d (C j) x ((C j).a+2)).race=(if side then 3 else 2)

def BanSpec (C : Fin 5→Chart h) (active desired : Fin 5→Bool)
    (ban : Fin n→Option (Fin n)) : Prop :=
  ∀ e a,ban e=some a ↔ ∃ j,active j=true ∧
    e=label (center (C j)) (!desired j) ∧
    a=label (center (C j)) (desired j)

def LiveRaces (d : Sheet) (C : Fin 5→Chart h)
    (x : Raw s n) (active : Fin 5→Bool) : Prop :=
  ∀ j,active j=true→healthyAdmit (params d s) (tok d (C j) x ((C j).a+2)) ∧
    (tok d (C j) x ((C j).a+2)).race=1

theorem spent_unblocked (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (C : Fin 5→Chart h)
    (inj : Function.Injective (fun j=>center (C j)))
    (x : Raw s n) (q : Fin n) (active desired : Fin 5→Bool)
    (ban : Fin n→Option (Fin n)) (B : BanSpec C active desired ban)
    (R : LiveRaces d C x active) (S : Spent d C x q) :
    ban q=none := by
  obtain ⟨j,side,E,_,Race⟩ := S
  cases A : ban q with
  | none => rfl
  | some a =>
    obtain ⟨k,K,J,_⟩ := (B q a).mp A
    have D := incidence_disjoint hh G (C j) (C k) (!side) (!desired k)
      (E.symm.trans J)
    have U := inj D.1
    subst k
    have Z := (R j K).2
    cases side <;> simp at Race <;> omega

-- Literal two incident labels of the actual gate.
private theorem blocked_label (C : Chart h) (side : Bool) :
    label (center C) (!side)=(if side then out C (C.a+1) else out C (C.a+2)) := by
  cases side
  · exact (physical_labels C).2.symm
  · exact (physical_labels C).1.symm

private theorem mate_label (C : Chart h) (side : Bool) :
    label (center C) side=(if side then out C (C.a+2) else out C (C.a+1)) := by
  cases side
  · exact (physical_labels C).1.symm
  · exact (physical_labels C).2.symm

-- The actual selected mate is a decision on the old race1, not
-- an arbitrary mark at a neighbour or a new packet arrival.
private theorem front_tag_iff (k i : Nat) : frontTag k i=2 ↔ i=k := by
  unfold frontTag
  by_cases E : i=k
  · subst i; simp
  · by_cases L : i<k <;> simp [E,L]

private theorem back_not_front (k i : Nat) : backTag k i≠2 := by
  unfold backTag
  split <;> try decide
  split <;> decide

private theorem actual_front (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : Serial d C x) (i : Nat) (I : i<C.L)
    (T : (tok d C x i).tag=2) : ForwardWait d C x i := by
  rcases S with A|⟨k,A⟩|⟨k,A⟩
  · have B := A.2.2 i I
    omega
  · have E := (front_tag_iff k i).mp ((A.2.2 i I).symm.trans T)
    exact E ▸ A
  · exact False.elim (back_not_front k i ((A.2.2 i I).symm.trans T))

private theorem gate_predecessor_trail (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : Serial d C x) (i : Nat) (I : i+1<C.L)
    (H : healthyAdmit (params d s) (tok d C x (i+1))) :
    (tok d C x i).tag=1 := by
  have A := actual_front d C x S (i+1) I H.1
  simpa [frontTag,show i<i+1 by omega] using A.2.2 i (by omega)

theorem ban_mate_spends (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d P)
    (C : Fin 5→Chart h) (x : Raw s n) (X : Cached d hh P x)
    (S : ∀ j,StrongSerial d (C j) x)
    (active desired : Fin 5→Bool) (ban : Fin n→Option (Fin n))
    (B : BanSpec C active desired ban) (R : LiveRaces d C x active)
    (q a : Fin n) (E : ban q=some a) :
    Spent d C (rawNext s x a) q := by
  obtain ⟨j,J,Q0,A0⟩ := (B q a).mp E
  let D := C j
  have ⟨H,R1⟩ := R j J
  change (tok d D x (D.a+2)).race=1 at R1
  have GI : D.a+2<D.L := (gate_geometry d D hh G (Q:=P)).2.1
  have Gate : chartGate d D x (D.a+2)=true :=
    ((gate_geometry d D hh G (Q:=P)).2.2 x X (D.a+2) GI).mpr rfl
  refine ⟨j,desired j,Q0,?_⟩
  have L := A0.trans (mate_label D (desired j))
  cases V : desired j
  · have K : a=out D (D.a+1) := by simpa [V] using L
    have T : (tok d D x (D.a+1)).tag≠2 := by
      rw [gate_predecessor_trail d D x (S j).1 (D.a+1) GI H]
      decide
    have U := raw_incoming_decisions d D N hh G F x X (D.a+1) GI Gate T H (.inl R1)
    rw [K,U]
    exact ⟨by simpa [healthyAdmit] using H,by simp [admitRaceAfter,show (tok d D x (D.a+1+1)).race=1 from R1]⟩
  · have K : a=out D (D.a+2) := by simpa [V] using L
    have U := raw_outgoing_decisions d D N hh G F x X (D.a+2) GI Gate H (.inl R1)
    rw [K,U]
    exact ⟨by simpa [healthyAdmit] using H,by simp [admitRaceAfter,R1]⟩

-- All marks except q preserve the very same settled token. In
-- particular a same-side mark of the blocker cannot re-arm it.
theorem spent_step (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d P)
    (C : Fin 5→Chart h) (x : Raw s n) (X : Cached d hh P x)
    (S : ∀ j,StrongSerial d (C j) x)
    (q e : Fin n) (E : e≠q) (A : Spent d C x q) :
    Spent d C (rawNext s x e) q := by
  obtain ⟨j,side,J,H,R⟩ := A
  let D := C j
  have I : D.a+1+1<D.L := (gate_geometry d D hh G (Q:=P)).2.1
  have Gate : chartGate d D x (D.a+2)=true :=
    ((gate_geometry d D hh G (Q:=P)).2.2 x X (D.a+2) I).mpr rfl
  have NE : e≠(if side then out D (D.a+1) else out D (D.a+2)) :=
    fun V=>E (V.trans ((J.trans (blocked_label D side)).symm))
  have T := raw_no_rearm_step d D N hh G F x X (S j).1
    (D.a+1) I Gate H side R e NE
  refine ⟨j,side,J,?_,?_⟩
  · rw [T]; exact H
  · rw [T]; exact R

theorem spent_word (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d P)
    (digit : 0<(params d s).digits)
    (C : Fin 5→Chart h) (x : Raw s n) (X : Cached d hh P x)
    (S : ∀ j,StrongSerial d (C j) x) (q : Fin n)
    (A : Spent d C x q) (v : List (Fin n)) (E : ∀ e∈v,e≠q) :
    Spent d C (rawRun x v) q := by
  induction v generalizing x with
  | nil => exact A
  | cons e v IH =>
    let y := rawNext s x e
    have Y := (cached_fibre d N hh P F).closed x e X
    have V : ∀ j,StrongSerial d (C j) y :=
      fun j=>strong_step d (C j) N hh G F x X (S j) digit e
    exact IH y Y V (spent_step d N hh G F C x X S q e (E e (by simp)) A)
      (fun b B=>E b (by simp [B]))

#print axioms spent_unblocked
#print axioms ban_mate_spends
#print axioms spent_step
#print axioms spent_word

section Bridge
variable {X : Type}

structure Rows (step0 : X→Fin n→X) (Good hit : X→Prop)
    (debt0 : X→Nat) (ban0 : X→Fin n→Option (Fin n))
    (Nom Spent0 : X→Fin n→Prop) : Prop where
  closed : ∀ x e,Good x→Good (step0 x e)
  sticky : ∀ x e,Good x→hit x→hit (step0 x e)
  idle : ∀ x e,Good x→¬hit x→debt0 (step0 x e)≤debt0 x
  exists_nom : ∀ x,Good x→¬hit x→∃ q,Nom x q
  pays : ∀ x q,Good x→¬hit x→Nom x q→debt0 (step0 x q)<debt0 x
  hold : ∀ x q e,Good x→¬hit x→Nom x q→
    debt0 (step0 x e)=debt0 x→Nom (step0 x e) q
  mate : ∀ x q a,Good x→¬hit x→ban0 x q=some a→Spent0 (step0 x a) q
  spent_hold : ∀ x q e,Good x→¬hit x→Spent0 x q→e≠q→Spent0 (step0 x e) q
  free : ∀ x q,Good x→¬hit x→Spent0 x q→ban0 x q=none

structure Track (X : Type) (n : Nat) where
  base : X
  pending : Fin n
  unspent : Bool

noncomputable def chooseNom (Nom : X→Fin n→Prop) (x : X) (fallback : Fin n) : Fin n := by
  classical
  exact if H : ∃ q,Nom x q then Classical.choose H else fallback

theorem chooseNom_spec (Nom : X→Fin n→Prop) (x : X) (q : Fin n)
    (H : ∃ e,Nom x e) : Nom x (chooseNom Nom x q) := by
  classical
  unfold chooseNom
  rw [dif_pos H]
  exact Classical.choose_spec H

noncomputable def start (Nom : X→Fin n→Prop) (x : X) (q : Fin n) : Track X n :=
  ⟨x,chooseNom Nom x q,true⟩

noncomputable def next (step0 : X→Fin n→X) (debt0 : X→Nat)
    (ban0 : X→Fin n→Option (Fin n)) (Nom : X→Fin n→Prop)
    (z : Track X n) (e : Fin n) : Track X n := by
  classical
  let y := step0 z.base e
  exact if debt0 y<debt0 z.base then ⟨y,chooseNom Nom y z.pending,true⟩
    else ⟨y,z.pending,if ban0 z.base z.pending=some e then false else z.unspent⟩

def GoodTrack (Good hit : X→Prop) (Nom Spent0 : X→Fin n→Prop)
    (z : Track X n) : Prop :=
  Good z.base ∧ (¬hit z.base→Nom z.base z.pending ∧
    (z.unspent=false→Spent0 z.base z.pending))

def debt (debt0 : X→Nat) (z : Track X n) : Nat := debt0 z.base
def credit (z : Track X n) : Bool := z.unspent
def ban (ban0 : X→Fin n→Option (Fin n)) (z : Track X n) : Fin n→Option (Fin n) := ban0 z.base
noncomputable def finish (hit : X→Prop) (z : Track X n) : Bool := by
  classical
  exact decide (hit z.base)

theorem live_iff (hit : X→Prop) (z : Track X n) :
    finish hit z≠true ↔ ¬hit z.base := by
  classical
  simp [finish]

theorem next_base (step0 : X→Fin n→X) (debt0 : X→Nat)
    (ban0 : X→Fin n→Option (Fin n)) (Nom : X→Fin n→Prop)
    (z : Track X n) (e : Fin n) :
    (next step0 debt0 ban0 Nom z e).base=step0 z.base e := by
  classical
  unfold next
  dsimp only
  split <;> rfl

theorem start_good (step0 : X→Fin n→X) (Good hit : X→Prop)
    (debt0 : X→Nat) (ban0 : X→Fin n→Option (Fin n))
    (Nom Spent0 : X→Fin n→Prop) (R : Rows step0 Good hit debt0 ban0 Nom Spent0)
    (x : X) (q : Fin n) (H : Good x) :
    GoodTrack Good hit Nom Spent0 (start Nom x q) := by
  refine ⟨H,fun L=>⟨chooseNom_spec Nom x q (R.exists_nom x H L),?_⟩⟩
  intro B
  cases B

theorem track_closed (step0 : X→Fin n→X) (Good hit : X→Prop)
    (debt0 : X→Nat) (ban0 : X→Fin n→Option (Fin n))
    (Nom Spent0 : X→Fin n→Prop) (R : Rows step0 Good hit debt0 ban0 Nom Spent0)
    (z : Track X n) (e : Fin n) (H : GoodTrack Good hit Nom Spent0 z) :
    GoodTrack Good hit Nom Spent0 (next step0 debt0 ban0 Nom z e) := by
  classical
  let y := step0 z.base e
  have Y : Good y := R.closed z.base e H.1
  by_cases D : debt0 y<debt0 z.base
  · change GoodTrack Good hit Nom Spent0
      (if debt0 y<debt0 z.base then ⟨y,chooseNom Nom y z.pending,true⟩
       else ⟨y,z.pending,if ban0 z.base z.pending=some e then false else z.unspent⟩)
    rw [if_pos D]
    refine ⟨Y,fun L=>⟨chooseNom_spec Nom y z.pending (R.exists_nom y Y L),?_⟩⟩
    intro B
    cases B
  · change GoodTrack Good hit Nom Spent0
      (if debt0 y<debt0 z.base then ⟨y,chooseNom Nom y z.pending,true⟩
       else ⟨y,z.pending,if ban0 z.base z.pending=some e then false else z.unspent⟩)
    rw [if_neg D]
    refine ⟨Y,?_⟩
    intro L
    have OLD : ¬hit z.base := fun K=>L (R.sticky z.base e H.1 K)
    obtain ⟨N0,W⟩ := H.2 OLD
    have Eq : debt0 y=debt0 z.base := by
      have I := R.idle z.base e H.1 OLD
      change debt0 y≤debt0 z.base at I
      omega
    refine ⟨R.hold z.base z.pending e H.1 OLD N0 Eq,?_⟩
    by_cases E : ban0 z.base z.pending=some e
    · intro _
      exact R.mate z.base z.pending e H.1 OLD E
    · intro F0
      have B : z.unspent=false := by simpa [E] using F0
      have NE : e≠z.pending := by
        intro K
        subst e
        have V := R.pays z.base z.pending H.1 OLD N0
        exact D V
      exact R.spent_hold z.base z.pending e H.1 OLD (W B) NE

-- The pending physical label cannot change on a plateau. This
-- is stronger than just asserting the existence of a nomination.
theorem retain_pending (step0 : X→Fin n→X) (debt0 : X→Nat)
    (ban0 : X→Fin n→Option (Fin n)) (Nom : X→Fin n→Prop)
    (z : Track X n) (e : Fin n)
    (E : debt0 (step0 z.base e)=debt0 z.base) :
    (next step0 debt0 ban0 Nom z e).pending=z.pending := by
  classical
  simp [next,E]

theorem credit_plateau (step0 : X→Fin n→X) (debt0 : X→Nat)
    (ban0 : X→Fin n→Option (Fin n)) (Nom : X→Fin n→Prop)
    (z : Track X n) (e : Fin n)
    (E : debt0 (step0 z.base e)=debt0 z.base) :
    (next step0 debt0 ban0 Nom z e).unspent=
      (if ban0 z.base z.pending=some e then false else z.unspent) := by
  classical
  simp [next,E]

-- Both requested PhaseRows field statements, with exactly the
-- quantifier and mergeSide convention of the refractory argument.
theorem service_no_rearm_credit (step0 : X→Fin n→X) (Good hit : X→Prop)
    (debt0 : X→Nat) (ban0 : X→Fin n→Option (Fin n))
    (Nom Spent0 : X→Fin n→Prop) :
    let step := next step0 debt0 ban0 Nom
    let Q := GoodTrack Good hit Nom Spent0
    ∀ z e,Q z→finish hit z≠true→
      debt debt0 (step z (mergeSide (ban ban0 z) e))=debt debt0 z→
      (credit (step z (mergeSide (ban ban0 z) e))).toNat≤(credit z).toNat := by
  classical
  dsimp only
  intro z e _ _ E
  let a := mergeSide (ban ban0 z) e
  have Eq : debt0 (step0 z.base a)=debt0 z.base := by
    simpa only [debt,next_base,a] using E
  change (next step0 debt0 ban0 Nom z a).unspent.toNat≤z.unspent.toNat
  rw [credit_plateau step0 debt0 ban0 Nom z a Eq]
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

theorem service_phase_debt (step0 : X→Fin n→X) (Good hit : X→Prop)
    (debt0 : X→Nat) (ban0 : X→Fin n→Option (Fin n))
    (Nom Spent0 : X→Fin n→Prop) (R : Rows step0 Good hit debt0 ban0 Nom Spent0) :
    let step := next step0 debt0 ban0 Nom
    let Q := GoodTrack Good hit Nom Spent0
    ∀ z e,Q z→finish hit z≠true→
      debt debt0 (step z (mergeSide (ban ban0 z) e))≤debt debt0 z := by
  dsimp only
  intro z e H L
  simpa only [debt,next_base] using
    R.idle z.base (mergeSide (ban ban0 z) e) H.1 ((live_iff hit z).mp L)

theorem service_phase_nominate (step0 : X→Fin n→X) (Good hit : X→Prop)
    (debt0 : X→Nat) (ban0 : X→Fin n→Option (Fin n))
    (Nom Spent0 : X→Fin n→Prop) (R : Rows step0 Good hit debt0 ban0 Nom Spent0) :
    let step := next step0 debt0 ban0 Nom
    let Q := GoodTrack Good hit Nom Spent0
    ∀ z,Q z→finish hit z≠true→
      ∃ a e,mergeSide (ban ban0 z) e=a ∧
        (debt debt0 (step z a)<debt debt0 z ∨
         (debt debt0 (step z a)=debt debt0 z ∧
          credit z=true ∧ credit (step z a)=false)) := by
  classical
  dsimp only
  intro z H L
  have OLD := (live_iff hit z).mp L
  obtain ⟨N0,W⟩ := H.2 OLD
  let q := z.pending
  cases E : ban0 z.base q with
  | none =>
    refine ⟨q,q,easy_allowed (ban0 z.base) q E,.inl ?_⟩
    simpa only [debt,next_base,q] using R.pays z.base q H.1 OLD N0
  | some a =>
    have B : z.unspent=true := by
      cases C : z.unspent
      · have F := R.free z.base q H.1 OLD (W C)
        rw [F] at E
        cases E
      · rfl
    refine ⟨a,q,desired_hit (ban0 z.base) q a E,?_⟩
    have I := R.idle z.base a H.1 OLD
    by_cases D : debt0 (step0 z.base a)<debt0 z.base
    · exact .inl (by simpa only [debt,next_base] using D)
    · have Eq : debt0 (step0 z.base a)=debt0 z.base := by omega
      right
      refine ⟨by simpa only [debt,next_base] using Eq,B,?_⟩
      change (next step0 debt0 ban0 Nom z a).unspent=false
      rw [credit_plateau step0 debt0 ban0 Nom z a Eq]
      exact if_pos E

-- Full original-mark property, useful to audit the raw monitor
-- separately from steering. No monotonicity only in probability.
theorem original_rank_idle (step0 : X→Fin n→X) (Good hit : X→Prop)
    (debt0 : X→Nat) (ban0 : X→Fin n→Option (Fin n))
    (Nom Spent0 : X→Fin n→Prop) (R : Rows step0 Good hit debt0 ban0 Nom Spent0)
    (z : Track X n) (e : Fin n) (H : GoodTrack Good hit Nom Spent0 z)
    (L : ¬hit z.base) :
    eventRank (debt debt0 (next step0 debt0 ban0 Nom z e))
      (credit (next step0 debt0 ban0 Nom z e))≤eventRank (debt debt0 z) (credit z) := by
  classical
  apply eventRank_idle
  · simpa only [debt,next_base] using R.idle z.base e H.1 L
  · intro E
    have Eq : debt0 (step0 z.base e)=debt0 z.base := by
      simpa only [debt,next_base] using E
    change (next step0 debt0 ban0 Nom z e).unspent.toNat≤z.unspent.toNat
    rw [credit_plateau step0 debt0 ban0 Nom z e Eq]
    split
    · exact Nat.zero_le _
    · exact Nat.le_refl _

theorem predictable_paying_mark (step0 : X→Fin n→X) (Good hit : X→Prop)
    (debt0 : X→Nat) (ban0 : X→Fin n→Option (Fin n))
    (Nom Spent0 : X→Fin n→Prop) (R : Rows step0 Good hit debt0 ban0 Nom Spent0)
    (z : Track X n) (H : GoodTrack Good hit Nom Spent0 z) (L : ¬hit z.base) :
    ∃ e : Fin n,eventRank
        (debt debt0 (next step0 debt0 ban0 Nom z (mergeSide (ban ban0 z) e)))
        (credit (next step0 debt0 ban0 Nom z (mergeSide (ban ban0 z) e)))<
      eventRank (debt debt0 z) (credit z) := by
  obtain ⟨a,e,E,P⟩ := service_phase_nominate step0 Good hit debt0 ban0 Nom Spent0 R
    z H ((live_iff hit z).mpr L)
  exact ⟨e,by rw [E]; exact eventRank_progress P⟩

-- Exact finite-alphabet lower bound, without adding real arithmetic
-- or presuming independent actual mapped labels.
theorem paying_driver_mass (step0 : X→Fin n→X) (Good hit : X→Prop)
    (debt0 : X→Nat) (ban0 : X→Fin n→Option (Fin n))
    (Nom Spent0 : X→Fin n→Prop) (R : Rows step0 Good hit debt0 ban0 Nom Spent0)
    (z : Track X n) (H : GoodTrack Good hit Nom Spent0 z) (L : ¬hit z.base) :
    1≤(List.ofFn (fun e : Fin n=>
      if eventRank
        (debt debt0 (next step0 debt0 ban0 Nom z (mergeSide (ban ban0 z) e)))
        (credit (next step0 debt0 ban0 Nom z (mergeSide (ban ban0 z) e)))<
        eventRank (debt debt0 z) (credit z) then 1 else 0)).sum := by
  classical
  obtain ⟨q,Q0⟩ := predictable_paying_mark step0 Good hit debt0 ban0 Nom Spent0 R z H L
  let f := fun e : Fin n=>if eventRank
        (debt debt0 (next step0 debt0 ban0 Nom z (mergeSide (ban ban0 z) e)))
        (credit (next step0 debt0 ban0 Nom z (mergeSide (ban ban0 z) e)))<
        eventRank (debt debt0 z) (credit z) then 1 else 0
  have B (e : Fin n) : (if q=e then 1 else 0)≤f e := by
    by_cases E : q=e
    · subst e
      simp [f,Q0]
    · simp [E]
  have V := Height.sum_ofFn_le _ _ B
  rw [sum_delta q (fun _=>1)] at V
  exact V

#print axioms track_closed
#print axioms retain_pending
#print axioms service_no_rearm_credit
#print axioms service_phase_nominate
#print axioms predictable_paying_mark
#print axioms paying_driver_mass
end Bridge

open ReportFastFreshReset

noncomputable def activeRaw (d : Sheet) (C : Fin 5→Chart h)
    (x : Raw s n) (j : Fin 5) : Bool := by
  classical
  exact decide (healthyAdmit (params d s) (tok d (C j) x ((C j).a+2)) ∧
    (tok d (C j) x ((C j).a+2)).race=1)

theorem activeRaw_sound (d : Sheet) (C : Fin 5→Chart h) (x : Raw s n) :
    LiveRaces d C x (activeRaw d C x) := by
  classical
  intro j H
  simpa [activeRaw] using H

noncomputable def makeBan (C : Fin 5→Chart h) (active desired : Fin 5→Bool)
    (e : Fin n) : Option (Fin n) := by
  classical
  exact if H : ∃ j,active j=true ∧ e=label (center (C j)) (!desired j)
    then some (label (center (C (Classical.choose H))) (desired (Classical.choose H)))
    else none

theorem makeBan_spec (hh : ∃ i,h i=true) (G : GapInput h)
    (C : Fin 5→Chart h) (inj : Function.Injective (fun j=>center (C j)))
    (active desired : Fin 5→Bool) : BanSpec C active desired (makeBan C active desired) := by
  classical
  intro e a
  unfold makeBan
  by_cases H : ∃ j,active j=true ∧ e=label (center (C j)) (!desired j)
  · rw [dif_pos H]
    let j := Classical.choose H
    have J := Classical.choose_spec H
    constructor
    · intro E
      exact ⟨j,J.1,J.2,(Option.some.inj E).symm⟩
    · rintro ⟨k,K,L,R⟩
      have E := incidence_disjoint hh G (C j) (C k) (!desired j) (!desired k)
        (J.2.symm.trans L)
      have U := inj E.1
      subst k
      exact congrArg some R.symm
  · rw [dif_neg H]
    constructor
    · intro E
      cases E
    · rintro ⟨j,J,K,_⟩
      exact False.elim (H ⟨j,J,K⟩)

-- Incoming-first denial throughout RESET. "false" is the actual
-- incoming side, by ReportGateGeometry.label, not a grant flag.
def denySides : Fin 5→Bool := fun _=>false

noncomputable def resetBan (d : Sheet) (C : Fin 5→Chart h)
    (hh : ∃ i,h i=true) (z : ReportFastFreshReset.State d hh P) :
    Fin n→Option (Fin n) :=
  makeBan C (activeRaw d C z.1.val) denySides

def ResetGood (d : Sheet) (C : Fin 5→Chart h) (D : Chart h)
    (hh : ∃ i,h i=true) (z : ReportFastFreshReset.State d hh P) : Prop :=
  Inv d D hh z ∧ ∀ j,StrongSerial d (C j) z.1.val

theorem reset_rows (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d P)
    (digit : 0<(params d s).digits)
    (C : Fin 5→Chart h) (inj : Function.Injective (fun j=>center (C j)))
    (D : Chart h) :
    Rows (ReportFastFreshReset.step d D N hh F) (ResetGood d C D hh)
      ReportOwnerReceiptClock.done (freshDebt d D hh)
      (resetBan d C hh) (NomAt d D hh) (fun z q=>Spent d C z.1.val q) := by
  constructor
  · intro z e H
    exact ⟨inv_closed d D N hh G F digit z e H.1,
      fun j=>strong_step d (C j) N hh G F z.1.val z.1.property (H.2 j) digit e⟩
  · intro z e _ H
    exact done_sticky d D N hh F z e H
  · intro z e H _
    exact freshDebt_idle d D N hh G F digit z H.1 e
  · intro z H L
    exact nom_exists d D hh z H.1 L
  · intro z q H _ A
    exact nom_pays d D N hh G F digit z H.1 q A
  · intro z q e H _ A E
    exact nom_plateau d D N hh G F digit z H.1 q e A E
  · intro z q a H _ E
    exact ban_mate_spends d N hh G F C z.1.val z.1.property H.2
      (activeRaw d C z.1.val) denySides (resetBan d C hh z)
      (makeBan_spec hh G C inj _ _) (activeRaw_sound d C z.1.val) q a E
  · intro z q e H _ A E
    exact spent_step d N hh G F C z.1.val z.1.property H.2 q e E A
  · intro z q _ _ A
    exact spent_unblocked d hh G C inj z.1.val q (activeRaw d C z.1.val)
      denySides (resetBan d C hh z) (makeBan_spec hh G C inj _ _)
      (activeRaw_sound d C z.1.val) A

abbrev ResetTrack (d : Sheet) (hh : ∃ i,h i=true) (P : Raw s n→Prop) :=
  Track (ReportFastFreshReset.State d hh P) n

noncomputable def resetNext (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (F : Fibre (h:=h) d P) (C : Fin 5→Chart h) (D : Chart h) :
    ResetTrack d hh P→Fin n→ResetTrack d hh P :=
  next (ReportFastFreshReset.step d D N hh F) (freshDebt d D hh)
    (resetBan d C hh) (NomAt d D hh)

def resetInv (d : Sheet) (C : Fin 5→Chart h) (D : Chart h)
    (hh : ∃ i,h i=true) (z : ResetTrack d hh P) : Prop :=
  GoodTrack (ResetGood d C D hh) ReportOwnerReceiptClock.done
    (NomAt d D hh) (fun z q=>Spent d C z.1.val q) z

theorem resetNext_raw (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (F : Fibre (h:=h) d P) (C : Fin 5→Chart h) (D : Chart h)
    (z : ResetTrack d hh P) (e : Fin n) :
    (resetNext d N hh F C D z e).base.1.val=rawNext s z.base.1.val e := by
  unfold resetNext
  rw [next_base,step_raw]

theorem resetInv_closed (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d P)
    (digit : 0<(params d s).digits)
    (C : Fin 5→Chart h) (inj : Function.Injective (fun j=>center (C j)))
    (D : Chart h) (z : ResetTrack d hh P) (e : Fin n)
    (H : resetInv d C D hh z) : resetInv d C D hh (resetNext d N hh F C D z e) :=
  track_closed _ _ _ _ _ _ _ (reset_rows d N hh G F digit C inj D) z e H

theorem reset_start_good (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d P)
    (digit : 0<(params d s).digits)
    (C : Fin 5→Chart h) (inj : Function.Injective (fun j=>center (C j)))
    (D : Chart h) (x : {x : Raw s n // Cached d hh P x})
    (S : StrongSerial d D x.val) (V : ∀ j,StrongSerial d (C j) x.val) (q : Fin n) :
    resetInv d C D hh (start (NomAt d D hh) (x,none) q) :=
  start_good _ _ _ _ _ _ _ (reset_rows d N hh G F digit C inj D)
    (x,none) q ⟨initial_inv d D hh x S,V⟩

-- Both exact fields, now on the actual RESET observer.
theorem reset_service_no_rearm_credit (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d P)
    (C : Fin 5→Chart h) (D : Chart h) :
    let step := resetNext d N hh F C D
    let debt := debt (freshDebt d D hh)
    let ban := ban (resetBan d C hh)
    let Q := resetInv d C D hh
    let finish := finish ReportOwnerReceiptClock.done
    ∀ z e,Q z→finish z≠true→
      debt (step z (mergeSide (ban z) e))=debt z→
      (credit (step z (mergeSide (ban z) e))).toNat≤(credit z).toNat :=
  service_no_rearm_credit (ReportFastFreshReset.step d D N hh F)
    (ResetGood d C D hh) ReportOwnerReceiptClock.done (freshDebt d D hh)
    (resetBan d C hh) (NomAt d D hh) (fun z q=>Spent d C z.1.val q)

theorem reset_service_phase_nominate (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d P)
    (digit : 0<(params d s).digits)
    (C : Fin 5→Chart h) (inj : Function.Injective (fun j=>center (C j)))
    (D : Chart h) :
    let step := resetNext d N hh F C D
    let debt := debt (freshDebt d D hh)
    let ban := ban (resetBan d C hh)
    let Q := resetInv d C D hh
    let finish := finish ReportOwnerReceiptClock.done
    ∀ z,Q z→finish z≠true→
      ∃ a e,mergeSide (ban z) e=a ∧
        (debt (step z a)<debt z ∨
         (debt (step z a)=debt z ∧ credit z=true ∧ credit (step z a)=false)) :=
  service_phase_nominate _ _ _ _ _ _ _ (reset_rows d N hh G F digit C inj D)

-- Actual adaptive driver mean, as opposed to the ordinary physical
-- mean in FRESHRESET1. The relabeling is applied externally.
theorem reset_driver_mean (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d P)
    (digit : 0<(params d s).digits)
    (C : Fin 5→Chart h) (inj : Function.Injective (fun j=>center (C j)))
    (D : Chart h) (z : ResetTrack d hh P) (H : resetInv d C D hh z) :
    let step := resetNext d N hh F C D
    let steer := fun y=>mergeSide (resetBan d C hh y.base)
    let hit := fun y : ResetTrack d hh P=>ReportOwnerReceiptClock.done y.base
    let rank := fun y=>eventRank (freshDebt d D hh y.base) y.unspent
    Height.IIDExpectedHittingTimeAtMost (driverStep step steer) hit z (n*rank z) := by
  dsimp only
  let step0 := ReportFastFreshReset.step d D N hh F
  let R := reset_rows d N hh G F digit C inj D
  apply ReportAdaptiveFibre.driver_nominated_mean
    (resetNext d N hh F C D) (fun y=>mergeSide (resetBan d C hh y.base))
    (resetInv d C D hh) (fun y=>ReportOwnerReceiptClock.done y.base)
    (fun y=>eventRank (freshDebt d D hh y.base) y.unspent)
  · exact resetInv_closed d N hh G F digit C inj D
  · intro y e Y L
    exact original_rank_idle step0 _ _ _ _ _ _ R y
      (mergeSide (resetBan d C hh y.base) e) Y L
  · intro y Y L
    obtain ⟨a,e,E,P⟩ := reset_service_phase_nominate d N hh G F digit C inj D
      y Y ((live_iff ReportOwnerReceiptClock.done y).mpr L)
    exact ⟨a,e,E,eventRank_progress P⟩
  · exact H

#print axioms makeBan_spec
#print axioms reset_rows
#print axioms resetNext_raw
#print axioms resetInv_closed
#print axioms reset_service_no_rearm_credit
#print axioms reset_service_phase_nominate
#print axioms reset_driver_mean
end L4.ReportFastNominationBridge

namespace L4.ReportFastNominationBridge
open ReportFastFreshReset ReportFastKernel

theorem prep_plateau_iff {t W k a b : Nat} :
    prepDebt t W k a=prepDebt t W k b ↔ a=b := by
  unfold prepDebt
  omega

theorem prep_strict_iff {t W k a b : Nat} :
    prepDebt t W k a<prepDebt t W k b ↔ a<b := by
  unfold prepDebt
  omega

theorem next_phase_strict {t W k r : Nat} (R : r≤resetReserve t W) :
    prepDebt t W k r<prepDebt t W (k+1) 1 := by
  unfold prepDebt
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem final_phase_strict {t W r : Nat} (R : r≤pubReserve t W) :
    r<prepDebt t W 0 1 := by
  unfold prepDebt
  simp only [Nat.zero_mul,Nat.add_zero]
  omega

#print axioms prep_plateau_iff
#print axioms prep_strict_iff
#print axioms next_phase_strict
#print axioms final_phase_strict
end L4.ReportFastNominationBridge

