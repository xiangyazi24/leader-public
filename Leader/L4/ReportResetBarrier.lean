import Leader.L4.ReportChartPartition
import Leader.L4.Height.ResidualPotential

namespace L4.ReportResetBarrier
open ShortResetCycle ShortResetChart ReportChartPartition

inductive Letter where
  | empty | trail | forward0 | reply0 | other
  deriving DecidableEq

inductive PC where
  | issue0 | wait0 | issue1 | other
  deriving DecidableEq

abbrev out {n : Nat} {h : Fin n→Bool} (C : Chart h) (j : Nat) := nextAt C.root j
def door {n : Nat} {h : Fin n→Bool} (C : Chart h) := RearTrace.predecessor C.root

/-- Minimal physical row interface. All valuations are decoded canonical
RESET letters; other recognized/malformed commands are left unconstrained
ahead of the F0 frontier. No same-chart stuttering is assumed at a live edge. -/
structure Rows {X : Type} {n : Nat} {h : Fin n→Bool} (C : Chart h)
    (step : X→Fin n→X) (slot : X→Nat→Letter) (pc : X→PC) : Prop where
  issue : ∀ x, pc x=.issue0 →
    pc (step x (door C))=.wait0 ∧ slot (step x (door C)) 0=.forward0
  doorFrame : ∀ x k, 0<k → k<C.L →
    slot (step x (door C)) k=slot x k
  doorHold : ∀ x, pc x=.wait0 → (slot x 0=.trail ∨ slot x 0=.forward0) →
    pc (step x (door C))=.wait0 ∧ slot (step x (door C)) 0=slot x 0
  consume : ∀ x, pc x=.wait0 → slot x 0=.reply0 →
    pc (step x (door C))=.issue1 ∧ slot (step x (door C)) 0=.empty
  noPCElse : ∀ x e, e≠door C → pc (step x e)=pc x
  offFrame : ∀ x e, e≠door C → (∀ j, j<C.L → e≠out C j) →
    ∀ k, k<C.L → slot (step x e) k=slot x k
  linkFrame : ∀ x j, j<C.L → ∀ k, k<C.L → k≠j → k≠j+1 →
    slot (step x (out C j)) k=slot x k
  hop : ∀ x j, j+1<C.L → slot x j=.forward0 →
    slot (step x (out C j)) j=.trail ∧ slot (step x (out C j)) (j+1)=.forward0
  turn : ∀ x j, j+1=C.L → slot x j=.forward0 → slot (step x (out C j)) j=.reply0
  prefixHold : ∀ x j, j+1<C.L → slot x j=.trail →
    (slot x (j+1)=.trail ∨ slot x (j+1)=.forward0) →
    slot (step x (out C j)) j=.trail ∧ slot (step x (out C j)) (j+1)=slot x (j+1)
  backward : ∀ x j, j+1<C.L → slot x j=.trail → slot x (j+1)=.reply0 →
    slot (step x (out C j)) j=.reply0 ∧ slot (step x (out C j)) (j+1)=.empty
  clearedHold : ∀ x j, j+1<C.L → (slot x j=.empty ∨ slot x j=.reply0) → slot x (j+1)=.empty →
    slot (step x (out C j)) j=slot x j ∧ slot (step x (out C j)) (j+1)=.empty
  terminalHold : ∀ x j, j+1=C.L → (slot x j=.empty ∨ slot x j=.reply0) →
    slot (step x (out C j)) j=slot x j

def At {X : Type} {n : Nat} {h : Fin n→Bool} (C : Chart h)
    (slot : X→Nat→Letter) (pc : X→PC) (x : X) : Stage→Prop
  | .fwd i => i<C.L ∧ pc x=.wait0 ∧ slot x i=.forward0 ∧ ∀ k, k<i → slot x k=.trail
  | .rev i => i<C.L ∧ pc x=.wait0 ∧
      (∀ k, k<C.L → slot x k=if k<i then .trail else if k=i then .reply0 else .empty)
  | .done => pc x=.issue1 ∧ ∀ k, k<C.L → slot x k=.empty

private theorem door_iff {n : Nat} {h : Fin n→Bool} (C : Chart h) (e : Fin n) :
    rightNeighbor e=C.root ↔ e=door C := by
  constructor
  · intro H
    simpa only [door,RearTrace.predecessor_right] using congrArg RearTrace.predecessor H
  · rintro rfl
    exact RearTrace.right_predecessor _

theorem issue_at {X : Type} {n : Nat} {h : Fin n→Bool} {C : Chart h}
    {step : X→Fin n→X} {slot pc} (F : Rows C step slot pc) (x : X) (P : pc x=.issue0) :
    At C slot pc (step x (door C)) (.fwd 0) :=
  ⟨C.positive,(F.issue x P).1,(F.issue x P).2,fun k K=>False.elim (Nat.not_lt_zero k K)⟩

theorem active_step {X : Type} {n : Nat} {h : Fin n→Bool} {C : Chart h}
    {step : X→Fin n→X} {slot pc} (F : Rows C step slot pc) (x : X) (e : Fin n)
    (st : Stage) (D : st≠.done) (A : At C slot pc x st) :
    At C slot pc (step x e) (nextStage C e st) := by
  have inj {a b : Nat} (HA : a<C.L) (HB : b<C.L) (E : out C a=out C b) : a=b :=
    nextAt_injective_under C.root _ _ (Nat.lt_trans HA C.length_lt) (Nat.lt_trans HB C.length_lt) E
  have dsep (j : Nat) (J : j<C.L) : door C≠out C j := door_not_outgoing C j J
  by_cases Dr : e=door C
  · subst e
    have back : rightNeighbor (door C)=C.root := (door_iff C _).mpr rfl
    cases st with
    | done => exact (D rfl).elim
    | fwd i =>
      obtain ⟨I,P,T,Pre⟩ := A
      have root : slot x 0=.trail ∨ slot x 0=.forward0 := by
        cases i with
        | zero => exact .inr T
        | succ i => exact .inl (Pre 0 (by omega))
      have W := F.doorHold x P root
      have frame (k : Nat) (K : k<C.L) : slot (step x (door C)) k=slot x k := by
        cases k with
        | zero => exact W.2
        | succ k => exact F.doorFrame x _ (by omega) K
      simp only [nextStage,if_neg (dsep i I)]
      exact ⟨I,W.1,(frame i I).trans T,fun k K=>(frame k (by omega)).trans (Pre k K)⟩
    | rev i =>
      obtain ⟨I,P,All⟩ := A
      cases i with
      | zero =>
        have root : slot x 0=.reply0 := by simpa using All 0 I
        have Q := F.consume x P root
        simp only [nextStage,if_pos back]
        refine ⟨Q.1,fun k K=>?_⟩
        cases k with
        | zero => exact Q.2
        | succ k =>
          rw [F.doorFrame _ _ (by omega) K]
          simpa using All _ K
      | succ i =>
        have root : slot x 0=.trail := by simpa using All 0 (by omega)
        have W := F.doorHold x P (.inl root)
        simp only [nextStage,if_neg (dsep i (by omega))]
        refine ⟨I,W.1,fun k K=>?_⟩
        cases k with
        | zero => exact W.2.trans (All 0 K)
        | succ k => exact (F.doorFrame _ _ (by omega) K).trans (All _ K)
  · have noBack : rightNeighbor e≠C.root := fun H=>Dr ((door_iff C e).mp H)
    have pcEq := F.noPCElse x e Dr
    by_cases E : ∃ j, j<C.L ∧ e=out C j
    · obtain ⟨j,J,rfl⟩ := E
      have frame (k : Nat) (K : k<C.L) (A : k≠j) (B : k≠j+1) :=
        F.linkFrame x j J k K A B
      cases st with
      | done => exact (D rfl).elim
      | fwd i =>
        obtain ⟨I,P,T,Pre⟩ := A
        by_cases H : j=i
        · subst j
          by_cases B : i+1<C.L
          · have Q := F.hop x i B T
            simp only [nextStage,if_pos B]
            refine ⟨B,pcEq.trans P,Q.2,fun k K=>?_⟩
            by_cases V : k=i
            · simpa only [V] using Q.1
            · exact (frame k (by omega) V (by omega)).trans (Pre k (by omega))
          · have Q := F.turn x i (by omega) T
            simp only [nextStage,if_neg B]
            refine ⟨I,pcEq.trans P,fun k K=>?_⟩
            by_cases V : k=i
            · subst k
              simpa only [Nat.lt_irrefl,if_false,if_true] using Q
            · have W : k<i := by omega
              simpa only [if_pos W] using (frame k K V (by omega)).trans (Pre k W)
        · have H' : out C j ≠ out C i := fun Eq=>H (inj J I Eq)
          simp only [nextStage,if_neg H']
          by_cases B : j<i
          · have K : j+1<C.L := by omega
            have R : slot x (j+1)=.trail ∨ slot x (j+1)=.forward0 := by
              by_cases V : j+1=i
              · exact .inr (V.symm ▸ T)
              · exact .inl (Pre _ (by omega))
            have Q := F.prefixHold x j K (Pre j B) R
            have K1 : slot (step x (out C j)) i=.forward0 := by
              by_cases V : i=j+1
              · rw [V,Q.2,←V]; exact T
              · exact (frame i I (Ne.symm H) V).trans T
            refine ⟨I,pcEq.trans P,K1,fun k L=>?_⟩
            by_cases V : k=j
            · simpa only [V] using Q.1
            · by_cases W : k=j+1
              · rw [W,Q.2,←W]; exact Pre k L
              · exact (frame k (by omega) V W).trans (Pre k L)
          · exact ⟨I,pcEq.trans P,(frame i I (Ne.symm H) (by omega)).trans T,
              fun k K=>(frame k (by omega) (by omega) (by omega)).trans (Pre k K)⟩
      | rev i =>
        obtain ⟨I,P,All⟩ := A
        have ltrail (k : Nat) (K : k<i) : slot x k=.trail := by
          simpa only [if_pos K] using All k (by omega)
        have lreply : slot x i=.reply0 := by
          simpa only [Nat.lt_irrefl,if_false,if_true] using All i I
        have lempty (k : Nat) (K : k<C.L) (B : i<k) : slot x k=.empty := by
          simpa only [if_neg (by omega : ¬k<i),if_neg (by omega : k≠i)] using All k K
        by_cases B : j+1=i
        · have I' : j+1<C.L := by omega
          have Q := F.backward x j I' (ltrail j (by omega)) (B.symm ▸ lreply)
          subst i
          simp only [nextStage]
          refine ⟨J,pcEq.trans P,fun k K=>?_⟩
          by_cases V : k=j
          · subst k
            simpa using Q.1
          · by_cases W : k=j+1
            · subst k
              simpa [show ¬j+1<j by omega] using Q.2
            · rw [frame k K V W,All k K]
              by_cases T : k<j
              · simp [T,show k<j+1 by omega]
              · simp [T,show ¬k<j+1 by omega,V,W]
        · have S : nextStage C (out C j) (.rev i)=.rev i := by
            cases i with
            | zero => simp only [nextStage,if_neg noBack]
            | succ k =>
              have H : out C j≠out C k := fun E=>B (congrArg Nat.succ (inj J (by omega) E))
              simp only [nextStage,if_neg H]
          rw [S]
          have aliveLink : ∀ k, k<C.L → slot (step x (out C j)) k=slot x k := by
            have pair : slot (step x (out C j)) j=slot x j ∧
                (j+1<C.L → slot (step x (out C j)) (j+1)=slot x (j+1)) := by
              by_cases K : j+1<C.L
              · by_cases K' : j+1<i
                · have Q := F.prefixHold x j K (ltrail j (by omega)) (.inl (ltrail _ K'))
                  exact ⟨Q.1.trans (ltrail j (by omega)).symm,fun _=>Q.2⟩
                · have V : i<j+1 := by omega
                  have jle : i≤j := by omega
                  have L : slot x j=.empty ∨ slot x j=.reply0 := by
                    by_cases Eq : j=i
                    · exact .inr (Eq.symm ▸ lreply)
                    · exact .inl (lempty j J (by omega))
                  have Q := F.clearedHold x j K L (lempty _ K V)
                  exact ⟨Q.1,fun _=>Q.2.trans (lempty _ K V).symm⟩
              · have L : slot x j=.empty ∨ slot x j=.reply0 := by
                  by_cases Eq : j=i
                  · exact .inr (Eq.symm ▸ lreply)
                  · exact .inl (lempty j J (by omega))
                exact ⟨F.terminalHold x j (by omega) L,fun N=>False.elim (K N)⟩
            intro k K
            by_cases V : k=j
            · simpa only [V] using pair.1
            · by_cases W : k=j+1
              · exact W.symm ▸ pair.2 (by omega)
              · exact frame k K V W
          exact ⟨I,pcEq.trans P,fun k K=>(aliveLink k K).trans (All k K)⟩
    · have frame := F.offFrame x e Dr (fun j J H=>E ⟨j,J,H⟩)
      cases st with
      | done => exact (D rfl).elim
      | fwd i =>
        obtain ⟨I,P,T,Pre⟩ := A
        simp only [nextStage,if_neg (fun H=>E ⟨i,I,H⟩)]
        exact ⟨I,pcEq.trans P,(frame i I).trans T,fun k K=>(frame k (by omega)).trans (Pre k K)⟩
      | rev i =>
        obtain ⟨I,P,All⟩ := A
        cases i with
        | zero => simp only [nextStage,if_neg noBack]; exact ⟨I,pcEq.trans P,fun k K=>(frame k K).trans (All k K)⟩
        | succ k =>
          simp only [nextStage,if_neg (fun H=>E ⟨k,by omega,H⟩)]
          exact ⟨I,pcEq.trans P,fun k K=>(frame k K).trans (All k K)⟩

#print axioms issue_at
#print axioms active_step
end L4.ReportResetBarrier

namespace L4.ReportResetBarrier
open ShortResetCycle

def monitor {X : Type} {n : Nat} {h : Fin n→Bool} (C : Chart h)
    (step : X→Fin n→X) (z : X×Stage) (e : Fin n) : X×Stage :=
  (step z.1 e,nextStage C e z.2)

theorem monitor_raw {X : Type} {n : Nat} {h : Fin n→Bool} (C : Chart h)
    (step : X→Fin n→X) (x : X) (st : Stage) (w : List (Fin n)) :
    (w.foldl (monitor C step) (x,st)).1=w.foldl step x := by
  induction w generalizing x st with
  | nil => rfl
  | cons e w ih => exact ih (step x e) (nextStage C e st)

private theorem done_transition {n : Nat} {h : Fin n→Bool} (C : Chart h) (e : Fin n)
    (st : Stage) (D : st≠.done) (N : nextStage C e st=.done) :
    st=.rev 0 ∧ e=door C := by
  cases st with
  | done => exact (D rfl).elim
  | fwd i =>
    simp only [nextStage] at N
    split at N
    · split at N <;> contradiction
    · contradiction
  | rev i =>
    cases i with
    | zero =>
      simp only [nextStage] at N
      split at N
      · rename_i H
        exact ⟨rfl,(door_iff C e).mp H⟩
      · contradiction
    | succ j =>
      simp only [nextStage] at N
      split at N <;> contradiction

/-- This receipt is a cut on the actual input tape, not a numeric
test for a pre-existing D0 or a fictitious post-completion freeze. -/
theorem receipt_cut {X : Type} {n : Nat} {h : Fin n→Bool} {C : Chart h}
    {step : X→Fin n→X} {slot pc} (F : Rows C step slot pc)
    (w : List (Fin n)) (x : X) (st : Stage) (D : st≠.done)
    (A : At C slot pc x st) (Q : (w.foldl (monitor C step) (x,st)).2=.done) :
    ∃ pre suf : List (Fin n), w=pre++door C::suf ∧
      (pre.foldl (monitor C step) (x,st)).2=.rev 0 ∧
      At C slot pc (pre.foldl step x) (.rev 0) ∧
      At C slot pc (step (pre.foldl step x) (door C)) .done := by
  induction w generalizing x st with
  | nil => exact (D Q).elim
  | cons e w ih =>
    have E := active_step F x e st D A
    by_cases Z : nextStage C e st=.done
    · obtain ⟨S,R⟩ := done_transition C e st D Z
      subst st
      subst e
      rw [Z] at E
      exact ⟨[],w,rfl,rfl,A,E⟩
    · obtain ⟨pre,suf,P,S,U,V⟩ := ih (step x e) (nextStage C e st) Z E Q
      exact ⟨e::pre,suf,congrArg (List.cons e) P,S,U,V⟩

theorem genuine_cut_after_issue {X : Type} {n : Nat} {h : Fin n→Bool} {C : Chart h}
    {step : X→Fin n→X} {slot pc} (F : Rows C step slot pc) (x : X) (O : pc x=.issue0)
    (w : List (Fin n))
    (Q : (w.foldl (monitor C step) (step x (door C),.fwd 0)).2=.done) :
    ∃ pre suf : List (Fin n), w=pre++door C::suf ∧
      At C slot pc ((door C::pre).foldl step x) (.rev 0) ∧
      At C slot pc ((door C::pre++[door C]).foldl step x) .done := by
  obtain ⟨p,q,W,_,A,B⟩ := receipt_cut F w (step x (door C)) (.fwd 0)
    (by decide) (issue_at F x O) Q
  refine ⟨p,q,W,A,?_⟩
  simpa only [List.foldl_cons,List.foldl_append,List.foldl_nil] using B

def Safe {X : Type} {n : Nat} {h : Fin n→Bool} (C : Chart h)
    (slot : X→Nat→Letter) (pc : X→PC) (z : X×Stage) : Prop :=
  z.2≠.done → At C slot pc z.1 z.2

private theorem monitor_closed {X : Type} {n : Nat} {h : Fin n→Bool} {C : Chart h}
    {step : X→Fin n→X} {slot pc} (F : Rows C step slot pc)
    (z : X×Stage) (e : Fin n) (Y : Safe C slot pc z) :
    Safe C slot pc (monitor C step z e) := by
  intro D
  have N : z.2≠.done := by
    intro I
    apply D
    change nextStage C e z.2=.done
    rw [I]
    rfl
  exact active_step F z.1 e z.2 N (Y N)

/-- Original physical-mark IID bound for the authenticated receipt
monitor. This cannot be shortened by hitting a matching arbitrary byte
state prior to the source ISSUE0 mark. -/
theorem completed_mean {X : Type} {n : Nat} {h : Fin n→Bool} {C : Chart h}
    {step : X→Fin n→X} {slot pc} (F : Rows C step slot pc) (x : X) (O : pc x=.issue0) :
    Height.IIDExpectedHittingTimeAtMost (monitor C step) (fun z=>z.2=.done)
      (step x (door C),.fwd 0) (2*C.L*n) := by
  let H : Height.ResidualPotentialData (S := X×Stage) (n := n) :=
    { next := monitor C step
      Q := Safe C slot pc
      P := fun z=>z.2=.done
      inFence := fun _=>False
      Rserial := fun z=>debt C.L z.2
      EF := fun _=>0
      K := n
      hweight := Nat.le_refl _
      closed := monitor_closed F
      hserial := by
        intro z S D _
        have A := S D
        have L : match z.2 with
          | .fwd k | .rev k => k<C.L
          | .done => False := by
          rcases z with ⟨y,st⟩
          cases st with
          | done => exact D rfl
          | fwd k => exact A.1
          | rev k => exact A.1
        exact debt_step C z.2 L
      hfence := fun _ _ _ A=>A.elim
      otherSerial := fun _ _ _ _ _ _=>Nat.le_refl _
      otherFence := fun _ _ _ _ A=>A.elim
      entryEscrow := fun _ _ _ _ _ A=>A.elim
      exitEscrow := fun _ _ _ _ A _=>A.elim
      oneFence := fun _ _ _ _ _ A=>A.elim }
  apply Height.residual_expected_le H
  · intro _
    exact issue_at F x O
  · change n*(2*C.L-0)+0≤2*C.L*n
    simp [Nat.mul_comm]

#print axioms monitor_raw
#print axioms receipt_cut
#print axioms genuine_cut_after_issue
#print axioms completed_mean
end L4.ReportResetBarrier
