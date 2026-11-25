import Leader.L4.ShortResetForwardH2
import Leader.L4.ShortResetReverseChart
import Leader.L4.Height.ResidualPotential

namespace L4.ShortResetCycle
open AllSizeProtocol MISByteCodec ShortResetFlow ShortResetRow PhysicalCustody
open ShortResetMIS1Ring ShortResetChart ShortResetForwardH2 ShortResetReverseChart
set_option maxRecDepth 8192
set_option maxHeartbeats 1300000

/-- The root source protocol is monitored on exactly the sampled raw tape. -/
def Wait0 {s n : Nat} (x : Raw s n) (r : Fin n) : Prop :=
    get (x r).mis1 81 2 (by decide)=2 ∧ get (x r).mis1 78 3 (by decide)=0

theorem edge_sep {n : Nat} (N : 1<n) (e : Fin n) : e≠rightNeighbor e := by
  intro E
  have H := congrArg Fin.val E.symm
  change (e.val+1)%n=e.val at H
  by_cases B : e.val+1<n
  · rw [Nat.mod_eq_of_lt B] at H
    omega
  · rw [show e.val+1=n by have := e.isLt; omega,Nat.mod_self] at H
    omega

/-- The root keeps WAIT0 on every nonconsuming raw mark. At root arrival,
the premise only excludes the one mark that actually consumes the reply. -/
theorem wait0_step {s n : Nat} (x : Raw s n) (r e : Fin n)
    (sep : e≠rightNeighbor e) (H : header x r=true) (W : Wait0 x r)
    (hold : rightNeighbor e=r →
      oldK true (x r).mis1 0=resetForward ∨ oldK true (x r).mis1 0=T) :
    Wait0 (rawNext s x e) r := by
  by_cases E : r=e
  · subst r
    have K := reset_controller_outgoing_raw x e H
    exact ⟨K.1.trans W.1,K.2.trans W.2⟩
  by_cases D : rightNeighbor e=r
  · obtain ⟨P,Q⟩ := W
    rw [←D] at H P Q ⊢
    exact reset_controller_inbound_hold_raw x e sep H P Q (by simpa only [D] using hold D)
  · unfold Wait0
    rw [reset_remote_frame_raw x e r E (Ne.symm D)]
    exact W

structure Chart {n : Nat} (h : Fin n → Bool) where
  root : Fin n
  a : Nat
  b : Nat
  L : Nat
  positive : 0<L
  length_lt : L<n
  rootPort : lane a b 0=0
  rootHeader : h root=true
  dst : ∀ i, i<L →
    destination (h (rightNeighbor (nextAt root i))) (lane a b i) =
    if i+1<L then some (lane a b (i+1)) else none

def Chart.route {n : Nat} {h : Fin n → Bool} (C : Chart h) : Route h where
  root := C.root
  length := C.L
  positive := C.positive
  port := lane C.a C.b
  rootPort := C.rootPort
  rootHeader := C.rootHeader
  live := fun i K=>by simpa only [if_pos K] using C.dst i (by omega)
  turn := by
    simpa only [if_neg (by have := C.positive; omega : ¬ C.L-1+1<C.L)] using
      C.dst (C.L-1) (by have := C.positive; omega)
  injectiveOn := fun i j hi hj E=>nextAt_injective_under C.root i j
    (Nat.lt_trans hi C.length_lt) (Nat.lt_trans hj C.length_lt) E

theorem Chart.actual_dst {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (heads : ∀ i, header x i=h i) : Dst x C.root C.a C.b C.L := by
  intro i I
  rw [heads]
  exact C.dst i I

theorem chart_exists {s n : Nat} (x : Raw s n) (M : PhysicalCustody.H1.rawMaximal x)
    (r : Fin n) (H : header x r=true) (N : 9<n) :
    ∃ C : Chart (header x), C.root=r ∧ C.L≤9 := by
  obtain ⟨a,b,c,A,B,C,Z,_,L,T,_⟩ := destination_chart M r H N
  have bound : a+b+c≤9 := by omega
  refine ⟨⟨r,a,b,a+b+c,by omega,by omega,Z,H,?_⟩,rfl,bound⟩
  intro i I
  split
  · exact L i (by assumption)
  · have E : i=a+b+c-1 := by omega
    subst i
    exact T

/-- The exact root lane needed to transport WAIT0 in the forward phase. -/
theorem forward_root_safe {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (H : header x C.root=true)
    (i : Nat) (tr : TrailPrefix C.route x i) (F : bits C.route x i=encode resetForward) :
    oldK true (x C.root).mis1 0=resetForward ∨ oldK true (x C.root).mis1 0=MISByteCodec.T := by
  have rootSlot : slot C.route x 0=oldK true (x C.root).mis1 0 := by
    change oldK (header x C.root) (x C.root).mis1 (lane C.a C.b 0)=_
    rw [H,C.rootPort]
  rw [←rootSlot]
  by_cases I : i=0
  · subst i
    exact .inl (slot_of_bits C.route x 0 _ resetForward_decode F)
  · exact .inr (slot_of_bits C.route x 0 _ trail_decode (tr 0 (Nat.pos_of_ne_zero I)))

/-- The exact source issue starts a genuine tracked forward phase and WAIT0. -/
theorem begin_reset {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (D : rightNeighbor e=C.root) (H : header x C.root=true)
    (P : get (x C.root).mis1 81 2 (by decide)=1)
    (Q : get (x C.root).mis1 78 3 (by decide)=0) :
    Wait0 (rawNext s x e) C.root ∧ bits C.route (rawNext s x e) 0=encode resetForward := by
  change _ ∧ (kField (lane C.a C.b 0)).read (rawNext s x e C.root).mis1=_
  rw [C.rootPort]
  rw [←D] at H P Q ⊢
  exact ⟨reset_issue_controller_raw x e sep H P Q, reset_issue_raw x e sep H P Q⟩

/-- An exact terminal forward step is the initial returning prefix. -/
theorem turn_reverse {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (F : TrailPrefix C.route x (C.L-1))
    (R : bits C.route x (C.L-1)=encode resetReply) :
    Rev x C.root C.a C.b C.L (C.L-1) := by
  intro i I
  change bits C.route x i=_
  by_cases X : i<C.L-1
  · simpa [trailAt,X] using F i X
  · have E : i=C.L-1 := by omega
    subst i
    simpa [trailAt] using R

inductive Stage where
  | fwd (k : Nat)
  | rev (k : Nat)
  | done
  deriving DecidableEq

def debt (L : Nat) : Stage → Nat
  | .fwd i => 2*L-i
  | .rev k => k+1
  | .done => 0

def nextStage {n : Nat} {h : Fin n → Bool} (C : Chart h) (e : Fin n) : Stage → Stage
  | .fwd i => if e=nextAt C.root i then
      if i+1<C.L then .fwd (i+1) else .rev i
    else .fwd i
  | .rev 0 => if rightNeighbor e=C.root then .done else .rev 0
  | .rev (k+1) => if e=nextAt C.root k then .rev k else .rev (k+1)
  | .done => .done

def Complete {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n) : Prop :=
  (∀ i, i<C.L → bits C.route x i=encode E) ∧
  get (x C.root).mis1 81 2 (by decide)=1 ∧ get (x C.root).mis1 78 3 (by decide)=1

def Active {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n) : Stage → Prop
  | .fwd i => i<C.L ∧ Wait0 x C.root ∧ TrailPrefix C.route x i ∧
      bits C.route x i=encode resetForward
  | .rev k => k<C.L ∧ Wait0 x C.root ∧ Rev x C.root C.a C.b C.L k
  | .done => Complete C x

private theorem rev_root_safe {s n k : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (H : header x C.root=true) (K : 0<k) (I : k<C.L)
    (R : Rev x C.root C.a C.b C.L k) : oldK true (x C.root).mis1 0=T := by
  have O : bits C.route x 0=encode T := by
    have P := R 0 (by omega)
    change bits C.route x 0=encode (trailAt k 0) at P
    simpa [trailAt,K] using P
  have O' := slot_of_bits C.route x 0 _ trail_decode O
  change oldK (header x C.root) (x C.root).mis1 (lane C.a C.b 0)=T at O'
  simpa only [H,C.rootPort] using O'

/-- Fully assembled same-tape deterministic drain after the authentic
issue: every raw mark preserves the next stage or delivers completion. -/
theorem active_step {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (e : Fin n) (N : 1<n)
    (heads : ∀ j, header x j=h j) (st : Stage) (running : st≠.done)
    (A : Active C x st) :
    Active C (rawNext s x e) (nextStage C e st) := by
  have sep := edge_sep N e
  have he : header x C.root=true := (heads C.root).trans C.rootHeader
  let y := rawNext s x e
  cases st with
  | done => exact False.elim (running rfl)
  | fwd i =>
    obtain ⟨I,W,P,F⟩ := A
    have WW := wait0_step x C.root e sep he W (fun _=>forward_root_safe C x he i P F)
    have X := forward_step C.route x e sep heads W.1 W.2 i I P F
    change TrailPrefix C.route y i ∧ (if e=nextAt C.root i then
      if i+1<C.L then bits C.route y i=encode T ∧ bits C.route y (i+1)=encode resetForward
      else bits C.route y i=encode resetReply else bits C.route y i=encode resetForward) at X
    change Active C y (if e=nextAt C.root i then
      if i+1<C.L then .fwd (i+1) else .rev i else .fwd i)
    by_cases E : e=nextAt C.root i
    · rw [if_pos E]
      have X' : TrailPrefix C.route y i ∧
          (if i+1<C.L then bits C.route y i=encode T ∧
            bits C.route y (i+1)=encode resetForward else bits C.route y i=encode resetReply) := by
        simpa only [E,if_true] using X
      by_cases J : i+1<C.L
      · rw [if_pos J] at X' ⊢
        refine ⟨J,WW,?_,X'.2.2⟩
        intro j Jj
        by_cases V : j=i
        · simpa only [V] using X'.2.1
        · exact X'.1 j (by omega)
      · rw [if_neg J] at X' ⊢
        have B : i=C.L-1 := by omega
        subst i
        exact ⟨I,WW,turn_reverse C y X'.1 X'.2⟩
    · rw [if_neg E]
      have X' : TrailPrefix C.route y i ∧ bits C.route y i=encode resetForward := by
        simpa only [if_neg E] using X
      exact ⟨I,WW,X'.1,X'.2⟩
  | rev k =>
    obtain ⟨I,W,R⟩ := A
    have D := C.actual_dst x heads
    cases k with
    | zero =>
      change Active C y (if rightNeighbor e=C.root then .done else .rev 0)
      by_cases E : rightNeighbor e=C.root
      · rw [if_pos E]
        exact consume R I N C.length_lt C.rootPort E he W.1 W.2
      · rw [if_neg E]
        have WW := wait0_step x C.root e sep he W (fun a=>False.elim (E a))
        exact ⟨I,WW,idle_at_root D R I N E⟩
    | succ k =>
      change Active C y (if e=nextAt C.root k then .rev k else .rev (k+1))
      have WW := wait0_step x C.root e sep he W
        (fun _=>.inr (rev_root_safe C x he (Nat.succ_pos _) I R))
      by_cases E : e=nextAt C.root k
      · rw [if_pos E]
        refine ⟨by omega,WW,?_⟩
        change Rev (rawNext s x e) C.root C.a C.b C.L k
        rw [E]
        exact advance D R I N C.length_lt
      · rw [if_neg E]
        exact ⟨I,WW,idle_before_arrival D R I (Nat.succ_pos _) N C.rootPort he W.1 W.2
          (fun j J=>by
            have eq : j=k := by omega
            rw [eq]
            exact E)⟩

/-- Rank over the actual edge alphabet after a genuine source issue:
every intervening mark is paid, only the nominated mark reduces rank. -/
theorem debt_step {n : Nat} {h : Fin n → Bool} (C : Chart h) (st : Stage)
    (live : match st with | .fwd k | .rev k => k<C.L | .done => False) :
    (∀ e, debt C.L (nextStage C e st) ≤ debt C.L st) ∧
    (∃ e, debt C.L (nextStage C e st)+1 ≤ debt C.L st) := by
  cases st with
  | done => exact False.elim live
  | fwd i =>
    change i<C.L at live
    have win : debt C.L (nextStage C (nextAt C.root i) (.fwd i))+1 ≤ 2*C.L-i := by
      by_cases K : i+1<C.L
      · simp only [nextStage,if_true,if_pos K,debt]; omega
      · simp only [nextStage,if_true,if_neg K,debt]; omega
    constructor
    · intro e
      by_cases J : e=nextAt C.root i
      · subst e
        exact Nat.le_trans (Nat.le_succ _) win
      · simp only [nextStage,if_neg J,Nat.le_refl]
    · exact ⟨nextAt C.root i,win⟩
  | rev k =>
    cases k with
    | zero =>
      constructor
      · intro e
        by_cases J : rightNeighbor e=C.root
        · simp only [nextStage,if_pos J,debt,Nat.zero_le]
        · simp only [nextStage,if_neg J,Nat.le_refl]
      · exact ⟨RearTrace.predecessor C.root,by simp [nextStage,debt,RearTrace.right_predecessor]⟩
    | succ k =>
      constructor
      · intro e
        by_cases J : e=nextAt C.root k
        · simp only [nextStage,if_pos J,debt]; omega
        · simp only [nextStage,if_neg J,Nat.le_refl]
      · exact ⟨nextAt C.root k,by simp [nextStage,debt]⟩

/-- Stops only at the real consumed reply. Prior to that it takes
exactly the same physical mark as the raw process. -/
def monitorNext {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (z : Raw s n × Stage) (e : Fin n) : Raw s n × Stage :=
  if z.2=.done then z else (rawNext s z.1 e,nextStage C e z.2)

private def readyMonitor {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (z : Raw s n × Stage) : Prop :=
  H2Ready z.1 ∧ (∀ j,header z.1 j=h j) ∧ Active C z.1 z.2

private theorem readyMonitor_closed {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (z : Raw s n × Stage) (e : Fin n) (A : readyMonitor C z) :
    readyMonitor C (monitorNext C z e) := by
  by_cases D : z.2=.done
  · simpa only [monitorNext,if_pos D] using A
  · rcases A with ⟨Q,H,B⟩
    simp only [monitorNext,if_neg D]
    refine ⟨h2_ready_closed N z.1 e Q,?_,active_step C z.1 e (by omega) H z.2 D B⟩
    intro j
    exact (PhysicalCustody.H1.raw_h1_selected_frozen N z.1 e j Q.1).trans (H j)

private def potentialData {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) : Height.ResidualPotentialData (S := Raw s n × Stage) (n := n) where
  next := monitorNext C
  Q := readyMonitor C
  P := fun z=>z.2=.done
  inFence := fun _=>False
  Rserial := fun z=>debt C.L z.2
  EF := fun _=>0
  K := n
  hweight := Nat.le_refl _
  closed := readyMonitor_closed C N
  hserial := by
    intro z A D _
    have live : match z.2 with | .fwd k | .rev k => k<C.L | .done => False := by
      have B := A.2.2
      rcases z with ⟨x,st⟩
      cases st with
      | done => exact D rfl
      | fwd k => exact B.1
      | rev k => exact B.1
    exact (by simpa only [monitorNext,if_neg D] using debt_step C z.2 live)
  hfence := fun _ _ _ F=>False.elim F
  otherSerial := fun _ _ _ _ _ _=>Nat.le_refl _
  otherFence := fun _ _ _ _ F=>False.elim F
  entryEscrow := fun _ _ _ _ _ F=>False.elim F
  exitEscrow := fun _ _ _ _ F=>False.elim F
  oneFence := fun _ _ _ _ _ F=>False.elim F

/-- The actual IID mean from a genuine issue cut to physical whole-owner
drain. There is no favorable-word probability or censored scheduler. -/
theorem completed_reset_mean_of_issue {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (x : Raw s n) (e : Fin n) (Q : H2Ready x)
    (heads : ∀ j,header x j=h j) (edge : rightNeighbor e=C.root)
    (issue : get (x C.root).mis1 81 2 (by decide)=1)
    (op : get (x C.root).mis1 78 3 (by decide)=0) :
    Height.IIDExpectedHittingTimeAtMost (rawNext s) (Complete C) (rawNext s x e)
      (2*C.L*n) := by
  let y := rawNext s x e
  let D : Height.ResidualPotentialData (S := Raw s n × Stage) (n := n) := potentialData C N
  have H : header x C.root=true := (heads C.root).trans C.rootHeader
  have issueCut := begin_reset C x e (edge_sep (by omega) e) edge H issue op
  have init : readyMonitor C (y,.fwd 0) := by
    refine ⟨h2_ready_closed N x e Q,?_,C.positive,issueCut.1,
      fun j J=>False.elim (Nat.not_lt_zero j J),issueCut.2⟩
    intro j
    exact (PhysicalCustody.H1.raw_h1_selected_frozen N x e j Q.1).trans (heads j)
  have M := Height.residual_expected_le D (y,.fwd 0) init (2*C.L*n)
    (by change n*(2*C.L-0)+0 ≤ 2*C.L*n; simp [Nat.mul_comm])
  have cmp (t : Nat) (z : Raw s n × Stage) (A : readyMonitor C z) :
      Height.iidHitCost (rawNext s) (Complete C) t z.1 ≤
      Height.iidHitCost D.next D.P t z := by
    induction t generalizing z with
    | zero => exact Nat.le_refl _
    | succ t ih =>
      by_cases K : Complete C z.1
      · rw [Height.iidHitCost_of_target _ _ _ K]
        exact Nat.zero_le _
      · have nd : z.2≠.done := by
          intro eq
          have B := A.2.2
          rw [eq] at B
          exact K B
        have ndD : ¬ D.P z := nd
        simp only [Height.iidHitCost,if_neg K,if_neg ndD]
        apply Nat.add_le_add_left
        apply Height.sum_ofFn_le
        intro f
        have T := ih (monitorNext C z f) (readyMonitor_closed C N z f A)
        have P : (monitorNext C z f).1=rawNext s z.1 f := by
          simp only [monitorNext,if_neg nd]
        rw [P] at T
        exact T
  intro t
  exact Nat.le_trans (cmp t _ init) (M t)

/-- Concrete uniform post-issue bound on every production-size ring.
The returned finite chart is tied to this owner's actual frozen H1
headers, so its clean target is not an existential arbitrary byte view. -/
theorem actual_owner_reset_mean {s n : Nat} (N : 9<n) (x : Raw s n)
    (Q : H2Ready x) (r e : Fin n) (head : header x r=true)
    (edge : rightNeighbor e=r)
    (issue : get (x r).mis1 81 2 (by decide)=1)
    (op : get (x r).mis1 78 3 (by decide)=0) :
    ∃ C : Chart (header x), C.root=r ∧ C.L≤9 ∧
      Height.IIDExpectedHittingTimeAtMost (rawNext s) (Complete C) (rawNext s x e)
        (18*n) := by
  obtain ⟨C,R,L⟩ := chart_exists x Q.1 r head N
  refine ⟨C,R,L,?_⟩
  have A := completed_reset_mean_of_issue C (by omega) x e Q (fun _=>rfl)
    (by simpa only [R] using edge) (by simpa only [R] using issue) (by simpa only [R] using op)
  have K : 2*C.L*n≤18*n := Nat.mul_le_mul_right n (by omega)
  intro t
  exact Nat.le_trans (A t) (Nat.mul_le_mul_right (n^t) K)

end L4.ShortResetCycle
