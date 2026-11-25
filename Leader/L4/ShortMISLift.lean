import Leader.L4.ShortMIS2Entrance
import Leader.L4.ShortMIS2Cap
import Leader.L4.ShortMISEngine
import Leader.L4.ShortMISStageBudget
import Leader.L4.ShortH2RawEntrance
import Leader.L4.ShortPrefixRenewal
import Leader.L4.ShortPrefixRawService
import Leader.L4.ShortFiveParkedParam
import Leader.L4.ShortFiveWinningWord
import Leader.L4.ShortAllOwnerClock
import Leader.L4.ShortLatestResetMonitor

namespace L4.ShortMISLift
open AllSizeProtocol PhysicalCustody PhysicalShortSheet
open ShortMISEngine ShortResetChart ShortResetCycle ShortLayerGeometry
open ShortHopSpacing ShortResetWatch
open ReportStaticSpacing
open ShortFiveWatchReplay (labels Covered Internal included keep)
open ShortFiveWinningWord (winningWord winning_length winning_watch)
open ShortH2RawEntrance (PermanentH2 permanent_h2_closed)
open CustodyMonitorTargets (RawMaximal)
open ShortControllerEntrance (pc)

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {s n : Nat}

private theorem run_append (x : Raw s n) (u v : List (Fin n)) :
    rawRun x (u++v)=rawRun (rawRun x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (rawNext s x e)

private theorem run_clock (x : Raw s n) (w : List (Fin n)) :
    SequentialMarkClock.run (rawNext s) x w=rawRun x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (rawNext s x e)

private theorem clock_height {X : Type} (f : X→Fin n→X)
    (x : X) (w : List (Fin n)) :
    SequentialMarkClock.run f x w=Height.runWord f x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (f x e)

private theorem cache_run (P : Params s n) (x : Raw s n)
    (X : Cached P x) (w : List (Fin n)) : Cached P (rawRun x w) := by
  induction w generalizing x with
  | nil => exact X
  | cons e w ih => exact ih _ (P.cached_closed x e X)

-- Strong physical lower geometry, not a compressed scheduler.
structure Geometry (s n : Nat) where
  P : Params s n
  A : Nat
  gaps : GapBounds P.h A P.B
  seven : 7*P.B<n

def Geometry.D (G : Geometry s n) : Nat := 3*G.P.B

def Geometry.ring (G : Geometry s n) : ShortNORCover.Ring (Lower G.P.h) :=
  SelectedRingGeometry.ring G.gaps G.P.hh (by have := G.seven; omega)

def Geometry.width (G : Geometry s n) (i : Lower G.P.h) : Nat :=
  successorWidth G.gaps i.val

theorem Geometry.width_spec (G : Geometry s n) (i : Lower G.P.h) :
    G.A≤G.width i ∧ G.width i≤G.P.B ∧ Gap G.P.h i.val (G.width i) :=
  successorWidth_spec G.gaps i.val i.property

def Geometry.rootAt (G : Geometry s n) (i : Lower G.P.h) :
    Nat → Lower G.P.h
  | 0 => i
  | k+1 => G.ring.right (G.rootAt i k)

def Geometry.coord (G : Geometry s n) (i : Lower G.P.h) : Nat → Nat
  | 0 => 0
  | k+1 => G.coord i k+G.width (G.rootAt i k)

theorem Geometry.coord_bound (G : Geometry s n) (i : Lower G.P.h)
    (k : Nat) : G.coord i k≤G.P.B*k := by
  induction k with
  | zero => simp [Geometry.coord]
  | succ k ih =>
    have H := (G.width_spec (G.rootAt i k)).2.1
    simp only [Geometry.coord,Nat.mul_succ]
    omega

theorem Geometry.coord_succ (G : Geometry s n) (i : Lower G.P.h)
    (k : Nat) : G.coord i k<G.coord i (k+1) := by
  have H := (G.width_spec (G.rootAt i k)).2.2.positive
  simp only [Geometry.coord]
  omega

theorem Geometry.coord_lt (G : Geometry s n) (i : Lower G.P.h)
    {a b : Nat} (H : a<b) : G.coord i a<G.coord i b := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases E : a=b
    · subst a
      exact G.coord_succ i b
    · exact Nat.lt_trans (ih (by omega)) (G.coord_succ i b)

theorem Geometry.coord_room (G : Geometry s n) (i : Lower G.P.h)
    (k : Nat) (K : k≤7) : G.coord i k<n := by
  have H := G.coord_bound i k
  have V := Nat.mul_le_mul_left G.P.B K
  have W := G.seven
  rw [Nat.mul_comm G.P.B 7] at V
  omega

theorem Geometry.root_coord (G : Geometry s n) (i : Lower G.P.h)
    (k : Nat) : (G.rootAt i k).val=nextAt i.val (G.coord i k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    -- CHECK: SelectedRingGeometry.lean:126-133; the right projection
    -- is ReportStaticSpacing.successor of the SAME GapBounds.
    change nextAt (G.rootAt i k).val (G.width (G.rootAt i k)) =
      nextAt i.val (G.coord i k+G.width (G.rootAt i k))
    rw [nextAt_add,ih]

def Geometry.chart (G : Geometry s n) (i : Lower G.P.h) : Chart G.P.h := by
  let j := G.ring.right i
  let k := G.ring.right j
  have F := G.width_spec i
  have H := G.width_spec j
  have I := G.width_spec k
  have room := G.P.room
  exact chart_of_three i.property F.2.2 H.2.2 I.2.2 (by omega)

theorem Geometry.chart_root (G : Geometry s n) (i : Lower G.P.h) :
    (G.chart i).root=i.val := rfl

theorem Geometry.chart_a (G : Geometry s n) (i : Lower G.P.h) :
    (G.chart i).a=G.width i := rfl

theorem Geometry.chart_length (G : Geometry s n) (i : Lower G.P.h) :
    (G.chart i).L=G.width i+G.width (G.ring.right i)+
      G.width (G.ring.right (G.ring.right i)) := rfl

theorem Geometry.chart_small (G : Geometry s n) (C : Chart G.P.h) :
    C.L≤G.D := (G.P.chart_gate C).2.2.1

def Geometry.start (G : Geometry s n) (i : Lower G.P.h) : Lower G.P.h :=
  G.ring.left (G.ring.left (G.ring.left i))

def Geometry.family (G : Geometry s n) (i : Lower G.P.h) :
    Fin 5 → Chart G.P.h := fun j=>G.chart (G.rootAt (G.start i) j.val)

theorem Geometry.family_root (G : Geometry s n) (i : Lower G.P.h) (j : Fin 5) :
    (G.family i j).root=nextAt (G.start i).val (G.coord (G.start i) j.val) :=
  G.root_coord (G.start i) j.val

theorem Geometry.family_extent (G : Geometry s n) (i : Lower G.P.h) (j : Fin 5) :
    G.coord (G.start i) j.val+(G.family i j).L=
      G.coord (G.start i) (j.val+3) := by
  -- CHECK: chart_of_three (ShortLayerGeometry.lean:107-117).
  -- This is associativity of the sum of three consecutive gap widths.
  rw [Geometry.family,Geometry.chart_length]
  change _ = ((G.coord (G.start i) j.val+
    G.width (G.rootAt (G.start i) j.val))+
    G.width (G.ring.right (G.rootAt (G.start i) j.val)))+
    G.width (G.ring.right (G.ring.right (G.rootAt (G.start i) j.val)))
  omega

theorem Geometry.family_order (G : Geometry s n) (i : Lower G.P.h)
    (j k : Fin 5) (H : j.val<k.val) :
    RearTrace.predecessor (G.family i j).root ∉ watch (G.family i k) := by
  apply ShortSimultaneousOrder.earlier_door_omitted _ _ _ _ _
    (G.family_root i j) (G.family_root i k) (G.coord_lt _ H)
  rw [G.family_extent i k]
  exact G.coord_room _ _ (by have := k.isLt; omega)

theorem Geometry.family_distinct (G : Geometry s n) (i : Lower G.P.h)
    (j k : Fin 5) (H : j≠k) : (G.family i j).root≠(G.family i k).root := by
  intro E
  rw [G.family_root i j,G.family_root i k] at E
  have Q := nextAt_injective_under (G.start i).val _ _
    (G.coord_room _ _ (by have := j.isLt; omega))
    (G.coord_room _ _ (by have := k.isLt; omega)) E
  rcases Nat.lt_trichotomy j.val k.val with L|L|L
  · have := G.coord_lt (G.start i) L
    omega
  · exact H (Fin.ext L)
  · have := G.coord_lt (G.start i) L
    omega

theorem Geometry.family_target (G : Geometry s n) (i : Lower G.P.h) :
    (G.family i 2).root=(G.ring.left i).val ∧
    (G.family i 3).root=i.val ∧
    nextAt (G.family i 2).root (G.family i 2).a=i.val := by
  have H : G.rootAt (G.start i) 2=G.ring.left i := by
    simp [Geometry.rootAt,Geometry.start,G.ring.rl]
  have I : G.rootAt (G.start i) 3=i := by
    change G.ring.right (G.rootAt (G.start i) 2)=i
    rw [H,G.ring.rl]
  refine ⟨congrArg Subtype.val H,congrArg Subtype.val I,?_⟩
  change (G.ring.right (G.rootAt (G.start i) 2)).val=i.val
  exact congrArg Subtype.val I

private theorem Geometry.covered_coord (G : Geometry s n) (i : Lower G.P.h)
    (j : Fin 5) (k : Nat)
    (A : G.coord (G.start i) j.val≤k)
    (B : k<G.coord (G.start i) (j.val+3)) :
    Covered (G.family i) (nextAt (G.start i).val k) := by
  have E := G.family_extent i j
  refine ⟨j,k-G.coord (G.start i) j.val,by omega,?_⟩
  rw [G.family_root i j,←nextAt_add,Nat.add_sub_of_le A]

theorem Geometry.target_internal (G : Geometry s n) (i : Lower G.P.h)
    (e : Fin n) (H : e∈watch (G.family i 2)) :
    Internal (G.family i) e := by
  let d := G.coord (G.start i)
  have H12 : d 1<d 2 := G.coord_lt _ (by decide)
  have H24 : d 2<d 4 := G.coord_lt _ (by decide)
  have H45 : d 4<d 5 := G.coord_lt _ (by decide)
  have H57 : d 5<d 7 := G.coord_lt _ (by decide)
  have E2 : d 2+(G.family i 2).L=d 5 := G.family_extent i 2
  rcases (mem_watch _ _).mp H with H|⟨k,K,H⟩
  · have R : rightNeighbor e=nextAt (G.start i).val (d 2) := by
      rw [H,PhysicalCustody.H1.incoming_spec,G.family_root i 2]
      rfl
    have E : e=nextAt (G.start i).val (d 2-1) := by
      have V : rightNeighbor (nextAt (G.start i).val (d 2-1)) =
          nextAt (G.start i).val (d 2) := by
        change nextAt (G.start i).val ((d 2-1)+1)=_
        rw [show d 2-1+1=d 2 by omega]
      have U := congrArg RearTrace.predecessor (R.trans V.symm)
      simpa only [RearTrace.predecessor_right] using U
    constructor
    · rw [E]
      exact G.covered_coord i 1 _ (show d 1 ≤ _ by omega) (show _ < d 4 by omega)
    · rw [R]
      exact G.covered_coord i 2 _ (show d 2 ≤ _ by omega) (show _ < d 5 by omega)
  · rw [G.family_root i 2,←nextAt_add] at H
    change e=nextAt (G.start i).val (d 2+k) at H
    have R : rightNeighbor e=nextAt (G.start i).val (d 2+k+1) :=
      congrArg rightNeighbor H
    constructor
    · rw [H]
      exact G.covered_coord i 2 _ (show d 2 ≤ _ by omega) (show _ < d 5 by omega)
    · rw [R]
      by_cases Q : d 2+k+1<d 5
      · exact G.covered_coord i 2 _ (show d 2 ≤ _ by omega) Q
      · exact G.covered_coord i 4 _ (show d 4 ≤ _ by omega) (show _ < d 7 by omega)

theorem Geometry.rival_fences (G : Geometry s n) (i : Lower G.P.h) :
    (∀ j : Fin 5, j.val<2 → RearTrace.predecessor (G.family i j).root ∉
      watch (G.family i 2)) ∧
    ∀ j : Fin 5, 2<j.val → nextAt (G.family i j).root ((G.family i j).L-1)
      ∉ watch (G.family i 2) := by
  constructor
  · intro j J
    exact G.family_order i j 2 J
  · intro j J H
    let d := G.coord (G.start i)
    have P := (G.family i j).positive
    have D : d j.val+(G.family i j).L=d (j.val+3) := G.family_extent i j
    have E2 : d 2+(G.family i 2).L=d 5 := G.family_extent i 2
    have B : d (j.val+3)<n := G.coord_room _ _ (by have := j.isLt; omega)
    have B5 : d 5<n := G.coord_room _ _ (by decide)
    have larger : d 5<d (j.val+3) := G.coord_lt _ (by omega)
    have d25 : d 2<d 5 := G.coord_lt _ (by decide)
    have eq : nextAt (G.family i j).root ((G.family i j).L-1) =
        nextAt (G.start i).val (d (j.val+3)-1) := by
      rw [G.family_root i j,←nextAt_add]
      change nextAt _ (d j.val+((G.family i j).L-1))=_
      rw [show d j.val+((G.family i j).L-1)=d (j.val+3)-1 by omega]
    rcases (mem_watch _ _).mp H with H|⟨k,K,H⟩
    · have U := (congrArg rightNeighbor (eq.symm.trans H)).trans
        (PhysicalCustody.H1.incoming_spec (G.family i 2).root)
      rw [G.family_root i 2] at U
      change nextAt (G.start i).val (d (j.val+3)-1+1)=
        nextAt (G.start i).val (d 2) at U
      have V := nextAt_injective_under (G.start i).val _ _
        (by omega) (by omega) U
      omega
    · have U := eq.symm.trans H
      rw [G.family_root i 2,←nextAt_add] at U
      change nextAt (G.start i).val (d (j.val+3)-1)=
        nextAt (G.start i).val (d 2+k) at U
      have V := nextAt_injective_under (G.start i).val _ _
        (by omega) (by omega) U
      omega

def Geometry.word (G : Geometry s n) (i : Lower G.P.h) : List (Fin n) :=
  winningWord (G.family i 2) (G.family i 2).a

def Wcap (D : Nat) : Nat := ShortFiveParkedParam.watchCap D
def Mcap (D : Nat) : Nat := 12*D+8
def prepCost (D : Nat) : Nat := Wcap D^ShortFiveParkedParam.exponent D
def pubCost (D : Nat) : Nat := Wcap D^Mcap D*(prepCost D+Mcap D)
def stageK (D : Nat) : Nat := 3+ShortMISStageBudget.resetCost D+2*pubCost D

theorem Geometry.word_length (G : Geometry s n) (i : Lower G.P.h) :
    (G.word i).length=12*(G.family i 2).L+8 :=
  winning_length _ _ (G.P.chart_gate (G.family i 2)).2.1

theorem Geometry.word_bound (G : Geometry s n) (i : Lower G.P.h) :
    (G.word i).length≤Mcap G.D := by
  rw [G.word_length]
  have H := G.chart_small (G.family i 2)
  unfold Mcap
  omega

theorem Geometry.word_nonempty (G : Geometry s n) (i : Lower G.P.h) :
    G.word i≠[] := by
  intro H
  have E := G.word_length i
  rw [H] at E
  simp at E

theorem Geometry.word_watch (G : Geometry s n) (i : Lower G.P.h) :
    ∀ e∈G.word i,e∈watch (G.family i 2) :=
  winning_watch _ _ (G.P.chart_gate (G.family i 2)).2.1

theorem Geometry.word_internal (G : Geometry s n) (i : Lower G.P.h) :
    ∀ e∈G.word i,Internal (G.family i) e :=
  fun e E=>G.target_internal i e (G.word_watch i e E)

theorem Geometry.watch_card (G : Geometry s n) (cs : Fin 5→Chart G.P.h) :
    (labels cs).length≤Wcap G.D := by
  have H := ShortFiveParkedParam.chartsWatch_bound (List.ofFn cs) G.D
    (fun C E=>by
      obtain ⟨i,I⟩ := List.mem_ofFn.mp E
      rw [←I]
      exact G.chart_small (cs i))
  simpa only [labels,List.length_ofFn,Wcap,ShortFiveParkedParam.watchCap,Nat.mul_comm] using H

-- Actual current-sheet projection and classifier.
def observe (P : Params s n) (x : Raw s n) (i : Lower P.h) : Bool :=
  ShortByteReadouts.misSelected (P.byte x i.val)

def classify (P : Params s n) (x : Raw s n) (e : Fin n) : Option (Lower P.h) :=
  let i := rightNeighbor e
  if H : P.h i=true then
    if (P.byte (rawNext s x e) i).getLsbD 92≠(P.byte x i).getLsbD 92 then
      some ⟨i,H⟩ else none
  else none

theorem classify_some (P : Params s n) (x : Raw s n) (X : Cached P x)
    (e : Fin n) (i : Lower P.h) (H : classify P x e=some i) :
    i.val=rightNeighbor e ∧ mask P.sheet x (rightNeighbor e)=true ∧
      (P.byte (rawNext s x e) i.val).getLsbD 92≠(P.byte x i.val).getLsbD 92 := by
  unfold classify at H
  dsimp only at H
  split at H
  · rename_i A
    split at H
    · rename_i B
      have E := congrArg Subtype.val (Option.some.inj H)
      -- CHECK: Params.maskEq, ShortMISEngine.lean:25.
      refine ⟨E.symm,?_,?_⟩
      · rw [P.maskEq x X.1]
        exact A
      · rw [←E]
        exact B
    · contradiction
  · contradiction

def Agree (P : Params s n) (cs : Fin 5→Chart P.h) (x y : Raw s n) : Prop :=
  ∀ q,Covered cs q→P.byte x q=P.byte y q

theorem outside_agree (P : Params s n) (cs : Fin 5→Chart P.h)
    (x : Raw s n) (e : Fin n) (E : e∉labels cs) :
    Agree P cs (rawNext s x e) x := by
  rintro q ⟨i,j,J,rfl⟩
  apply P.remote_byte
  · intro H
    exact E (included cs i e ((watch_incident (cs i) e).mpr ⟨j,J,.inl H⟩))
  · intro H
    exact E (included cs i e ((watch_incident (cs i) e).mpr ⟨j,J,.inr H⟩))

private theorem agree_trans (P : Params s n) (cs : Fin 5→Chart P.h)
    (x y z : Raw s n) (A : Agree P cs x y) (B : Agree P cs y z) :
    Agree P cs x z := fun q H=>(A q H).trans (B q H)

theorem internal_step_agrees (P : Params s n) (cs : Fin 5→Chart P.h)
    (x y : Raw s n) (X : Cached P x) (Y : Cached P y)
    (A : Agree P cs x y) (e : Fin n) (E : Internal cs e) :
    Agree P cs (rawNext s x e) (rawNext s y e) := by
  let r := rightNeighbor e
  intro q J
  have Px := congrFun (PhysicalShortSheet.exact_raw_step P.sheet x e) q
  have Py := congrFun (PhysicalShortSheet.exact_raw_step P.sheet y e) q
  change P.byte (rawNext s x e) q=_ at Px
  change P.byte (rawNext s y e) q=_ at Py
  rw [Px,Py,P.maskEq x X.1,P.maskEq y Y.1]
  unfold sliceStep
  dsimp only
  change (if q=e then (PhysicalShortSheet.pairStep (rows s) (P.h e,P.h r)
      (P.byte x e,P.byte x r)).1 else if q=r then
      (PhysicalShortSheet.pairStep (rows s) (P.h e,P.h r) (P.byte x e,P.byte x r)).2
      else P.byte x q)=
    (if q=e then (PhysicalShortSheet.pairStep (rows s) (P.h e,P.h r)
      (P.byte y e,P.byte y r)).1 else if q=r then
      (PhysicalShortSheet.pairStep (rows s) (P.h e,P.h r) (P.byte y e,P.byte y r)).2
      else P.byte y q)
  rw [A e E.1,A r E.2,A q J]

theorem pair_local (P : Params s n) (cs : Fin 5→Chart P.h)
    (x y : Raw s n) (X : Cached P x) (Y : Cached P y)
    (A : Agree P cs x y) (e : Fin n) (I : Internal cs e) :
    classify P x e=classify P y e := by
  have K := internal_step_agrees P cs x y X Y A e I
  unfold classify
  dsimp only
  rw [A _ I.2,K _ I.2]

-- CHECK: mechanically ported ShortFiveWatchReplay.lean:93-135;
-- its proof is independent of the selected-bank semantics.
/-- If an explicitly certified local classifier fires in the prescribed
word, it also fires on the unchanged physical tape. Every spectator
mark and all endpoint/cut positions remain in the proof. -/
theorem publication_on_original_word {s n : Nat} {J : Type}
    (P : Params s n) (cs : Fin 5 → Chart P.h) (classify : Raw s n → Fin n → Option J)
    (pairLocal : ∀ x y e, Cached P x → Cached P y → Agree P cs x y → Internal cs e →
      classify x e=classify y e)
    (x y : Raw s n) (X : Cached P x) (Y : Cached P y) (A : Agree P cs x y)
    (w u : List (Fin n)) (word : keep cs w=u) (ok : ∀ e∈u, Internal cs e)
    (j : J) (event : j∈ShortNORCover.publications (rawNext s) classify y u) :
    j∈ShortNORCover.publications (rawNext s) classify x w := by
  have closed (z : Raw s n) (e : Fin n) (Z : Cached P z) : Cached P (rawNext s z e) :=
    P.cached_closed z e Z
  induction w generalizing x y u with
  | nil =>
    have U : u=[] := word.symm
    rw [U] at event
    exact (List.not_mem_nil event).elim
  | cons e w ih =>
    by_cases W : e∈labels cs
    · have E : e::keep cs w=u := by simpa [keep,W] using word
      rw [←E] at ok event
      have I := ok e (by simp)
      have same := pairLocal x y e X Y A I
      simp only [ShortNORCover.publications,same]
      simp only [ShortNORCover.publications] at event
      have tail (T : j∈ShortNORCover.publications (rawNext s) classify (rawNext s y e) (keep cs w)) :=
        ih _ _ (closed x e X) (closed y e Y) (internal_step_agrees P cs x y X Y A e I) _ rfl
          (fun z Z=>ok z (List.mem_cons_of_mem e Z)) T
      cases C : classify y e
      · simp only [C] at event
        exact tail event
      · simp only [C] at event
        rcases List.mem_cons.mp event with B|B
        · exact List.mem_cons.mpr (.inl B)
        · exact List.mem_cons.mpr (.inr (tail B))
    · have E : keep cs w=u := by simpa [keep,W] using word
      have T := ih _ _ (closed x e X) Y
        (agree_trans P cs _ _ _ (outside_agree P cs x e W) A) _ E ok event
      unfold ShortNORCover.publications
      cases classify x e
      · exact T
      · exact List.mem_cons_of_mem _ T

theorem replay_from_word (P : Params s n) (cs : Fin 5→Chart P.h)
    (x : Raw s n×Bool) (X : Cached P x.1) (word : List (Fin n))
    (internal : ∀ e∈word,Internal cs e) (i : Lower P.h)
    (hit : i∈ShortNORCover.publications (rawNext s) (classify P) x.1 word) :
    ShortPrefixTrial.Replay (ShortTwoPublicationClock.phase (rawNext s) (classify P) i)
      (fun e=>decide (e∈labels cs)) x word := by
  intro w W
  have K : keep cs w=word := W
  have E := publication_on_original_word P cs (classify P)
    (fun x y e X Y A I=>pair_local P cs x y X Y A e I)
    x.1 x.1 X X (fun _ _=>rfl) w word K internal i hit
  have H := (ShortTwoPublicationClock.flag_eq (rawNext s) (classify P) i x w).mpr (.inr E)
  unfold ShortTwoPublicationClock.goal at H
  rwa [clock_height] at H

-- Exact raw RESET observer and historical domain.
def bits (P : Params s n) (C : Chart P.h) (x : Raw s n) (k : Nat) : BitVec 19 :=
  (MISByteCodec.kField (C.route.port k)).read (P.byte x (nextAt C.root k))

def Clear (P : Params s n) (C : Chart P.h) (x : Raw s n) : Prop :=
  ∀ k,k<C.L→bits P C x k=MISByteCodec.encode MISByteCodec.E

def Complete (P : Params s n) (C : Chart P.h) (x : Raw s n) : Prop :=
  Clear P C x ∧ MISByteCodec.get (P.byte x C.root) 81 2 (by decide)=1 ∧
    MISByteCodec.get (P.byte x C.root) 78 3 (by decide)=1

def Parked (P : Params s n) (C : Chart P.h) (x : Raw s n) : Prop :=
  Complete P C x ∧ ∀ k,k<C.L→P.h (nextAt C.root k)=true→
    (P.byte x (nextAt C.root k)).getLsbD (91-(C.route.port k).val)=false

def FiveParked (P : Params s n) (cs : Fin 5→Chart P.h) (x : Raw s n) : Prop :=
  ∀ i,Parked P (cs i) x

def Issuable (P : Params s n) (C : Chart P.h) (x : Raw s n) : Prop :=
  pc (P.byte x C.root)=8

instance issuableDec (P : Params s n) (C : Chart P.h) (x : Raw s n) : Decidable (Issuable P C x) := by
  unfold Issuable
  infer_instance

def resetStep (P : Params s n) (C : Chart P.h)
    (z : Raw s n×Bool) (e : Fin n) : Raw s n×Bool :=
  (rawNext s z.1 e,z.2 || decide (Issuable P C z.1 ∧ e=RearTrace.predecessor C.root))

def resetGoal (P : Params s n) (C : Chart P.h) (z : Raw s n×Bool) : Prop :=
  z.2=true ∧ Complete P C z.1

def GenuineAt (P : Params s n) (C : Chart P.h) (x : Raw s n) (w : List (Fin n)) : Prop :=
  ∃ a t : List (Fin n), w=a++RearTrace.predecessor C.root::t ∧
    Issuable P C (rawRun x a) ∧
    ShortResetReleased.BeforeConsume C (.fwd 0) t ∧
    ShortResetReleased.stageRun C (.fwd 0) t=.done

def Receipt (P : Params s n) (C : Chart P.h) (x : Raw s n) (w : List (Fin n)) : Prop :=
  GenuineAt P C x w ∧ Parked P C (rawRun x w) ∧
    ∃ v : List (Fin n), ∃ e : Fin n, w=v++[e] ∧ rightNeighbor e=C.root ∧
      MISByteCodec.get (P.byte (rawRun x v) C.root) 81 2 (by decide)=2 ∧
      MISByteCodec.get (P.byte (rawRun x v) C.root) 78 3 (by decide)=0 ∧
      (MISByteCodec.kField 0).read (P.byte (rawRun x v) C.root)=
        MISByteCodec.encode ShortResetFlow.resetReply

-- A forward image of a genuinely generated own RESET, not of an arbitrary
-- displayed Parked or controller snapshot. Semantic J/S must be proved
-- on this image by the local auth producer.
def Epoch (P : Params s n) (C : Chart P.h) (y : Raw s n) : Prop :=
  ∃ x : Raw s n, ∃ w v : List (Fin n), Cached P x ∧ Receipt P C x w ∧
    rawRun (rawRun x w) v=y

theorem epoch_run (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (X : Epoch P C x) (w : List (Fin n)) : Epoch P C (rawRun x w) := by
  obtain ⟨z,u,v,Z,R,E⟩ := X
  exact ⟨z,u,v++w,Z,R,by rw [run_append,E]⟩

def Good (P : Params s n) (x : Raw s n) : Prop :=
  Cached P x ∧ ∀ r,P.h r=true→∃ C : Chart P.h,C.root=r ∧ Epoch P C x

theorem good_closed (P : Params s n) (x : Raw s n) (e : Fin n)
    (X : Good P x) : Good P (rawNext s x e) := by
  refine ⟨P.cached_closed x e X.1,?_⟩
  intro r R
  obtain ⟨C,E,H⟩ := X.2 r R
  exact ⟨C,E,epoch_run P C x H [e]⟩

-- THESE are the remaining row-level producer obligations, not already
-- checked declarations. The complete consumer below takes them explicitly.
structure LocalRows (G : Geometry s n) where
  rank : ∀ C : Chart G.P.h,
    ShortMISStageBudget.RankRows G.P.sheet C G.D (Cached G.P)
  clean : ∀ (C : Chart G.P.h) x, Cached G.P x→Issuable G.P C x→
    Height.IIDExpectedHittingTimeAtMost (resetStep G.P C) (resetGoal G.P C)
      (x,false) ((2*C.L+1)*n)
  firstHit : ∀ (C : Chart G.P.h) x, Cached G.P x→∀ w,
    SequentialMarkClock.ClearBefore (resetStep G.P C) (resetGoal G.P C) (x,false) w→
    resetGoal G.P C (SequentialMarkClock.run (resetStep G.P C) (x,false) w)→
      Receipt G.P C x w
  parkPhase : ∀ _C : Chart G.P.h,
    RestartRankClock.Phase (rawNext s) (Cached G.P) (Option Stage)
      (ShortSimulLocalParam.phaseCap G.D)
  parkGoal : ∀ C,(parkPhase C).goal=Parked G.P C
  parkWatch : ∀ C,(parkPhase C).watch=watch C
  parkedNondoor : ∀ (C : Chart G.P.h) x, Cached G.P x→Parked G.P C x→
    ∀ e,e≠RearTrace.predecessor C.root→Parked G.P C (rawNext s x e)
  auth : ∀ x e,Good G.P x→observe G.P (rawNext s x e)=
    match classify G.P x e with
    | none => observe G.P x
    | some j => ShortNORCover.update G.ring (observe G.P x) j
  win : ∀ (i : Lower G.P.h) x,Good G.P x→FiveParked G.P (G.family i) x→
    i∈ShortNORCover.publications (rawNext s) (classify G.P) x (G.word i)

-- Generic Bellman splice of inherited ISSUE0 rank and a clean own reset.
theorem clean_cost_via_issue0 (G : Geometry s n) (L : LocalRows G)
    (C : Chart G.P.h) (t : Nat) (x : Raw s n) (X : Cached G.P x) :
    Height.iidHitCost (resetStep G.P C) (resetGoal G.P C) t (x,false)≤
    Height.iidHitCost (rawNext s) (Issuable G.P C) t x+((2*C.L+1)*n)*n^t := by
  let B := (2*C.L+1)*n
  induction t generalizing x with
  | zero => simp [Height.iidHitCost]
  | succ t IH =>
    by_cases I : Issuable G.P C x
    · rw [Height.iidHitCost_of_target _ _ _ I,Nat.zero_add]
      exact L.clean C x X I _
    · have NG : ¬resetGoal G.P C (x,false) := by simp [resetGoal]
      simp only [Height.iidHitCost,if_neg NG,if_neg I]
      let f := fun e : Fin n=>Height.iidHitCost (rawNext s)
        (Issuable G.P C) t (rawNext s x e)
      have P : (List.ofFn (fun e : Fin n=>Height.iidHitCost
          (resetStep G.P C) (resetGoal G.P C) t (resetStep G.P C (x,false) e))).sum≤
          (List.ofFn (fun e : Fin n=>f e+B*n^t)).sum := by
        apply FiniteUniformStoppingTree.ofFn_sum_le
        intro e
        have Y : resetStep G.P C (x,false) e=(rawNext s x e,false) := by
          simp [resetStep,I]
        rw [Y]
        exact IH _ (G.P.cached_closed x e X)
      rw [FiniteUniformStoppingTree.ofFn_sum_add,FiniteUniformStoppingTree.ofFn_sum_const] at P
      have E : n*(B*n^t)=B*n^(t+1) := by rw [Nat.pow_succ]; ac_rfl
      rw [E] at P
      apply Nat.le_trans (Nat.add_le_add_left P _)
      rw [Nat.add_assoc]
      exact Nat.le_refl _

theorem reset_expected (G : Geometry s n) (L : LocalRows G)
    (C : Chart G.P.h) (x : Raw s n) (X : Cached G.P x) :
    Height.IIDExpectedHittingTimeAtMost (resetStep G.P C) (resetGoal G.P C)
      (x,false) (ShortMISStageBudget.resetCost G.D*n) := by
  have B := ShortMISStageBudget.sheet_issue0_expected G.P.sheet C (G.chart_small C)
    (Cached G.P) G.P.cached_closed (L.rank C) x X
  -- CHECK: ShortSheetRankClock.lean:19-21, ShortPhaseRank.lean:54;
  -- at slot zero nextAt root 0=root, hence the same Issuable predicate.
  change L4.IIDExpectedHittingTimeAtMost (rawNext s) (Issuable G.P C) x
    (n*(G.D+1)^ShortInheritedRankParam.phaseCap G.D) at B
  have BH := (MonitorRawBridge.height_iff_row _ _ _ _).mpr B
  intro t
  have S := G.chart_small C
  have D : ((2*C.L+1)*n)*n^t≤((2*G.D+1)*n)*n^t :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have T := Nat.le_trans (clean_cost_via_issue0 G L C t x X) (Nat.add_le_add (BH t) D)
  unfold ShortMISStageBudget.resetCost
  simpa only [Nat.add_mul,Nat.mul_comm n ((G.D+1)^ShortInheritedRankParam.phaseCap G.D)]
    using T

private theorem chart_list (P : Params s n) (rs : List (Fin n))
    (R : ∀ r∈rs,P.h r=true) :
    ∃ cs : List (Chart P.h), cs.map (fun C=>C.root)=rs := by
  induction rs with
  | nil => exact ⟨[],rfl⟩
  | cons r rs ih =>
    obtain ⟨C,E,_⟩ := P.chart_exists r (R r (by simp))
    obtain ⟨cs,F⟩ := ih (fun q Q=>R q (List.mem_cons_of_mem _ Q))
    exact ⟨C::cs,by simp [E,F]⟩

private theorem receipts_sound (G : Geometry s n) (L : LocalRows G)
    (cs : List (Chart G.P.h)) (x : Raw s n) (X : Cached G.P x)
    (w : List (Fin n))
    (R : SequentialMarkClock.FirstHitReceipts (resetStep G.P) (resetGoal G.P)
      false cs (x,false) w) :
    ∀ C∈cs,Epoch G.P C (rawRun x w) := by
  induction cs generalizing x w with
  | nil => simp
  | cons C cs ih =>
    obtain ⟨u,v,E,_,B,H,R⟩ := R
    have T := L.firstHit C x X u B H
    have F := SequentialMarkClock.phase_run_raw (rawNext s) (resetStep G.P)
      (fun _ _ _=>rfl) C (x,false) u
    rw [run_clock] at F
    rw [F] at R
    intro D HD
    rcases List.mem_cons.mp HD with A|A
    · subst D
      exact ⟨x,u,v,X,T,by rw [E,run_append]⟩
    · rw [E,run_append]
      exact ih (rawRun x u) (cache_run G.P x X u) v R D A

theorem all_owners_expected (G : Geometry s n) (L : LocalRows G)
    (x : Raw s n) (X : Cached G.P x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (Good G.P) x
      (ShortMISStageBudget.resetCost G.D*n^2) := by
  obtain ⟨cs,M⟩ := chart_list G.P (ShortAllOwnerClock.roots G.P.h)
    (fun r R=>(ShortAllOwnerClock.mem_roots _ _).mp R)
  let z := SequentialMarkClock.start false cs x
  let f := SequentialMarkClock.step (rawNext s) (resetStep G.P) (resetGoal G.P) false
  have phys : ∀ (z : SequentialMarkClock.State (Raw s n) Bool (Chart G.P.h)) e,
      (f z e).raw=rawNext s z.raw e :=
    SequentialMarkClock.step_raw _ _ _ _ (fun _ _ _=>rfl)
  have initial : ∀ C (y : Raw s n), ¬resetGoal G.P C (y,false) := by
    intro C y
    simp [resetGoal]
  have K := SequentialMarkClock.expected (rawNext s) (resetStep G.P) (resetGoal G.P)
    false (Cached G.P) (fun _ _ _=>rfl) G.P.cached_closed
    (ShortMISStageBudget.resetCost G.D*n) (fun C y _=>initial C y)
    (reset_expected G L) cs x X
  have len : cs.length≤n := by
    have E := congrArg List.length M
    rw [List.length_map] at E
    rw [E]
    exact ShortAllOwnerClock.roots_length_le _
  have V : cs.length*(ShortMISStageBudget.resetCost G.D*n)≤
      ShortMISStageBudget.resetCost G.D*n^2 := by
    calc
      _ ≤ n*(ShortMISStageBudget.resetCost G.D*n) := Nat.mul_le_mul_right _ len
      _ = _ := by rw [Nat.pow_two]; ac_rfl
  have bound : Height.IIDExpectedHittingTimeAtMost f SequentialMarkClock.finished z
      (ShortMISStageBudget.resetCost G.D*n^2) :=
    fun t=>Nat.le_trans (K t) (Nat.mul_le_mul_right _ V)
  -- CHECK: MonitorRawBridge.lean:154-173; note target is on raw endpoint.
  refine MonitorRawBridge.expected_of_monitor_words (rawNext s) f
    (fun y=>y.raw) SequentialMarkClock.finished (Good G.P) phys z ?_ _ bound
  intro w D
  have before : SequentialMarkClock.BeforeCurrent (resetGoal G.P) z := by
    unfold z SequentialMarkClock.start
    cases cs with
    | nil => trivial
    | cons C cs => exact initial C x
  have R := SequentialMarkClock.first_hit_receipts_of_finished (rawNext s)
    (resetStep G.P) (resetGoal G.P) false initial z w before D
  change SequentialMarkClock.FirstHitReceipts (resetStep G.P) (resetGoal G.P)
    false cs (x,false) w at R
  change Good G.P (SequentialMarkClock.run (rawNext s) x w)
  rw [run_clock]
  refine ⟨cache_run G.P x X w,?_⟩
  intro r H
  have E : r∈cs.map (fun C=>C.root) := by
    rw [M]
    exact (ShortAllOwnerClock.mem_roots _ _).mpr H
  obtain ⟨C,HC,RC⟩ := List.mem_map.mp E
  exact ⟨C,RC,receipts_sound G L cs x X w R C HC⟩

-- Five-parked regeneration from arbitrary dirty current-sheet bytes.
theorem regenerate (G : Geometry s n) (L : LocalRows G)
    (i : Lower G.P.h) (x : Raw s n) (X : Cached G.P x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (FiveParked G.P (G.family i)) x (prepCost G.D*n) := by
  let cs := G.family i
  let ps := fun j : Fin 5=>L.parkPhase (cs j)
  let W := labels cs
  have Inc (j : Fin 5) (e : Fin n) (E : e∈(ps j).watch) : e∈W := by
    change e∈(L.parkPhase (cs j)).watch at E
    rw [L.parkWatch] at E
    exact included cs j e E
  have Safe (j k : Fin 5) (I : j.val<k.val) (y : Raw s n) (e : Fin n)
      (Y : Cached G.P y) (E : e∈(ps k).watch) (A : (ps j).goal y) :
      (ps j).goal (rawNext s y e) := by
    change (L.parkPhase (cs j)).goal y at A
    change (L.parkPhase (cs j)).goal _ 
    change e∈(L.parkPhase (cs k)).watch at E
    rw [L.parkGoal] at A ⊢
    rw [L.parkWatch] at E
    exact L.parkedNondoor _ y Y A e (fun H=>G.family_order i j k I (H ▸ E))
  have Idle (j : Fin 5) (y : Raw s n) (e : Fin n)
      (Y : Cached G.P y) (E : e∉(ps j).watch) (A : (ps j).goal y) :
      (ps j).goal (rawNext s y e) := by
    change (L.parkPhase (cs j)).goal y at A
    change (L.parkPhase (cs j)).goal _
    change e∉(L.parkPhase (cs j)).watch at E
    rw [L.parkGoal] at A ⊢
    rw [L.parkWatch] at E
    apply L.parkedNondoor _ y Y A e
    intro H
    exact E (H.symm ▸ ShortSimulLocal.door_mem (cs j))
  have card : W.length≤Wcap G.D := G.watch_card cs
  have Q : 1<Wcap G.D := by unfold Wcap ShortFiveParkedParam.watchCap; omega
  have H := RestartRankClock.simultaneous_expected ps none G.P.cached_closed W
    Inc Safe Idle (Wcap G.D) Q card x X
  have E : RestartRankClock.AllComplete ps=FiveParked G.P cs := by
    funext y
    apply propext
    constructor
    · intro A j
      have T := A j
      change (L.parkPhase (cs j)).goal y at T
      rwa [L.parkGoal] at T
    · intro A j
      change (L.parkPhase (cs j)).goal y
      rw [L.parkGoal]
      exact A j
  rw [E] at H
  simpa only [prepCost,ShortFiveParkedParam.exponent,Nat.mul_comm] using H

theorem publication_expected (G : Geometry s n) (L : LocalRows G) :
    ShortTwoPublicationClock.UniformPublicationMean (rawNext s) (classify G.P)
      (Good G.P) (pubCost G.D*n) := by
  intro i x X
  let cs := G.family i
  let word := G.word i
  let setup : ShortPrefixTrial.Setup (Raw s n) n :=
    ⟨word,fun e=>decide (e∈labels cs),FiveParked G.P cs,
      ShortTwoPublicationClock.phase (rawNext s) (classify G.P) i⟩
  have P : 0<Wcap G.D := by unfold Wcap ShortFiveParkedParam.watchCap; omega
  have W : ShortPrefixTrial.cardinal setup.watch≤Wcap G.D :=
    Nat.le_trans (ShortPrefixRawService.cardinal_le_list (labels cs)) (G.watch_card cs)
  have B : setup.word.length≤Mcap G.D := G.word_bound i
  have Z : Wcap G.D^Mcap G.D*(prepCost G.D*n+Mcap G.D*n)=pubCost G.D*n := by
    rw [pubCost,Nat.mul_assoc,Nat.add_mul]
  have H := ShortPrefixTrial.renewal_expected_param setup (Good G.P) (rawNext s)
    (fun _ _=>rfl) (fun z e=>good_closed G.P z.1 e)
    (fun z e E=>by simp [setup,ShortTwoPublicationClock.phase,E])
    (fun e E=>decide_eq_true (included cs 2 e (G.word_watch i e E)))
    (fun z A F=>replay_from_word G.P cs z A.1 word (G.word_internal i) i
      (L.win i z.1 A F))
    (G.word_nonempty i) (Wcap G.D) (Mcap G.D) P W B
    (prepCost G.D*n) (fun y Y=>regenerate G L i y Y.1) (x,false) X
  rw [Z] at H
  exact (MonitorRawBridge.height_iff_row _ _ _ _).mpr H

-- The only final predicate is raw maximality in the actual historical Good.
def Cut (G : Geometry s n) (x : Raw s n) : Prop :=
  RawMaximal G.ring (observe G.P) (Good G.P) x

def upper (P : Params s n) (x : Raw s n) : Fin n→Bool :=
  ShortNORPhysicalAdapter.embed P.h (observe P x)

private def ownerSites (h : Fin n→Bool) : List (Lower h) :=
  (List.finRange n).filterMap (fun i=>if H : h i=true then some ⟨i,H⟩ else none)

private theorem ownerSites_mem (h : Fin n→Bool) (i : Lower h) : i∈ownerSites h := by
  unfold ownerSites
  exact List.mem_filterMap.mpr ⟨i.val,List.mem_finRange _,by simp [i.property]⟩

theorem stage_expected (G : Geometry s n) (L : LocalRows G)
    (x : Raw s n) (X : G.P.Lower x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (Cut G) x (stageK G.D*n^2) := by
  rw [stageK,Nat.add_mul,Nat.add_mul,Nat.add_assoc]
  apply AllSizeComposition.additive_stage (rawNext s) (Cached G.P) (Cut G)
    (3*n^2) (ShortMISStageBudget.resetCost G.D*n^2+2*pubCost G.D*n^2) x
    (G.P.cached_expected x X)
  intro y Y
  unfold Cut
  apply AllSizeComposition.additive_stage (rawNext s) (Good G.P)
    (RawMaximal G.ring (observe G.P) (Good G.P)) _ _ y
    (all_owners_expected G L y Y)
  intro z Z
  refine CustodyMonitorTargets.raw_two_covers_expected (rawNext s) (classify G.P)
    G.ring (observe G.P) (Good G.P) (good_closed G.P) (fun y e Y => by
      have A := L.auth y e Y
      cases E : classify G.P y e <;> rw [E] at A <;> exact A)
    (ownerSites G.P.h) (ownerSites_mem _) ?_ (pubCost G.D) (publication_expected G L) z Z
  exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

theorem cut_closed (G : Geometry s n) (L : LocalRows G) (x : Raw s n)
    (e : Fin n) (X : Cut G x) : Cut G (rawNext s x e) :=
  CustodyMonitorTargets.raw_maximal_closed (rawNext s) (classify G.P)
    G.ring (observe G.P) (Good G.P) (good_closed G.P) (fun y e Y => by
      have A := L.auth y e Y
      cases E : classify G.P y e <;> rw [E] at A <;> exact A) x e X

theorem cut_frozen (G : Geometry s n) (L : LocalRows G) (x : Raw s n)
    (e : Fin n) (X : Cut G x) : upper G.P (rawNext s x e)=upper G.P x := by
  have H : observe G.P (rawNext s x e)=observe G.P x := by
    rw [L.auth x e X.1]
    cases classify G.P x e with
    | none => rfl
    | some j => exact ShortNORFrozen.update_eq_of_maximal G.ring _ X.2.1 X.2.2 j
  exact congrArg (ShortNORPhysicalAdapter.embed G.P.h) H

theorem cut_layer (G : Geometry s n) (x : Raw s n) (X : Cut G x) :
    SelectedMISLayers.Layer G.gaps (upper G.P x) :=
  ShortNORPhysicalAdapter.layer_of_observe G.gaps G.P.hh
    (by have := G.seven; omega) (observe G.P x) X.2.1 X.2.2

theorem cut_gaps (G : Geometry s n) (x : Raw s n) (X : Cut G x) :
    GapBounds (upper G.P x) (2*G.A) (3*G.P.B) :=
  SelectedMISLayers.layer_gaps (cut_layer G x X)

theorem cut_nonempty (G : Geometry s n) (x : Raw s n) (X : Cut G x) :
    ∃ i,upper G.P x i=true :=
  SelectedMISLayers.layer_nonempty (cut_layer G x X) G.P.hh

-- Actual H2 → MIS2 handoff: these use the NEW CHECKED H2 theorem,
-- not an additional H2 maximality assumption.
theorem h2_frozen (N : 21<n) (x : Raw s n) (X : PermanentH2 N x)
    (w : List (Fin n)) : SelectedMISLayers.h2 (rawRun x w)=SelectedMISLayers.h2 x := by
  obtain ⟨z,Z,H⟩ := X
  exact (ShortH2Final.physical_suffix N z Z x H w).2.2.1

theorem h2_gaps (N : 21<n) (x : Raw s n) (X : PermanentH2 N x) :
    GapBounds (SelectedMISLayers.h2 x) 4 9 := by
  obtain ⟨z,Z,H⟩ := X
  have C := (ShortH2Final.physical_suffix N z Z x H []).2.2.2
  exact SelectedMISLayers.layer_gaps C

theorem h2_nonempty (N : 21<n) (x : Raw s n) (X : PermanentH2 N x) :
    ∃ i,SelectedMISLayers.h2 x i=true := by
  obtain ⟨z,Z,H⟩ := X
  have C := (ShortH2Final.physical_suffix N z Z x H []).2.2.2
  exact SelectedMISLayers.layer_nonempty C (SelectedMISLayers.h1_nonempty Z.1 (by omega))

def H2Fibre (N : 21<n) (x0 y : Raw s n) : Prop :=
  PermanentH2 N y ∧ SelectedMISLayers.h2 y=SelectedMISLayers.h2 x0

theorem h2_fibre_closed (N : 21<n) (x0 y : Raw s n) (e : Fin n)
    (Y : H2Fibre N x0 y) : H2Fibre N x0 (rawNext s y e) :=
  ⟨permanent_h2_closed N y Y.1 [e],(h2_frozen N y Y.1 [e]).trans Y.2⟩

def mis2Geometry (N : 63<n) (x0 : Raw s n)
    (H : PermanentH2 (by omega : 21<n) x0) : Geometry s n where
  P := Params.ofGapBounds .mis2 (H2Fibre (by omega) x0)
    (h2_fibre_closed (by omega) x0)
    (SelectedMISLayers.h2 x0) (fun y Y=>Y.2)
    (h2_nonempty (by omega) x0 H) 4 9 (h2_gaps (by omega) x0 H) (by omega)
  A := 4
  gaps := h2_gaps (by omega) x0 H
  seven := by change 7*9<n; omega

-- Compare embed with the literal oldHeaders mask, NOT a synthetic layer.
theorem upper_mis2 (P : Params s n) (S : P.sheet=.mis2)
    (x : Raw s n) (X : P.Lower x) : upper P x=SelectedMISLayers.h3 x := by
  have E := ShortNORPhysicalAdapter.embed_eq_mask (h:=P.h)
    (fun i=>ShortByteReadouts.misSelected (P.byte x i))
  change upper P x=_ at E
  rw [E]
  funext i
  rw [SelectedMISLayers.h3_mask]
  have M := congrFun (P.maskEq x X) i
  rw [S] at M
  change SelectedMISLayers.h2 x i=P.h i at M
  simp only [Params.byte,S,bytes,M]

def K_H3 : Nat := stageK 27
def K_H4 : Nat := stageK 81

-- LocalRows is kept in the existential anchor to carry the actual
-- proved row laws across closure. No state-dependent choice of a new mask.
def PermanentH3 (N : 63<n) (y : Raw s n) : Prop :=
  ∃ x0 : Raw s n, ∃ H : PermanentH2 (by omega : 21<n) x0,
    ∃ _L : LocalRows (mis2Geometry N x0 H), Cut (mis2Geometry N x0 H) y

theorem permanent_h3_from_h2 (N : 63<n) (x : Raw s n)
    (H : PermanentH2 (by omega : 21<n) x)
    (L : LocalRows (mis2Geometry N x H)) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH3 N) x (K_H3*n^2) := by
  let G := mis2Geometry N x H
  have X : G.P.Lower x := ⟨H,rfl⟩
  have T := stage_expected G L x X
  intro t
  exact Nat.le_trans
    (RankRenewal.cost_mono_target (next:=rawNext s) (Cut G) (PermanentH3 N)
      (fun y Y=>⟨x,H,L,Y⟩) t x) (T t)

theorem permanent_h3_step (N : 63<n) (x : Raw s n) (e : Fin n)
    (X : PermanentH3 N x) : PermanentH3 N (rawNext s x e) := by
  obtain ⟨z,H,L,C⟩ := X
  exact ⟨z,H,L,cut_closed _ L x e C⟩

theorem permanent_h3_closed (N : 63<n) (x : Raw s n) (X : PermanentH3 N x)
    (w : List (Fin n)) : PermanentH3 N (rawRun x w) := by
  induction w generalizing x with
  | nil => exact X
  | cons e w ih => exact ih _ (permanent_h3_step N x e X)

theorem permanent_h3_mask_step (N : 63<n) (x : Raw s n) (e : Fin n)
    (X : PermanentH3 N x) : SelectedMISLayers.h3 (rawNext s x e)=SelectedMISLayers.h3 x := by
  obtain ⟨z,H,L,C⟩ := X
  let G := mis2Geometry N z H
  have R := cut_frozen G L x e C
  have C' := cut_closed G L x e C
  rw [upper_mis2 G.P rfl _ C'.1.1.1,upper_mis2 G.P rfl _ C.1.1.1] at R
  exact R

theorem permanent_h3_gaps (N : 63<n) (x : Raw s n) (X : PermanentH3 N x) :
    GapBounds (SelectedMISLayers.h3 x) 8 27 := by
  obtain ⟨z,H,L,C⟩ := X
  let G := mis2Geometry N z H
  have R := cut_gaps G x C
  rw [upper_mis2 G.P rfl _ C.1.1.1] at R
  exact R

theorem permanent_h3_nonempty (N : 63<n) (x : Raw s n) (X : PermanentH3 N x) :
    ∃ i,SelectedMISLayers.h3 x i=true := by
  obtain ⟨z,H,L,C⟩ := X
  let G := mis2Geometry N z H
  have R := cut_nonempty G x C
  rwa [upper_mis2 G.P rfl _ C.1.1.1] at R

/-- Specialize to the existing checked anchored H2→MIS2 entrance. -/
def mis2Geometry_at (N : 63<n) (x0 : Raw s n) (A : H2Ready x0)
    (y : Raw s n) (Y : ShortH2Final.PermanentH2At x0 A (by omega) y) : Geometry s n where
  P := ShortMIS2Entrance.params (by omega) x0 A y Y
  A := 4
  gaps := h2_gaps (by omega) y ⟨x0,A,Y⟩
  seven := by change 7*9<n; omega

theorem anchored_mis2_stage (N : 63<n) (x0 : Raw s n) (A : H2Ready x0)
    (y : Raw s n) (Y : ShortH2Final.PermanentH2At x0 A (by omega) y)
    (L : LocalRows (mis2Geometry_at N x0 A y Y)) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (Cut (mis2Geometry_at N x0 A y Y)) y (K_H3*n^2) :=
  stage_expected _ L y ⟨Y,rfl⟩

-- The checked negative control needs no enumeration of a 2^32 ring.
theorem mis2_not_cap9 (C : Chart (mask .mis2 ShortMIS2Cap.x)) : ¬ C.L≤9 := by
  rw [ShortMIS2Cap.every_mis2_chart_has_length12 C]
  decide

theorem mis2_not_word116 (C : Chart (mask .mis2 ShortMIS2Cap.x)) (g : Nat)
    (G : g+1<C.L) : ¬ (winningWord C g).length≤116 := by
  rw [winning_length C g G,ShortMIS2Cap.every_mis2_chart_has_length12 C]
  decide

#print axioms Geometry.target_internal
#print axioms Geometry.rival_fences
#print axioms replay_from_word
#print axioms regenerate
#print axioms publication_expected
#print axioms stage_expected
#print axioms h2_fibre_closed
#print axioms permanent_h3_from_h2
#print axioms permanent_h3_closed
#print axioms anchored_mis2_stage
#print axioms mis2_not_cap9
#print axioms mis2_not_word116

end
end L4.ShortMISLift

