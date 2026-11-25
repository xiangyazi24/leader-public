import Leader.L4.ShortParkedMIS1Ring
import Leader.L4.ShortAdmitMIS1Ring
import Leader.L4.ShortForwardReadyRank
import Leader.L4.ShortGateChart
import Leader.L4.ShortDirtyWaitExit

namespace L4.ShortMaskLeastForward
open AllSizeProtocol MISByteCodec PhysicalCustody
open ShortResetRow ShortResetMIS1Ring ShortAdmitMIS1Ring ShortParkedMIS1Ring
open ShortResetCycle ShortResetChart ShortResetForwardH2 ShortForwardReadyRank ShortGateChart
open ShortForwardRank ShortResetWatch ShortPacketTag ShortDirtySweep

theorem out_mem_notdoor {n : Nat} {h : Fin n→Bool} (C : Chart h) (i : Nat) (I : i<C.L) :
    nextAt C.root i∈watch C ∧ nextAt C.root i≠RearTrace.predecessor C.root := by
  constructor
  · exact (mem_watch C _).mpr (.inr ⟨i,I,rfl⟩)
  · intro e
    have Z : nextAt C.root (i+1)=nextAt C.root 0 := by
      change rightNeighbor (nextAt C.root i)=C.root
      rw [e,RearTrace.right_predecessor]
    have NL := C.length_lt
    have K := nextAt_injective_under _ _ _ (by omega) (by omega) Z
    omega

private theorem slot_at_new_bits {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (y : Raw s n) (i : Nat) (t : Token) (N : bits C.route y i=encode t) :
    slot C.route y i=decode (slotGate C y i) (encode t) := by
  change decode (slotGate C y i) (bits C.route y i)=_
  rw [N]

private theorem ungated_debt {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (i : Nat) (G : slotGate C x i=false) :
    raceDebt (slot C.route x i)=0 := by
  have R : (slot C.route x i).race=0 := by
    change (decode (slotGate C x i) (bits C.route x i)).race=0
    rw [G,ungated_race_zero]
  simp [raceDebt,R]

private theorem least_under (P : Nat→Prop) (m : Nat)
    (H : ∃ i, i<m ∧ P i) :
    ∃ i, i<m ∧ P i ∧ ∀ j, j<i → ¬P j := by
  classical
  induction m with
  | zero => obtain ⟨i,I,_⟩ := H; omega
  | succ m ih =>
    by_cases B : ∃ i, i<m ∧ P i
    · obtain ⟨i,I,F,K⟩ := ih B
      exact ⟨i,by omega,F,K⟩
    · obtain ⟨i,I,F⟩ := H
      have E : i=m := by
        by_cases U : i<m
        · exact (B ⟨i,U,F⟩).elim
        · omega
      subst i
      exact ⟨m,by omega,F,fun j J Pj=>B ⟨j,J,Pj⟩⟩

/-- A physical least inherited forward always has a rank-decreasing
watched move: its ready output, or one legal edge observation on the
two-sided ADMIT gate. The mark is never the owner's root door. -/
theorem nominate_forward {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (Hx : ∀ q,header x q=h q)
    (HY : ∀ e q, header (rawNext s x e) q=h q)
    (g : Nat) (gp : 0<g) (gl : g+1<C.L)
    (gates : ∀ i, i<C.L → (slotGate C x i=true ↔ i=g))
    (afterGates : ∀ e i, i<C.L →
      (slotGate C (rawNext s x e) i=true ↔ i=g))
    (nonzero : ¬ NoForward C x) :
    ∃ e, e∈watch C ∧ e≠RearTrace.predecessor C.root ∧
      physicalScore C (rawNext s x e)<physicalScore C x := by
  classical
  have existsF : ∃ i, i<C.L ∧ (slot C.route x i).tag=2 := by
    by_cases E : ∃ i, i<C.L ∧ (slot C.route x i).tag=2
    · exact E
    · exact (nonzero (fun i I F=>E ⟨i,I,F⟩)).elim
  obtain ⟨i,I,F,least⟩ := least_under (fun j=>(slot C.route x j).tag=2) C.L existsF
  let ei := nextAt C.root i
  let t := slot C.route x i
  cases rd : forwardReady (header x ei) (x ei).mis1 (C.route.port i) with
  | true =>
    have W := out_mem_notdoor C i I
    exact ⟨ei,W.1,W.2,ready_descent C x ⟨i,I⟩ Hx (HY ei) F rd⟩
  | false =>
    have S := unready_forward_shape (header x ei) (x ei).mis1 (C.route.port i) F rd
    have oldGate : slotGate C x i=true := S.1.2.2
    have Gi : i=g := (gates i I).mp oldGate
    have bnd : i+1<C.L := by omega
    have pos : 0<i := by omega
    have GY (e : Fin n) : slotGate C (rawNext s x e) i=true :=
      (afterGates e i I).mpr Gi
    have shp : t.opcode=2 ∧ t.fault=false ∧ t.payload≤1 ∧ t.outcome=0 ∧ t.applied=false :=
      ⟨S.1.1,S.1.2.1,S.2.2⟩
    have rr : t.race=1 ∨ t.race=3 ∨ t.race=2 := by
      have R : t.race=1 ∨ t.race=2 ∨ t.race=3 := S.2.1
      omega
    have redecode (e : Fin n) (r : Nat) (lo : 1≤r) (hi : r≤5)
        (B : bits C.route (rawNext s x e) i=encode {t with race:=r}) :
        slot C.route (rawNext s x e) i={t with race:=r} := by
      rw [slot_at_new_bits C _ i _ B,GY e]
      exact admit_race_roundtrip t r F shp.1 shp.2.1 shp.2.2.1 shp.2.2.2.1
        shp.2.2.2.2 lo hi
    have sz : 1<n := by have := C.length_lt; omega
    let a : Fin C.L := ⟨i,I⟩
    by_cases r2 : t.race=2
    · let y := rawNext s x ei
      let b : Fin C.L := ⟨i+1,bnd⟩
      have W := out_mem_notdoor C i I
      refine ⟨ei,W.1,W.2,?_⟩
      have d : destination (header x (rightNeighbor ei)) (C.route.port i)=some (C.route.port (i+1)) := by
        simpa only [Chart.route,if_pos bnd] using C.actual_dst x Hx i I
      have B : bits C.route y i=encode {t with race:=4} := by
        have P := parked_admit_left_raw x ei (edge_sep sz ei) (C.route.port i) t rfl F
          shp.1 shp.2.1 oldGate (.inr r2)
        have E : ¬t.race=1 := by omega
        rw [if_neg E] at P
        exact P
      have U : slot C.route y i={t with race:=4} := redecode _ _ (by decide) (by decide) B
      have keep : (slot C.route y (i+1)).tag=(slot C.route x (i+1)).tag :=
        parked_outgoing_successor_tag_raw x ei (edge_sep sz ei) _ _ d F rd
      have gx' : slotGate C x (i+1)=false :=
        Bool.eq_false_iff.mpr (fun J=>by have := (gates _ bnd).mp J; omega)
      have gy' : slotGate C y (i+1)=false :=
        Bool.eq_false_iff.mpr (fun J=>by
          have := (afterGates ei _ bnd).mp J
          omega)
      have G : raceDebt (slot C.route y (i+1))=raceDebt (slot C.route x (i+1)) :=
        (ungated_debt C y _ gy').trans (ungated_debt C x _ gx').symm
      rw [physicalScore_eq C y (HY ei),physicalScore_eq C x Hx]
      apply observe_lt a b (fun E=>by have := congrArg Fin.val E; change i=i+1 at this; omega) F
      · change (slot C.route y i).tag=2
        rw [U]
        exact F
      · change raceDebt (slot C.route y i)<raceDebt t
        rw [U]
        exact raceDebt_obs t _ shp.1 shp.1 shp.2.1 shp.2.1
          (.inr ⟨.inl r2,.inl rfl⟩)
      · change localScore _ (i+1) (slot C.route y (i+1))=_
        unfold localScore
        rw [keep,G]
      · intro j J K
        rw [chart_except C x i j.val I j.isLt Hx (HY ei)
          (fun E=>J (Fin.ext E)) (fun E=>K (Fin.ext E))]
    · let k := i-1
      have K : k+1=i := by omega
      have Kl : k<C.L := by omega
      let ek := nextAt C.root k
      let y := rawNext s x ek
      let b : Fin C.L := ⟨k,Kl⟩
      have W := out_mem_notdoor C k Kl
      refine ⟨ek,W.1,W.2,?_⟩
      have no := least k (by omega)
      have d : destination (header x (rightNeighbor ek)) (C.route.port k)=some (C.route.port (k+1)) := by
        simpa only [Chart.route,if_pos (by omega : k+1<C.L)] using C.actual_dst x Hx k Kl
      have side : t.race=1 ∨ t.race=3 := by omega
      let r := if t.race=1 then 2 else 5
      have B : bits C.route y i=encode {t with race:=r} := by
        have old : oldK (header x (rightNeighbor ek)) (x (rightNeighbor ek)).mis1
            (C.route.port (k+1))=t := by
          change slot C.route x (k+1)=t
          rw [K]
        have g : slotGate C x (k+1)=true := by rwa [K]
        rw [←K]
        exact parked_admit_right_raw x ek (edge_sep sz ek) (C.route.port k) (C.route.port (k+1))
          d no t old F shp.1 shp.2.1 g side
      have R : r=2 ∨ r=5 := by unfold r; split <;> simp
      have U := redecode ek r (by omega) (by omega) B
      have keep : (slot C.route y k).tag=(slot C.route x k).tag := by
        have F' : (slot C.route x (k+1)).tag=2 := by rw [K]; exact F
        exact parked_incoming_predecessor_tag_raw x ek (edge_sep sz ek) _ _ d no F'
      rw [physicalScore_eq C y (HY ek),physicalScore_eq C x Hx]
      apply observe_lt a b (fun E=>by have := congrArg Fin.val E; change i=k at this; omega) F
      · change (slot C.route y i).tag=2
        rw [U]
        exact F
      · change raceDebt (slot C.route y i)<raceDebt t
        rw [U]
        apply raceDebt_obs t {t with race:=r} shp.1 shp.1 shp.2.1 shp.2.1
        rcases side with S|S
        · exact .inl ⟨S,.inl (if_pos S)⟩
        · exact .inr ⟨.inr S,.inr (if_neg (by omega))⟩
      · change localScore _ k (slot C.route y k)=localScore _ k (slot C.route x k)
        rw [localScore_nonforward no,localScore_nonforward (keep ▸ no)]
      · intro j J L
        rw [chart_except C x k j.val Kl j.isLt Hx (HY ek)
          (fun E=>L (Fin.ext E)) (fun E=>J (Fin.ext (E.trans K)))]

end L4.ShortMaskLeastForward
