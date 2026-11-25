import Leader.L4.ShortFiveRivalFence

namespace L4.ShortFiveLaneHeaders
open AllSizeProtocol PhysicalCustody PhysicalCustody.H1 ShortResetMIS1Ring
open ShortResetChart ShortResetCycle ShortResetRow ShortResetForwardH2
open ShortSimultaneousOrder ShortFiveWatchSupport PhysicalH1Neighbors
open ShortFiveRivalFence ShortFiveWinningWord ShortResetWatch ShortPreReadGrants ShortHelloForward

variable {s n : Nat}

private theorem next_selected_segment (x : Raw s n) (M : rawMaximal x) (r : Fin n)
    (R : header x r=true) :
    header x (nextAt r (rightDist (header x) r))=true ∧
    ∀ k, 0<k → k<rightDist (header x) r → header x (nextAt r k)=false := by
  obtain ⟨d,D,H,C⟩ := gap M r R
  rw [rightDist_eq_gap D H C]
  exact ⟨H,C⟩

/-- On each of its three selected header positions, an actual chart has
exactly port 0, 1, or 2, not just a matching physical site. -/
theorem chart_selected_port (x : Raw s n) (M : rawMaximal x) (N : 9<n)
    (C : Chart (header x)) (j : Fin 3) :
    let k := offset (header x) C.root j.val
    k<C.L ∧ header x (nextAt C.root k)=true ∧ C.route.port k=j := by
  dsimp only
  have L := chart_extent x M N C
  let d := offset (header x) C.root
  have bounds (j : Nat) (J : j<3) : d j<C.L := by
    rw [L]; exact offset_monotone _ _ J
  have aux (j : Nat) (J : j<3) : C.route.port (d j) = (⟨j,J⟩ : Fin 3) := by
    induction j with
    | zero => exact C.rootPort
    | succ j ih =>
      let q := nextAt C.root (d j)
      let len := rightDist (header x) q
      have actual : d (j+1)=d j+len := rfl
      have pos : 0<len := by dsimp [len]; unfold rightDist; split <;> omega
      have hh := next_selected_segment x M q (offset_at_header x M C.root C.rootHeader j)
      have stable (i : Nat) (I : i<len) :
          C.route.port (d j+i) = (⟨j,by omega⟩ : Fin 3) := by
        induction i with
        | zero => exact ih (by omega)
        | succ i step =>
          have B : d j+(i+1)<C.L := by
            have := bounds (j+1) J
            omega
          have K := C.route.live (d j+i) (by omega : d j+i+1<C.L)
          have Z : header x (rightNeighbor (nextAt C.root (d j+i)))=false := by
            change header x (nextAt C.root (d j+i+1))=false
            rw [show d j+i+1=d j+(i+1) by omega,nextAt_add]
            exact hh.2 _ (by omega) I
          change destination (header x (rightNeighbor (nextAt C.root (d j+i)))) (C.route.port (d j+i)) = _ at K
          rw [Z,step (by omega)] at K
          change some (⟨j,by omega⟩ : Fin 3) = some (C.route.port (d j+i+1)) at K
          rw [show d j+(i+1)=d j+i+1 by omega]
          exact (Option.some.inj K).symm
      have B : d (j+1)<C.L := bounds _ J
      have K := C.route.live (d j+(len-1)) (by omega : d j+(len-1)+1<C.L)
      have Eq : d j+(len-1)+1=d (j+1) := by omega
      have Z : header x (rightNeighbor (nextAt C.root (d j+(len-1))))=true := by
        change header x (nextAt C.root (d j+(len-1)+1))=true
        rw [Eq]
        exact offset_at_header x M C.root C.rootHeader _
      change destination (header x (rightNeighbor (nextAt C.root (d j+(len-1))))) (C.route.port (d j+(len-1))) = _ at K
      rw [Z,stable (len-1) (by omega),Eq] at K
      change (if hj : j+1<3 then some (⟨j+1,hj⟩ : Fin 3) else none) =
        some (C.route.port (d (j+1))) at K
      rw [dif_pos J] at K
      exact (Option.some.inj K).symm
  exact ⟨bounds _ j.isLt,offset_at_header x M C.root C.rootHeader _,aux _ j.isLt⟩

/-- For target header j, its slot k is owned by chart (2+j−k).
The difference is nonnegative and less than five, so all conflicting
lanes lie inside the actual five-Parked fence. -/
theorem raw_header_lane_owner (x : Raw s n) (M : rawMaximal x) (N : 21<n)
    (r : Fin n) (cs : Fin 5 → Chart (header x))
    (roots : ∀ i, (cs i).root=nextAt r (offset (header x) r i.val))
    (j k : Fin 3) :
    let i : Fin 5 := ⟨2+j.val-k.val,by have := j.isLt; omega⟩
    ∃ p : Nat, p<(cs i).L ∧ (cs i).route.port p=k ∧
      nextAt (cs i).root p =
        nextAt (cs 2).root (offset (header x) (cs 2).root j.val) := by
  dsimp only
  let i : Fin 5 := ⟨2+j.val-k.val,by have := j.isLt; omega⟩
  let d := offset (header x) r
  refine ⟨offset (header x) (cs i).root k.val, ?_, ?_, ?_⟩
  · exact (chart_selected_port x M (by omega) (cs i) k).1
  · exact (chart_selected_port x M (by omega) (cs i) k).2.2
  · rw [roots i, roots 2, ←nextAt_add, ←nextAt_add,
      ←offset_add,←offset_add]
    have E : i.val+k.val=2+j.val := by
      dsimp [i]
      have := k.isLt
      omega
    rw [E]
    rfl

theorem rival_header_asks_and_grants (x : Raw s n) (X : H2Ready x) (N : 21<n)
    (r : Fin n) (cs : Fin 5 → Chart (header x))
    (roots : ∀ i, (cs i).root=nextAt r (offset (header x) r i.val))
    (P : ShortFiveParked.FiveParked cs x) (w : List (Fin n))
    (watchOnly : ∀ e∈w, e∈watch (cs 2)) (j k : Fin 3) (K : k≠j) :
    let q := nextAt (cs 2).root (offset (header x) (cs 2).root j.val)
    let y := rawRun x w
    (headerGrantView (y q).mis1).ask k=false ∧ (y q).mis1.getLsbD (91-k.val)=false := by
  let i : Fin 5 := ⟨2+j.val-k.val,by have := j.isLt; omega⟩
  have J : i≠2 := by
    intro E
    have B := congrArg Fin.val E
    have I := k.isLt
    apply K
    apply Fin.ext
    change 2+j.val-k.val=2 at B
    omega
  obtain ⟨p,L,port,site⟩ := raw_header_lane_owner x X.1 N r cs roots j k
  change p<(cs i).L at L
  change (cs i).route.port p=k at port
  change nextAt (cs i).root p=nextAt (cs 2).root (offset (header x) (cs 2).root j.val) at site
  have H : header x (nextAt (cs i).route.root p)=true := by
    change header x (nextAt (cs i).root p)=true
    rw [site]
    exact (chart_selected_port x X.1 (by omega) (cs 2) j).2.1
  have V := all_rivals_fenced x X N r cs roots P w watchOnly i J
  have A := V.1 p L H
  have G := V.2 p L H
  change (headerGrantView ((rawRun x w) (nextAt (cs i).root p)).mis1).ask
    ((cs i).route.port p)=false at A
  change ((rawRun x w) (nextAt (cs i).root p)).mis1.getLsbD (91-((cs i).route.port p).val)=false at G
  rw [site,port] at A G
  exact ⟨A,G⟩

theorem chart_header_coordinates (x : Raw s n) (M : rawMaximal x) (N : 9<n)
    (C : Chart (header x)) (k : Nat) (K : k<C.L) (H : header x (nextAt C.root k)=true) :
    ∃ j : Fin 3, k=offset (header x) C.root j.val := by
  let d := offset (header x) C.root
  have D : C.L=d 3 := chart_extent x M N C
  have cover (j : Nat) (A : d j≤k) (B : k<d (j+1)) : k=d j := by
    by_cases yes : k=d j
    · exact yes
    · exfalso
      have Z : 0<k-d j := by omega
      have E : k=d j+(k-d j) := by omega
      let q := nextAt C.root (d j)
      have C0 := offset_at_header x M C.root C.rootHeader j
      obtain ⟨_,F⟩ := next_selected_segment x M q C0
      have D0 : d (j+1)=d j+rightDist (header x) q := rfl
      have K0 : k-d j<rightDist (header x) q := by omega
      have X0 := F _ Z K0
      have Y0 : nextAt q (k-d j)=nextAt C.root k := by
        dsimp [q]
        rw [←nextAt_add,←E]
      rw [Y0,H] at X0
      contradiction
  by_cases B0 : k<d 1
  · exact ⟨0,cover 0 (Nat.zero_le _) B0⟩
  · by_cases B1 : k<d 2
    · exact ⟨1,cover 1 (by omega) B1⟩
    · exact ⟨2,cover 2 (by omega) (by change k<d 3; omega)⟩

#print axioms chart_selected_port
#print axioms raw_header_lane_owner
#print axioms rival_header_asks_and_grants
#print axioms chart_header_coordinates
end L4.ShortFiveLaneHeaders
