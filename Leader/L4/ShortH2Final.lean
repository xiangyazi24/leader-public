import Leader.L4.ShortPrefixRawService
import Leader.L4.ShortFiveCentreClock
import Leader.L4.ShortFiveWinningWord
import Leader.L4.ShortClassifiedOwnerAuth
import Leader.L4.ShortNORFrozen
import Leader.L4.ShortNORPhysicalAdapter
import Leader.L4.Height.LeaderBridge
import Leader.L4.RankRenewal
import Leader.L4.ShortFiveGuardTour

namespace L4.ShortH2Final
open PhysicalCustody ShortResetCycle ShortResetMIS1Ring ShortResetChart
open ShortSimulLocal ShortFiveParked ShortSimultaneousOrder ShortFiveWatchReplay
open ShortClassifiedOwnerAuth ShortGuardedNOR ShortFiveWinningWord
open CustodyMonitorTargets

variable {s n : Nat}
set_option exponentiation.threshold 40575

/-- Exact boundary of the literal marked-word replay. -/
def LiteralS1 (s n : Nat) : Prop :=
  ∀ (x : Raw s n), H2Ready x → 21<n → ∀ (r : Fin n)
    (cs : Fin 5→Chart (header x)),
    (∀ i,(cs i).root=nextAt r (offset (header x) r i.val)) →
    FiveParked cs x → ∀ g : Nat, 0<g → g+1<(cs 2).L →
    ShortAdmitFlight.FixedGate (s:=s) (cs 2) g →
    ∃ (i : Sites (header x)) (lead tail : List (Fin n)),
      i.val=nextAt (cs 2).root (cs 2).a ∧
      winningWord (cs 2) g=lead++nextAt (cs 2).root ((cs 2).a-1)::tail ∧
      classifyFixed (header x) (rawRun x lead)
        (nextAt (cs 2).root ((cs 2).a-1))=some i

private theorem fold_run (x : Raw s n) (w : List (Fin n)) :
    w.foldl (rawNext s) x=rawRun x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (rawNext s x e)

private theorem witness_mem {h : Fin n→Bool} (x : Raw s n)
    (lead tail : List (Fin n)) (e : Fin n) (i : Sites h)
    (E : classifyFixed h (rawRun x lead) e=some i) :
    i ∈ ShortNORCover.publications (rawNext s) (classifyFixed h) x (lead++e::tail) := by
  rw [ShortTwoPublicationClock.publications_append,List.mem_append]
  right
  rw [fold_run]
  simp [ShortNORCover.publications,E]

private theorem literal_on_fibre (S : LiteralS1 s n)
    {h : Fin n→Bool} (x : Raw s n) (F : Fiber h x) (N : 21<n)
    (r : Fin n) (cs : Fin 5→Chart h)
    (roots : ∀ i,(cs i).root=nextAt r (offset h r i.val))
    (P : FiveParked cs x) (g : Nat) (gp : 0<g) (gL : g+1<(cs 2).L)
    (G : ShortAdmitFlight.FixedGate (s:=s) (cs 2) g)
    (i : Sites h) (C : nextAt (cs 2).root (cs 2).a=i.val) :
    i ∈ ShortNORCover.publications (rawNext s) (classifyFixed h) x (winningWord (cs 2) g) := by
  have E : h=header x := funext fun q=>(F.2 q).symm
  subst h
  obtain ⟨j,lead,tail,J,W,H⟩ := S x F.1 N r cs roots P g gp gL G
  have eq : j=i := Subtype.ext (J.trans C)
  subst j
  rw [W]
  exact witness_mem x lead tail _ i H

def publicationScale : Nat := 50^116 * (50^40575+116)

theorem uniform_publication_of_literal (S : LiteralS1 s n) (N : 21<n)
    (x0 : Raw s n) (A : H2Ready x0) :
    ShortTwoPublicationClock.UniformPublicationMean (rawNext s) (classifyFixed (header x0))
      (AllOwnerInv (header x0)) (publicationScale*n) := by
  apply ShortPrefixRawService.uniform_of_families (by omega : 5≤n)
    (AllOwnerInv (header x0)) (fun y e G=>all_owner_closed y (by omega) e G)
    (fun _ G=>⟨G.1,G.2.1⟩) (50^40575)
  intro i
  let owner := PhysicalH1Neighbors.left A.1 i
  let left := PhysicalH1Neighbors.left A.1
  let r := (left (left owner)).val
  obtain ⟨cs,roots,_,center,_,small,gates,_,mean⟩ :=
    ShortFiveCentreClock.fixed_five_for_centre N x0 A i
  obtain ⟨g,gp,gL,G⟩ := gates 2
  refine ⟨cs,winningWord (cs 2) g,small,?_,winning_length_le _ _ gL (small 2),?_,
    winning_internal x0 A.1 N r cs roots g gL,?_,?_⟩
  · intro E
    have L := winning_length (cs 2) g gL
    rw [E] at L
    simp at L
  · intro e E
    exact List.mem_flatMap.mpr ⟨cs 2,by simp,winning_watch (cs 2) g gL e E⟩
  · intro y Y P
    exact literal_on_fibre S y ⟨Y.1,Y.2.1⟩ N r cs roots P g gp gL G i center
  · intro y Y
    simpa only [Nat.mul_comm] using mean y Y

private def ownerSites (h : Fin n→Bool) : List (Sites h) :=
  (List.finRange n).filterMap (fun i=>if H : h i=true then some ⟨i,H⟩ else none)

private theorem ownerSites_mem (h : Fin n→Bool) (i : Sites h) :
    i ∈ ownerSites h := by
  unfold ownerSites
  exact List.mem_filterMap.mpr ⟨i.val, List.mem_finRange _, by simp [i.property]⟩

def PermanentH2At (x0 : Raw s n) (A : H2Ready x0) (N : 21<n) (y : Raw s n) : Prop :=
  RawMaximal
    (PhysicalH1Neighbors.fixedRing (x:=x0) (h:=header x0) A.1 (by omega : 3<n) (fun _=>rfl))
    observe (AllOwnerInv (header x0)) y

theorem permanent_expected_of_service (N : 21<n)
    (x0 : Raw s n) (A : H2Ready x0) (K : Nat)
    (Service : ShortTwoPublicationClock.UniformPublicationMean
      (rawNext s) (classifyFixed (header x0)) (AllOwnerInv (header x0)) (K*n)) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH2At x0 A N) x0
      ((10^8095+19)*n^2 + 2*K*n^2) := by
  apply (MonitorRawBridge.height_iff_row _ _ _ _).mp
  refine Height.iid_stage_le (rawNext s) (by omega : 0<n) x0
    (AllOwnerInv (header x0)) (PermanentH2At x0 A N) ((10^8095+19)*n^2) (2*K*n^2) ?_ ?_
  · apply (MonitorRawBridge.height_iff_row _ _ _ _).mpr
    intro t
    exact Nat.le_trans (RankRenewal.cost_mono_target (next:=rawNext s) _ _ (fun _ G=>Or.inl G) t x0)
      (all_owner_inv_expected x0 A (by omega : 9<n) t)
  · intro y Y
    unfold PermanentH2At
    have hn : 3<n := by omega
    have hn9 : 9<n := by omega
    apply (MonitorRawBridge.height_iff_row _ _ _ _).mpr
    refine raw_two_covers_expected (rawNext s) (classifyFixed (header x0))
      (PhysicalH1Neighbors.fixedRing (x:=x0) (h:=header x0) A.1 hn (fun _=>rfl))
      observe (AllOwnerInv (header x0)) (fun z e G=>all_owner_closed z (by omega : 9<n) e G)
      (fun z e G=>by
        have H := all_owner_nor_step (h:=header x0) x0 z A hn9 (fun _=>rfl) G e
        dsimp only at H
        cases E : classifyFixed (header x0) z e <;> simpa only [E] using H)
      (ownerSites (header x0)) (ownerSites_mem _) ?_ K Service y Y
    exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

theorem permanent_expected (S : LiteralS1 s n) (N : 21<n)
    (x0 : Raw s n) (A : H2Ready x0) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH2At x0 A N) x0
      ((10^8095+19+2*publicationScale)*n^2) := by
  rw [Nat.add_mul]
  exact permanent_expected_of_service N x0 A _ (uniform_publication_of_literal S N x0 A)

theorem permanent_frozen (N : 21<n) (x0 : Raw s n) (A : H2Ready x0)
    (y : Raw s n) (M : PermanentH2At x0 A N y) (w : List (Fin n)) :
    PermanentH2At x0 A N (rawRun y w) ∧
    (observe (rawRun y w) : Sites (header x0)→Bool)=observe y := by
  rw [←fold_run]
  have hn : 3<n := by omega
  have hn9 : 9<n := by omega
  exact ShortNORFrozen.raw_observe_frozen (rawNext s) (classifyFixed (header x0))
    (PhysicalH1Neighbors.fixedRing (x:=x0) (h:=header x0) A.1 hn (fun _=>rfl))
    observe (AllOwnerInv (header x0)) (fun z e G=>all_owner_closed z (by omega : 9<n) e G)
    (fun z e G=>by
        have H := all_owner_nor_step (h:=header x0) x0 z A hn9 (fun _=>rfl) G e
        dsimp only at H
        cases E : classifyFixed (header x0) z e <;> simpa only [E] using H) y w M

theorem selected_readout (w : BitVec 96) :
    ShortReaderMIS1.selectedValue w=ShortByteReadouts.misSelected w := by
  have B : (w.extractLsb' 92 1).toNat<2 := (w.extractLsb' 92 1).isLt
  have L : (w.extractLsb' 92 1).toNat=0 ∨ (w.extractLsb' 92 1).toNat=1 := by omega
  rcases L with L|L <;>
    unfold ShortReaderMIS1.selectedValue ShortByteReadouts.misSelected
      ShortByteReadouts.misSelector MISByteCodec.lane AllSizeProtocol.Field.read
  · rw [L]
    have E : (w.extractLsb' 92 1).getLsbD 0=false := by
      change (w.extractLsb' 92 1).toNat.testBit 0=false
      rw [L]
      decide
    have W : w[92] = false := by simpa using E
    simp [W,ShortByteReadouts.misBank]
  · rw [L]
    have E : (w.extractLsb' 92 1).getLsbD 0=true := by
      change (w.extractLsb' 92 1).toNat.testBit 0=true
      rw [L]
      decide
    have W : w[92] = true := by simpa using E
    simp [W,ShortByteReadouts.misBank]

theorem physical_suffix (N : 21<n) (x0 : Raw s n) (A : H2Ready x0)
    (y : Raw s n) (M : PermanentH2At x0 A N y) (w : List (Fin n)) :
    let z := rawRun y w
    PermanentH2At x0 A N z ∧
    SelectedMISLayers.h1 z=SelectedMISLayers.h1 x0 ∧
    SelectedMISLayers.h2 z=SelectedMISLayers.h2 y ∧
    SelectedMISLayers.Layer (SelectedMISLayers.h1_gaps A.1) (SelectedMISLayers.h2 z) := by
  dsimp only
  let z := rawRun y w
  let h := SelectedMISLayers.h1 x0
  have hn : 3<n := by omega
  obtain ⟨P,F⟩ := permanent_frozen N x0 A y M w
  have H (v : Raw s n) (V : PermanentH2At x0 A N v) :
      SelectedMISLayers.h1 v=SelectedMISLayers.h1 x0 := funext V.1.2.1
  have mask (v : Raw s n) (V : PermanentH2At x0 A N v) :
      SelectedMISLayers.h2 v=ShortNORPhysicalAdapter.embed h (observe v) := by
    funext j
    rw [SelectedMISLayers.h2_mask,congrFun (H v V) j]
    have R : observe v = (fun i : Sites h=>ShortByteReadouts.misSelected (v i.val).mis1) :=
      funext fun i=>selected_readout (v i.val).mis1
    rw [R]
    exact congrFun (ShortNORPhysicalAdapter.embed_eq_mask
      (h:=h) (fun k=>ShortByteReadouts.misSelected (v k).mis1)).symm j
  have RI := ShortNORPhysicalAdapter.mis1_h1_rings_identical A.1 hn
  have IN := P.2.1
  have DN := P.2.2
  change ShortNORCover.Independent
      (PhysicalH1Neighbors.fixedRing (x:=x0) (h:=h) A.1 hn (fun _=>rfl)) (observe z) at IN
  change ∀ i,ShortNORCover.Dominates
      (PhysicalH1Neighbors.fixedRing (x:=x0) (h:=h) A.1 hn (fun _=>rfl)) (observe z) i at DN
  have IN' := congrArg (fun R => ShortNORCover.Independent R (observe z)) RI
  have DN' := congrArg (fun R => ∀ i, ShortNORCover.Dominates R (observe z) i) RI
  have IN2 := Eq.mp IN' IN
  have DN2 := Eq.mp DN' DN
  refine ⟨P,H z P,(mask z P).trans ((congrArg (ShortNORPhysicalAdapter.embed h) F).trans
    (mask y M).symm),?_⟩
  rw [mask z P]
  exact ShortNORPhysicalAdapter.layer_of_observe _ (SelectedMISLayers.h1_nonempty A.1 (by omega))
    hn (observe z) IN2 DN2

#print axioms physical_suffix
#print axioms selected_readout
theorem literalS1 : LiteralS1 s n :=
  ShortFiveGuardTour.mis1_fenced_word_actual_publication

theorem permanent_h2_expected (N : 21<n)
    (x0 : Raw s n) (A : H2Ready x0) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH2At x0 A N) x0
      ((10^8095+19+2*publicationScale)*n^2) :=
  permanent_expected literalS1 N x0 A

#print axioms literalS1
#print axioms permanent_h2_expected
#print axioms uniform_publication_of_literal
#print axioms permanent_expected_of_service
#print axioms permanent_expected
#print axioms permanent_frozen
end L4.ShortH2Final
