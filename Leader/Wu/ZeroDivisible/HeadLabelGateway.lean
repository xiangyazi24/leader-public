import Leader.Wu.ZeroDivisible.HeadIncomingWrite
import Leader.Wu.ZeroDivisible.HeadResetWord
import Leader.Wu.ZeroDivisible.BinaryRank

/-! Label normalization by actual incoming-edge transfers. The shield producer
and arbitrary-root coordinate transport are separate gateway obligations. -/
namespace PPLLAstraGateway
open PPLLAstraResetWord
attribute [local irreducible] PPLLAstraDesign2.pipeline

private def rev {n : Nat} (i : Fin n) : Fin n := ⟨n-1-i.val,by omega⟩
private theorem rev_rev {n : Nat} (i : Fin n) : rev (rev i) = i := by
  apply Fin.ext
  dsimp [rev]
  omega
private def rank {ψ n : Nat} (C : Fin n → AgentState ψ) : Nat :=
  PPLLAstraBinaryRank.weight (fun i => (C (rev i)).leader)

private theorem incoming_progress {ψ n : Nat} (hp : ψ>0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hroot : (C ⟨0,ring.hn⟩).leader=true) (x : Fin n)
    (hx : 0<x.val) (hl : (C x).leader=true) (hz : (C x).label.val≠0) :
    let e : Fin n := ⟨x.val-1,by omega⟩
    let D := (protocol hp κ).step ring C e
    PopulationProtocol.Reachable (protocol hp κ) ring C D ∧
    rank D < rank C ∧
    (D ⟨0,ring.hn⟩).leader = (C ⟨0,ring.hn⟩).leader ∧
    (D ⟨0,ring.hn⟩).label = (C ⟨0,ring.hn⟩).label := by
  let e : Fin n := ⟨x.val-1,by omega⟩
  let D := (protocol hp κ).step ring C e
  have hneighbor : ring.rightNeighbor e=x := by
    apply Fin.ext
    change (x.val-1+1)%n=x.val
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hxe : x≠e := by intro h; have hh:=congrArg Fin.val h; dsimp [e] at hh; omega
  have hi := PPLLAstraIncoming.pipeline_incoming hp κ (C e) (C x) hl hz
  have hright : (D x).leader=false := by
    simpa [D,PopulationProtocol.step,protocol,hxe,hneighbor] using hi.2.1
  have hleft : (D e).leader=true := by
    simpa [D,PopulationProtocol.step,protocol,hneighbor] using hi.1
  have hlabel : (D e).label=(C e).label := by
    simpa [D,PopulationProtocol.step,protocol,hneighbor] using hi.2.2
  refine ⟨PopulationProtocol.OneStep.to_reachable ⟨e,rfl⟩,?_,?_,?_⟩
  · apply PPLLAstraBinaryRank.first_difference_drop _ _ (rev x)
    · simpa only [rev_rev] using hl
    · simpa only [rev_rev] using hright
    · intro i him
      have hix : rev i≠x := by
        intro h
        have hh:=congrArg Fin.val h
        dsimp [rev] at hh him
        omega
      have hie : rev i≠e := by
        intro h
        have hh:=congrArg Fin.val h
        dsimp [rev,e] at hh him
        omega
      change (C (rev i)).leader = ((protocol hp κ).step ring C e (rev i)).leader
      simp only [PopulationProtocol.step,hneighbor,if_neg hie,if_neg hix]
  · by_cases he0 : e=⟨0,ring.hn⟩
    · rw [← he0]
      exact hleft.trans (by simpa only [he0] using hroot.symm)
    · have hx0 : (⟨0,ring.hn⟩ : Fin n)≠x := by intro h; have:=congrArg Fin.val h; simp at this; omega
      change ((protocol hp κ).step ring C e ⟨0,ring.hn⟩).leader = (C ⟨0,ring.hn⟩).leader
      simp only [PopulationProtocol.step,hneighbor,if_neg (Ne.symm he0),if_neg hx0]
  · by_cases he0 : e=⟨0,ring.hn⟩
    · simpa only [he0] using hlabel
    · have hx0 : (⟨0,ring.hn⟩ : Fin n)≠x := by intro h; have:=congrArg Fin.val h; simp at this; omega
      change ((protocol hp κ).step ring C e ⟨0,ring.hn⟩).label = (C ⟨0,ring.hn⟩).label
      simp only [PopulationProtocol.step,hneighbor,if_neg (Ne.symm he0),if_neg hx0]

/-- Actual incoming edges normalize every nonroot leader label while preserving
the existing root leader and its label. This is the first label-normalization
phase of the gateway, not an anchor-creation or shield-production theorem. -/
theorem reaches_nonroot_zero {ψ n : Nat} (hp : ψ>0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hroot : (C ⟨0,ring.hn⟩).leader=true) :
    ∃ D, PopulationProtocol.Reachable (protocol hp κ) ring C D ∧
      (D ⟨0,ring.hn⟩).leader=true ∧
      (D ⟨0,ring.hn⟩).label=(C ⟨0,ring.hn⟩).label ∧
      ∀ i : Fin n, 0<i.val → (D i).leader=true → (D i).label.val=0 := by
  classical
  generalize hk : rank C=k
  induction k using Nat.strongRecOn generalizing C with
  | ind k ih =>
    by_cases hex : ∃ x : Fin n, 0<x.val ∧ (C x).leader=true ∧ (C x).label.val≠0
    · obtain ⟨x,hx,hl,hz⟩ := hex
      let e : Fin n := ⟨x.val-1,by omega⟩
      let D := (protocol hp κ).step ring C e
      obtain ⟨hr,hd,hbit,hlab⟩ := incoming_progress hp κ ring C hroot x hx hl hz
      have hlt : rank D<k := by simpa only [← hk] using hd
      obtain ⟨F,hDF,hF,hFL,hNZ⟩ := ih (rank D) hlt D (hbit.trans hroot) rfl
      exact ⟨F,hr.trans hDF,hF,hFL.trans hlab,hNZ⟩
    · refine ⟨C,(show PopulationProtocol.Reachable (protocol hp κ) ring C C from PopulationProtocol.Reachable.refl (P:=protocol hp κ) (ring:=ring) C),hroot,rfl,?_⟩
      intro i hi hl
      by_cases hz : (C i).label.val=0
      · exact hz
      · exact False.elim (hex ⟨i,hi,hl,hz⟩)


/-! Coordinate arithmetic follows the existing Local3 rotation proof, but the
transport below is for PopulationProtocol.step and its actual Reachable type. -/
def rotateIndex {n : Nat} (ring : DirectedRing n) (a i : Fin n) : Fin n :=
  ⟨(a.val+i.val)%n,Nat.mod_lt _ ring.hn⟩
def unrotateIndex {n : Nat} (ring : DirectedRing n) (a i : Fin n) : Fin n :=
  ⟨(n-a.val+i.val)%n,Nat.mod_lt _ ring.hn⟩
theorem rotateIndex_unrotateIndex {n : Nat} (ring : DirectedRing n) (a i : Fin n) :
    rotateIndex ring a (unrotateIndex ring a i)=i := by
  apply Fin.ext
  change (a.val+((n-a.val+i.val)%n))%n=i.val
  calc
    _ = (a.val+(n-a.val+i.val))%n := by rw [Nat.add_mod a.val]; simp only [Nat.mod_mod]; rw [← Nat.add_mod]
    _ = (n+i.val)%n := by congr 1; omega
    _ = i.val := by simp [Nat.mod_eq_of_lt i.isLt]
theorem unrotateIndex_rotateIndex {n : Nat} (ring : DirectedRing n) (a i : Fin n) :
    unrotateIndex ring a (rotateIndex ring a i)=i := by
  apply Fin.ext
  change (n-a.val+((a.val+i.val)%n))%n=i.val
  calc
    _ = (n-a.val+(a.val+i.val))%n := by rw [Nat.add_mod (n-a.val)]; simp only [Nat.mod_mod]; rw [← Nat.add_mod]
    _ = (n+i.val)%n := by congr 1; omega
    _ = i.val := by simp [Nat.mod_eq_of_lt i.isLt]
theorem rotateIndex_zero {n : Nat} (ring : DirectedRing n) (a : Fin n) :
    rotateIndex ring a ⟨0,ring.hn⟩=a := by
  apply Fin.ext
  simp [rotateIndex,Nat.mod_eq_of_lt a.isLt]
theorem rotateIndex_inj {n : Nat} (ring : DirectedRing n) (a i j : Fin n)
    (h : rotateIndex ring a i=rotateIndex ring a j) : i=j := by
  have hh := congrArg (unrotateIndex ring a) h
  simpa only [unrotateIndex_rotateIndex] using hh
theorem rotateIndex_rightNeighbor {n : Nat} (ring : DirectedRing n) (a i : Fin n) :
    rotateIndex ring a (ring.rightNeighbor i)=ring.rightNeighbor (rotateIndex ring a i) := by
  apply Fin.ext
  change (a.val+((i.val+1)%n))%n=(((a.val+i.val)%n)+1)%n
  rw [Nat.add_mod a.val, Nat.mod_mod, ← Nat.add_mod]
  rw [Nat.add_mod ((a.val+i.val)%n), Nat.mod_mod, ← Nat.add_mod]
  rw [Nat.add_assoc]
def rotateConfig {n : Nat} {Q : Type} (ring : DirectedRing n) (a : Fin n) (C : Fin n→Q) :=
  fun i => C (rotateIndex ring a i)
def unrotateConfig {n : Nat} {Q : Type} (ring : DirectedRing n) (a : Fin n) (C : Fin n→Q) :=
  fun i => C (unrotateIndex ring a i)
theorem rotateConfig_unrotateConfig {n : Nat} {Q : Type} (ring : DirectedRing n) (a : Fin n) (C : Fin n→Q) :
    rotateConfig ring a (unrotateConfig ring a C)=C := by funext i; exact congrArg C (unrotateIndex_rotateIndex ring a i)
theorem unrotateConfig_rotateConfig {n : Nat} {Q : Type} (ring : DirectedRing n) (a : Fin n) (C : Fin n→Q) :
    unrotateConfig ring a (rotateConfig ring a C)=C := by funext i; exact congrArg C (rotateIndex_unrotateIndex ring a i)
theorem rotate_step {n : Nat} (P : PopulationProtocol) (ring : DirectedRing n)
    (a : Fin n) (C : P.Configuration n) (e : Fin n) :
    P.step ring (rotateConfig ring a C) e=rotateConfig ring a (P.step ring C (rotateIndex ring a e)) := by
  funext i
  unfold PopulationProtocol.step rotateConfig
  dsimp only
  rw [← rotateIndex_rightNeighbor]
  by_cases hie : i=e
  · subst i; simp
  · have hri : rotateIndex ring a i≠rotateIndex ring a e := fun h => hie (rotateIndex_inj ring a i e h)
    by_cases hij : i=ring.rightNeighbor e
    · subst i
      simp only [if_neg hie,if_neg hri]
    · have hrj : rotateIndex ring a i≠rotateIndex ring a (ring.rightNeighbor e) := fun h => hij (rotateIndex_inj ring a i _ h)
      simp only [if_neg hie,if_neg hij,if_neg hri,if_neg hrj]
theorem unrotate_step {n : Nat} (P : PopulationProtocol) (ring : DirectedRing n)
    (a : Fin n) (C : P.Configuration n) (e : Fin n) :
    unrotateConfig ring a (P.step ring C e)=P.step ring (unrotateConfig ring a C) (rotateIndex ring a e) := by
  have h := rotate_step P ring a (unrotateConfig ring a C) e
  rw [rotateConfig_unrotateConfig ring a C] at h
  have hh := congrArg (unrotateConfig ring a) h
  simpa only [unrotateConfig_rotateConfig ring a (P.step ring (unrotateConfig ring a C) (rotateIndex ring a e))] using hh
theorem unrotate_reachable {n : Nat} (P : PopulationProtocol) (ring : DirectedRing n)
    (a : Fin n) {C D : P.Configuration n} (h : PopulationProtocol.Reachable P ring C D) :
    PopulationProtocol.Reachable P ring (unrotateConfig ring a C) (unrotateConfig ring a D) := by
  induction h with
  | refl => exact PopulationProtocol.Reachable.refl (P:=P) (ring:=ring) _
  | step D F h hstep ih =>
    obtain ⟨e,rfl⟩ := hstep
    exact PopulationProtocol.Reachable.step _ _ _ ih ⟨rotateIndex ring a e,unrotate_step P ring a D e⟩

/-- Arbitrary physical anchor version of incoming label normalization. Only the
anchor itself may retain a nonzero label; no shield assumption is used. -/
theorem reaches_other_zero {ψ n : Nat} (hp : ψ>0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) (a : Fin n)
    (ha : (C a).leader=true) :
    ∃ D, PopulationProtocol.Reachable (protocol hp κ) ring C D ∧
      (D a).leader=true ∧ (D a).label=(C a).label ∧
      ∀ i : Fin n, i≠a → (D i).leader=true → (D i).label.val=0 := by
  have har : (rotateConfig ring a C ⟨0,ring.hn⟩).leader=true := by simpa only [rotateConfig,rotateIndex_zero] using ha
  obtain ⟨D,hr,hd,hlab,hz⟩ := reaches_nonroot_zero hp κ ring (rotateConfig ring a C) har
  refine ⟨unrotateConfig ring a D,?_,?_,?_,?_⟩
  · have hh := unrotate_reachable (protocol hp κ) ring a hr
    simpa only [unrotateConfig_rotateConfig] using hh
  · have hz0 : unrotateIndex ring a a=⟨0,ring.hn⟩ := by
      have hh := unrotateIndex_rotateIndex ring a ⟨0,ring.hn⟩
      simpa only [rotateIndex_zero] using hh
    simpa only [unrotateConfig,hz0] using hd
  · have hz0 : unrotateIndex ring a a=⟨0,ring.hn⟩ := by
      have hh := unrotateIndex_rotateIndex ring a ⟨0,ring.hn⟩
      simpa only [rotateIndex_zero] using hh
    simpa only [unrotateConfig,rotateConfig,hz0,rotateIndex_zero] using hlab
  · intro i hia hl
    have hi : 0<(unrotateIndex ring a i).val := by
      by_cases h0 : (unrotateIndex ring a i).val=0
      · have he : unrotateIndex ring a i=⟨0,ring.hn⟩ := Fin.ext h0
        have hh := congrArg (rotateIndex ring a) he
        rw [rotateIndex_unrotateIndex,rotateIndex_zero] at hh
        exact False.elim (hia hh)
      · omega
    exact hz _ hi hl

/-- Phase A from an arbitrary positive configuration: actual incoming edges
reach a singleton or normalize every leader label to zero. This theorem does
not produce a shield and is not the complete gateway. -/
theorem reaches_singleton_or_allzero {ψ n : Nat} (hp : ψ>0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hpos : ∃ a, (C a).leader=true) :
    ∃ D, PopulationProtocol.Reachable (protocol hp κ) ring C D ∧
      ((∃ a, (D a).leader=true ∧ ∀ i, (D i).leader=true → i=a) ∨
       ((∃ a, (D a).leader=true) ∧ ∀ i, (D i).leader=true → (D i).label.val=0)) := by
  classical
  obtain ⟨a,ha⟩ := hpos
  obtain ⟨D,hr,hd,hlab,hz⟩ := reaches_other_zero hp κ ring C a ha
  by_cases hex : ∃ b, b≠a ∧ (D b).leader=true
  · obtain ⟨b,hba,hb⟩ := hex
    have hb0 := hz b hba hb
    obtain ⟨F,hDF,hFb,hFL,hFz⟩ := reaches_other_zero hp κ ring D b hb
    refine ⟨F,hr.trans hDF,Or.inr ⟨⟨b,hFb⟩,?_⟩⟩
    intro i hi
    by_cases hib : i=b
    · subst i
      exact (congrArg Fin.val hFL).trans hb0
    · exact hFz i hib hi
  · refine ⟨D,hr,Or.inl ⟨a,hd,?_⟩⟩
    intro i hi
    by_cases hia : i=a
    · exact hia
    · exact False.elim (hex ⟨i,hia,hi⟩)

#print axioms rotate_step
#print axioms unrotate_reachable
#print axioms reaches_nonroot_zero
#print axioms reaches_other_zero
#print axioms reaches_singleton_or_allzero
end PPLLAstraGateway
