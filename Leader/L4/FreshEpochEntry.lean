import Leader.L4.FreshEpochEarly
import Leader.L4.FreshSupplierTrack
import Leader.L4.RankSupplierPhysical

namespace L4.FreshEpochEntry
open RankSupplier FreshEpochEarly

private theorem right_ne {n : Nat} (hn : 4≤n) (e : Fin n) : rightNeighbor e≠e := by
  intro h
  have hh : liftedSite e 1=liftedSite e 0 := by
    simpa [liftedSite_succ,liftedSite_zero] using h
  have H := liftedSite_inj e (show 1<n by omega) (show 0<n by omega) hh
  omega

/-- The completed killing mark yields a genuinely fresh initial gap.
If that mark paid a surviving victim, identify its post-mark landing
site. A simultaneously retired mover is excluded by the premise. -/
theorem kill_starts_fresh_epoch {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (e : Fin n) (hq : QuietEntrance x)
    (hLeader : (x (rightNeighbor e)).leader=true)
    (hKilled : (step x e (rightNeighbor e)).leader=false)
    (hRet : RankPhysical.retirement x e=false) :
    ∃ v s, s.config=step x e ∧ Protected v s ∧ freshInit s.config v s.donor := by
  obtain ⟨v,d,he,hP⟩ := peaceful_kill_starts_protected hn x e hq hLeader hKilled hRet
  let pay := geometricPay (x e) (x (rightNeighbor e))
  let s := init (step x e) (d+pay.toNat)
  refine ⟨v,s,rfl,hP,?_⟩
  have hD : s.donor=d+pay.toNat := rfl
  have hk := (TenureOrigins.covered_ring_leader_loss_iff x e (right_ne hn e) hq.2.1 hLeader).mp hKilled
  cases hp : pay
  · have hz : rightNeighbor e=liftedSite v (d+1) := by rw [he,←liftedSite_succ]
    have hh : TenureOrigins.nativeKill (x (liftedSite v d)) (x (liftedSite v (d+1))) := by
      rwa [←he,←hz]
    have hf : geometricPay (x (liftedSite v d)) (x (liftedSite v (d+1)))=false := by
      rw [←he,←hz]
      exact hp
    have hA := FreshCountHits.unpaid_death_auth_start hn x v hh hq.2.1 hf
    have hds : s.donor=d := by simp [hD,hp]
    refine ⟨hP.1.2.2.2.1,Or.inr ?_⟩
    change (step x e (liftedSite v (s.donor+1))).source=.i1 ∧
      FreshEpochAuthentication.Auth (FreshEpochAuthentication.railsAt (step x e) v s.donor)
    rw [hds,he]
    exact hA
  · have hA := FreshTimerEpoch.paid_landing_off hn x e hq.1 hq.2.1 hp hRet
    have hds : s.donor=d+1 := by simp [hD,hp]
    have hz : rightNeighbor (rightNeighbor e)=liftedSite v (s.donor+1) := by
      rw [he,hds,liftedSite_succ,liftedSite_succ]
    refine ⟨hP.1.2.2.2.1,Or.inl ?_⟩
    change (step x e (liftedSite v (s.donor+1))).source=.off
    simpa only [←hz] using hA.1

/-- Every *surviving* paid advance starts a strictly larger gap with
the new physical landing controller OFF. Payment and retirement on
one mark do not produce an epoch at a resident root. -/
theorem paid_starts_fresh_epoch {p c n : Nat} (hn : 4≤n) (v e : Fin n)
    (s : Obs p c n) (hs : Protected v s) (hc : COV s.config)
    (hAlive : (advance v s e).stopped=false)
    (hMove : s.donor < (advance v s e).donor) :
    let t := advance v s e
    t.donor=s.donor+1 ∧ Protected v t ∧ freshInit t.config v t.donor := by
  let t := advance v s e
  let pay := geometricPay (s.config e) (s.config (rightNeighbor e))
  have fields := RankSupplierPhysical.unstopped_fields v e s hs.1.1 hAlive
  have hP := protected_step hn v e s hs hAlive
  have hOn : ((e == liftedSite v s.donor) && pay)=true := by
    cases h : ((e == liftedSite v s.donor) && pay)
    · have hh := fields.2
      change t.donor = s.donor + ((e == liftedSite v s.donor) && pay).toNat at hh
      simp [h] at hh
      change s.donor<t.donor at hMove
      omega
    · rfl
  have hBoth : (e == liftedSite v s.donor)=true ∧ pay=true := by
    simpa only [Bool.and_eq_true] using hOn
  obtain ⟨he,hPay⟩ := hBoth
  have hE : e=liftedSite v s.donor := beq_iff_eq.mp he
  have hD : t.donor=s.donor+1 := by
    have h := fields.2
    change t.donor=s.donor+((e == liftedSite v s.donor) && pay).toNat at h
    simpa [hOn] using h
  have hNot : (pay && (s.config (rightNeighbor e)).mark)=false := by
    unfold advance at hAlive
    simp only [hs.1.1,Bool.false_eq_true,if_false] at hAlive
    split at hAlive
    · contradiction
    · rename_i h
      change ¬ stop s.config (step s.config e) v e
        (s.donor+((e == liftedSite v s.donor)&&pay).toNat) pay = true at h
      have hh := Bool.eq_false_iff.mpr h
      unfold stop at hh
      have hB := (Bool.or_eq_false_iff.mp hh).1
      exact (Bool.or_eq_false_iff.mp hB).1
  have hR : RankPhysical.retirement s.config e=false := hNot
  have hA := FreshTimerEpoch.paid_landing_off hn s.config e hs.1.2.1 hc hPay hR
  have hz : rightNeighbor (rightNeighbor e)=liftedSite v (t.donor+1) := by
    rw [hE,hD,liftedSite_succ,liftedSite_succ]
  refine ⟨hD,hP,hP.1.2.2.2.1,Or.inl ?_⟩
  change (t.config (liftedSite v (t.donor+1))).source=.off
  rw [fields.1,←hz]
  exact hA.1

end L4.FreshEpochEntry

#print axioms L4.FreshEpochEntry.kill_starts_fresh_epoch
#print axioms L4.FreshEpochEntry.paid_starts_fresh_epoch
