import Leader.L4.WindowProtectedMass

/-! Authenticate the named victim at its post-N2/P3 slot. -/
namespace L4.WindowProtectedEntry
open SevenTagCharge RankSupplier RankPhysical WindowProtectedMass

attribute [local irreducible] WindowLocal.route

theorem named_kill_entry {p c n d : Nat} {z0 : Config p c n} (hn : 4≤n)
    (z : Ledger p c n) (group cert : List (Fin n)) (target : Option (Fin n))
    (s a e post : Fin n) (hV : Valid z z0) (hq : QuietEntrance z.config)
    (hSub : cert ⊆ group) (hA : a ∈ cert) (hSlot : z.slots e=some a)
    (hR : WindowLocal.route group cert target z e=.prefixDeath a post)
    (hD : WindowLocal.nativeDeath z.config e=true)
    (hM : (z.config s).mark=true) (hL : (z.config (rightNeighbor s)).leader=true)
    (hE : e=liftedSite (rightNeighbor s) d) (hcap : d+1<n)
    (hBefore : ∀ i, i<d → (z.config (liftedSite (rightNeighbor s) i)).mark=false) :
    let v := rightNeighbor s
    let newD := d+(geometricPay (z.config e) (z.config (rightNeighbor e))).toNat
    Authenticated z0 v a newD ⟨SevenTagCharge.advance z e,[]⟩ ∧
    post=liftedSite v (newD+1) := by
  let x := z.config
  let v := rightNeighbor s
  let pay := geometricPay (x e) (x (rightNeighbor e))
  have hK := (WindowLocal.nativeDeath_iff x e).mp hD
  have hNE : rightNeighbor e≠e := by
    intro he
    have h := liftedSite_inj e (show 1<n by omega) (show 0<n by omega)
      (show liftedSite e 1=liftedSite e 0 by simpa [liftedSite_succ,liftedSite_zero] using he)
    omega
  have hOld := hK.1
  have hKill := (TenureOrigins.covered_ring_leader_loss_iff x e hNE hV.sourceCover hOld).mpr hK
  have ht : liftedSite v (d+1)=rightNeighbor e := by rw [liftedSite_succ,←hE]
  have hNo : retirement x e=false := by
    apply Bool.eq_false_iff.mpr
    intro hRe
    have hGone : lostStep x z.slots e=some a := by simp [lostStep,hRe,hSlot]
    have hRw := (WindowLocal.reward_iff group cert target z e a).mpr ⟨hGone,hSub hA⟩
    rw [hR] at hRw
    cases hRw
  have hF : FirstMark x v d := by
    refine ⟨by omega,?_,?_⟩
    · rw [←hE]; exact hV.markCover e (.inl hOld)
    · intro i hi H
      have K := hBefore i hi
      rw [H] at K
      cases K
  obtain ⟨i,b,k,hB,hS,hkn,hk,hNoMark,hKind⟩ :=
    WindowLocal.killing_shooter_pre_mark hn z e hq hV.covers hD
  have hI : (x i).mark=true := by simpa [hB] using (hV.covers i).symm
  obtain ⟨hIS,hKD⟩ := WindowLocal.nearest_shooting_root_unique x i s k d hI hM
    (hk.trans hE) hNoMark hBefore
  rw [hIS,hKD] at hKind
  have hShield : (step x e v).shield=true := by
    rcases hKind with ⟨h0,hFire⟩ | ⟨hs,_⟩
    · have he : e=v := by simpa only [h0,liftedSite_zero] using hE
      rw [he] at hFire ⊢
      simpa [step] using (fresh_firing_shields (x v) (x (rightNeighbor v)) hFire).2
    · by_cases hh : v=e
      · simpa [step,hh] using (RankFresh.outgoing_leader_shield (x e) (x (rightNeighbor e))
          (hh ▸ hs)).2
      · have hnr : v≠rightNeighbor e := by
          intro h
          have eq : liftedSite v 0=liftedSite v (d+1) := (liftedSite_zero v).trans (h.trans ht.symm)
          have bad := liftedSite_inj v (show 0<n by omega) hcap eq
          omega
        simpa [step,hh,hnr] using hs
  have hQuiet : ∀ j, j<d → (x (liftedSite v j)).signal≠.one := by
    intro j hj
    rcases hKind with ⟨h0,_⟩ | ⟨_,hs⟩
    · omega
    · rw [hs j (by omega)]
      decide
  have hp := protected_after_kill_prefix hn x v hV.markCover hV.sourceCover hF hcap hL
    (ht.symm ▸ hOld) (by rw [←hE,ht]; exact hKill)
    (by rwa [←hE]) hQuiet (by rwa [←hE])
  rw [←hE] at hp
  let q := SevenTagCharge.advance z e
  let d' := d+pay.toNat
  have hProtected : Protected v (init q.config d') := hp
  have hAuth : FreshEpochEarly.freshInit q.config v d' := by
    refine ⟨hProtected.2.ghost,?_⟩
    cases hPay : pay with
    | false =>
      have hA := FreshCountHits.unpaid_death_auth_start hn x v
        (by rwa [←hE,ht]) hV.sourceCover (by rwa [←hE,ht])
      have hDD : d'=d := by simp [d',hPay]
      right
      rw [hDD]
      change (step x e (liftedSite v (d+1))).source=.i1 ∧
        FreshEpochAuthentication.Auth (FreshEpochAuthentication.railsAt (step x e) v d)
      rw [hE]
      exact hA
    | true =>
      have hA := FreshTimerEpoch.paid_landing_off hn x e hV.markCover hV.sourceCover hPay hNo
      have hDD : d'=d+1 := by simp [d',hPay]
      have H : liftedSite v (d'+1)=rightNeighbor (rightNeighbor e) := by rw [hDD,liftedSite_succ,ht]
      left
      change (step x e (liftedSite v (d'+1))).source=.off
      rw [H]
      exact hA.1
  have hLand : WindowLocal.landingSlot x e=liftedSite v d' := by
    unfold WindowLocal.landingSlot
    change (if pay then rightNeighbor e else e)=_
    cases hPay : pay
    · simp only [Bool.false_eq_true,if_false]
      have hs : d'=d := by simp [d',hPay]
      rw [hs]; exact hE
    · simp only [if_true]
      have hs : d'=d+1 := by simp [d',hPay]
      rw [hs]; exact ht.symm
  rcases WindowLocal.prefix_death_result group cert target z e a hn hV.markCover hV.sourceCover
      hV.covers hV.unique hSub hSlot hA hD with hBad|hGood
  · have H := hBad.1
    rw [hR] at H
    cases H
  · have hPost : post=rightNeighbor (WindowLocal.landingSlot x e) := by
      have H := hGood.1
      rw [hR] at H
      injection H
    refine ⟨⟨valid_step hn z z0 e hV,hProtected,?_ ,hAuth⟩,?_⟩
    · rw [←hLand]
      exact hGood.2.1
    · rw [hPost,hLand,liftedSite_succ]

#print axioms named_kill_entry
end L4.WindowProtectedEntry
