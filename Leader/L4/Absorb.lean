import Leader.L4.Closure
import Leader.L4.RankRootless

/-! Deterministic endpoint of the paper's lem:last-leader, lem:full-closure and
thm:absorb. Stochastic time estimates are not used in this module. -/
namespace L4.Absorb
open TaggedTail

private theorem sSucc {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun j : Fin n => f j.succ) := by
  simp [sumEdge, List.ofFn_succ]

private theorem one_mark_aux {n : Nat} (f : Fin n → Bool)
    (h : sumEdge (fun i => (f i).toNat) = 1) :
    ∃ e : Fin n, ∀ j : Fin n, f j = true ↔ j = e := by
  induction n with
  | zero => simp [sumEdge] at h
  | succ n ih =>
    rw [sSucc] at h
    cases hf : f 0
    · have hTail : sumEdge (fun i : Fin n => (f i.succ).toNat) = 1 := by simpa [hf] using h
      obtain ⟨e,he⟩ := ih (fun i => f i.succ) hTail
      refine ⟨e.succ,?_⟩
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp [hf,Ne.symm (Fin.succ_ne_zero e)]
      · simpa using he k
    · have hTail : sumEdge (fun i : Fin n => (f i.succ).toNat) = 0 := by
        simp only [hf,Bool.toNat_true] at h
        omega
      have allZero {m : Nat} (g : Fin m → Bool)
          (hg : sumEdge (fun i => (g i).toNat) = 0) : ∀ i, g i = false := by
        induction m with
        | zero => exact fun i => i.elim0
        | succ m ih' =>
          rw [sSucc] at hg
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · cases hz : g 0 <;> simp_all
          · exact ih' (fun j => g j.succ) (by omega) j
      refine ⟨0,?_⟩
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp [hf]
      · simp [allZero (fun k => f k.succ) hTail k,Fin.succ_ne_zero]

/-- Exact single incoming mark, without any assumption about the
residues, shields or timer bytes. -/
theorem rank_one_unique_mark {p c n : Nat} (x : Config p c n)
    (h : RankPhysical.rank x = 1) :
    ∃ e : Fin n, ∀ j : Fin n, (x j).mark = true ↔ j = e :=
  one_mark_aux (fun j => (x j).mark) h

theorem not_rootless_has_leader {p c n : Nat} {x : Config p c n}
    (h : ¬ RankRootless.NoLiving x) : ∃ r, (x r).leader = true := by
  classical
  by_cases he : ∃ r, (x r).leader = true
  · exact he
  · exact False.elim (h (fun i => Bool.eq_false_iff.mpr (fun hi => he ⟨i,hi⟩)))

private theorem right_inj {n : Nat} {a b : Fin n}
    (h : rightNeighbor a = rightNeighbor b) : a = b := by
  have hp := congrArg RearTrace.predecessor h
  simpa only [RearTrace.predecessor_right] using hp

/-- This is the literal bridge from reaching one living identity to the
root-peaceful terminal invariant already proved closed under all words. -/
theorem singleton_live_terminal {p c n : Nat} (x : Config p c n)
    (hq : QuietEntrance x) (hr : RankPhysical.rank x = 1)
    (hl : ¬ RankRootless.NoLiving x) : ∃ r, TerminalAt x r := by
  obtain ⟨e,he⟩ := rank_one_unique_mark x hr
  obtain ⟨z,hz⟩ := not_rootless_has_leader hl
  let r := rightNeighbor e
  have hFind : ∀ j, (x j).leader = true → j = r := by
    intro j hj
    let u := RearTrace.predecessor j
    have hU : rightNeighbor u = j := RearTrace.right_predecessor j
    have hm := hq.1 u (Or.inl (hU.symm ▸ hj))
    exact hU.symm.trans (congrArg rightNeighbor ((he u).mp hm))
  have hL : (x r).leader = true := hFind z hz ▸ hz
  refine ⟨r,?_,?_,?_,?_,?_⟩
  · intro j
    exact ⟨hFind j,fun hj => hj.symm ▸ hL⟩
  · intro u
    exact ⟨fun hu => congrArg rightNeighbor ((he u).mp hu),
      fun hu => (he u).mpr (right_inj hu)⟩
  · intro u hu
    by_cases hResidue : (x (rightNeighbor u)).residue = nextResidue (x u).residue
    · exact hResidue
    · exact False.elim (hu (congrArg rightNeighbor ((he u).mp (hq.1 u (Or.inr hResidue)))))
  · intro j hj
    let u := RearTrace.predecessor j
    have hU : rightNeighbor u = j := RearTrace.right_predecessor j
    obtain ⟨hL',hM⟩ := hq.2.1 u (hU.symm ▸ hj)
    exact ⟨hU ▸ hL',u,hU,hM⟩
  · intro d hd hB
    have hp : RootPeacefulAt x (liftedSite r d) := hq.2.2.2 _ hB
    obtain ⟨u,k,hk,hm,hl',hs,hcarrier,_,hzero⟩ := hp
    have hEq : u = e := (he u).mp hm
    subst u
    have hkinj : k = d := liftedSite_inj r hk hd hcarrier
    subst k
    exact ⟨hs,hzero⟩

/-- A singleton ghost in the paper's entrance class cannot carry any
live bullets anywhere. This rules out an old live killer on its birth
mark without imposing a cleanliness predicate on dummy bullets. -/
theorem rootless_quiet_no_live {p c n : Nat} (x : Config p c n)
    (hq : QuietEntrance x) (hl : RankRootless.NoLiving x) :
    ∀ j, (x j).bullet ≠ .live := by
  intro j hj
  obtain ⟨u,d,_,_,hL,_,_,_,_⟩ := hq.2.2.2 j hj
  rw [hl (rightNeighbor u)] at hL
  contradiction

/-- Literal succinct success predicate used by the singleton clock. -/
def SingletonLive {p c n : Nat} (x : Config p c n) : Prop :=
  QuietEntrance x ∧ RankPhysical.rank x = 1 ∧ ¬ RankRootless.NoLiving x

/-- The paper's concrete forward-closed target, more informative than
merely displaying one leader on the present mark. -/
def Absorbing {p c n : Nat} (x : Config p c n) : Prop :=
  ∃ r, TerminalAt x r

theorem absorbing_of_singleton_live {p c n : Nat} {x : Config p c n}
    (hx : SingletonLive x) : Absorbing x :=
  singleton_live_terminal x hx.1 hx.2.1 hx.2.2

theorem absorbing_run {p c n : Nat} (hn : 4 ≤ n) {x : Config p c n}
    (hx : Absorbing x) (w : List (Fin n)) : Absorbing (run x w) := by
  obtain ⟨r,hr⟩ := hx
  exact ⟨r,terminalAt_run hn x r w hr⟩

theorem absorbing_safe {p c n : Nat} (hn : 4 ≤ n) {x : Config p c n}
    (hx : Absorbing x) : SafeOneLeader x := by
  obtain ⟨r,hr⟩ := hx
  exact terminalAt_safeOneLeader hn x r hr

theorem singleton_live_safe {p c n : Nat} (hn : 4 ≤ n) {x : Config p c n}
    (hx : SingletonLive x) : SafeOneLeader x :=
  absorbing_safe hn (absorbing_of_singleton_live hx)

private theorem distinct {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro he
  have hh : liftedSite e 1 = liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using he
  have hh' := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) hh
  omega

/-- On the terminal class no physical mark can take the P3 branch.
Even its unique marked responder retains its living status. -/
theorem terminal_no_payment {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (r e : Fin n) (h : TerminalAt x r) :
    geometricPay (x e) (x (rightNeighbor e)) = false := by
  have hCover : MCOV x := by
    intro u hM
    apply (h.2.1 u).mpr
    rcases hM with hLeader | hResidue
    · exact (h.1 _).mp hLeader
    · by_cases hEq : rightNeighbor u = r
      · exact hEq
      · exact False.elim (hResidue (h.2.2.1 u hEq))
  apply Bool.eq_false_iff.mpr
  intro hpay
  have hMarked := RearTrace.paid_was_marked hCover e hpay
  have hRoot := (h.2.1 e).mp hMarked
  have hSurvives := ((terminalAt_step hn x r e h).1 (rightNeighbor e)).mpr hRoot
  have hFalse := TaggedTrace.geometricPay_responder_nonleader _ _ hpay
  have hTrue : (pairStep (x e) (x (rightNeighbor e))).2.leader = true := by
    simpa [step,distinct hn e] using hSurvives
  rw [hFalse] at hTrue
  contradiction

/-- The exact literal public geometry is fixed along every continuation.
Stock, patrol rail, signal and bullet scratch need not be constant. -/
theorem terminal_geometry_run {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (r : Fin n) (w : List (Fin n)) (h : TerminalAt x r) :
    ∀ u, (run x w u).mark = (x u).mark ∧ (run x w u).residue = (x u).residue ∧
      (run x w u).source = .off := by
  induction w generalizing x with
  | nil => intro u; exact ⟨rfl,rfl,terminalAt_source_off h u⟩
  | cons e w ih =>
    have hkeep := terminalAt_step hn x r e h
    have hd := terminal_no_payment hn x r e h
    intro u
    obtain ⟨hm,hres,hs⟩ := ih (step x e) hkeep u
    change (run (step x e) w u).mark = _ ∧ (run (step x e) w u).residue = _ ∧ _
    refine ⟨hm.trans ?_,hres.trans ?_,hs⟩
    · rw [covered_step_mark hn x (show MCOV x from by
        intro v hv; apply (h.2.1 v).mpr
        rcases hv with hl | hd
        · exact (h.1 _).mp hl
        · by_cases he : rightNeighbor v = r
          · exact he
          · exact False.elim (hd (h.2.2.1 v he)))]
      simp [hd]
    · by_cases hu : u=e
      · subst u
        simpa [step] using (pair_geometric_fields (x e) (x (rightNeighbor e))).1
      · by_cases hv : u=rightNeighbor e
        · subst u
          simpa [step,distinct hn e,hd] using (pair_geometric_fields (x e) (x (rightNeighbor e))).2.2
        · simp [step,hu,hv]

private theorem sSelector {n : Nat} (i : Fin n) :
    sumEdge (fun e => if e = i then 1 else 0) = 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [sSucc]
      have hz : (fun e : Fin n => if e.succ = (0 : Fin (n+1)) then 1 else 0) =
          (fun _ : Fin n => 0) := by funext e; simp [Fin.succ_ne_zero]
      rw [hz]
      have hz0 (m : Nat) : sumEdge (fun _ : Fin m => 0) = 0 := by
        induction m with
        | zero => rfl
        | succ m ihm => rw [sSucc,ihm,Nat.zero_add]
      rw [hz0,Nat.add_zero]; rfl
    · rw [sSucc, if_neg (Ne.symm (Fin.succ_ne_zero j))]
      have hc : (fun e : Fin n => if e.succ = j.succ then 1 else 0) =
          (fun e : Fin n => if e = j then 1 else 0) := by funext e; simp
      rw [hc,ih,Nat.zero_add]

/-- No additional semantic hypothesis is hidden in the terminal
target: it is exactly rank-one living root-peaceful entrance. -/
theorem singleton_live_of_absorbing {p c n : Nat} {x : Config p c n}
    (h : Absorbing x) : SingletonLive x := by
  obtain ⟨r,hr⟩ := h
  let e := RearTrace.predecessor r
  have he : rightNeighbor e = r := RearTrace.right_predecessor r
  have hm : (x e).mark = true := (hr.2.1 e).mpr he
  have hRank : RankPhysical.rank x = 1 := by
    have hh : (fun u => (x u).mark.toNat) = fun u => if u=e then 1 else 0 := by
      funext u
      by_cases hu : u=e
      · subst u; simp [hm]
      · have hf : (x u).mark = false := Bool.eq_false_iff.mpr
          (fun hM => hu (right_inj (((hr.2.1 u).mp hM).trans he.symm)))
        simp [hu,hf]
    rw [RankPhysical.rank,hh]
    exact sSelector e
  refine ⟨⟨?_,?_,⟨e,hm⟩,?_⟩,hRank,?_⟩
  · intro u hu
    apply (hr.2.1 u).mpr
    rcases hu with hl | hd
    · exact (hr.1 _).mp hl
    · by_cases hEq : rightNeighbor u = r
      · exact hEq
      · exact False.elim (hd (hr.2.2.1 u hEq))
  · intro u hOff
    exact False.elim (hOff (terminalAt_source_off hr _))
  · intro u hBullet
    obtain ⟨d,hd,hu⟩ := liftedSite_of_site r u
    have hb : (x (liftedSite r d)).bullet = .live := hu.symm ▸ hBullet
    obtain ⟨hS,hZ⟩ := hr.2.2.2.2 d hd hb
    refine ⟨e,d,hd,hm,(hr.1 _).mpr he,he.symm ▸ hS,?_,?_,?_⟩
    · rw [he]; exact hu
    · intro j hj
      apply Bool.eq_false_iff.mpr
      intro hM
      have hEq := (hr.2.1 (liftedSite (rightNeighbor e) j)).mp hM
      rw [he,← liftedSite_succ] at hEq
      have hContra := liftedSite_inj r (by omega : j+1<n) (by omega : 0<n) (hEq.trans (liftedSite_zero r).symm)
      omega
    · intro j hj
      rw [he]; exact hZ j hj
  · intro hNo
    have hL := (hr.1 r).mpr rfl
    simp [hNo r] at hL

/-- Bare rank one plus a living bit is not sufficient: an old unprotected
live bullet can delete the sole leader. This n=4,p=3 fixture has one
correct incoming mark but is outside the quiet entrance class. -/
def unprotected4 : Config 3 12 4 := fun i =>
  { residue := if i.val = 3 then 0 else ⟨i.val%3, Nat.mod_lt _ (by decide)⟩
    mark := i.val == 3
    leader := i.val == 0
    stock := false
    shield := false
    signal := .zero
    bullet := if i.val = 3 then .live else .none
    source := .off
    rail := .e }

theorem unprotected4_replay :
    RankPhysical.rank unprotected4 = 1 ∧
    (unprotected4 0).leader = true ∧
    (∀ i : Fin 4, (step unprotected4 3 i).leader = false) := by decide

end L4.Absorb
