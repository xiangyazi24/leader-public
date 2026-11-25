import Leader.L4.TriplePrep

/-! Sealed (prepared) sector phase laws on the literal scheduler. -/
namespace L4.TriplePhase
open TripleResidual TriplePrep

inductive Kind where | dummy | live
  deriving DecidableEq

def Kind.bullet : Kind → Bullet
  | .dummy => .dummy
  | .live => .live

def Kind.shield : Kind → Bool
  | .dummy => false
  | .live => true

structure SealedFront {p c n : Nat}
    (x : Config p c n) (s : Fin n) (d q : Nat) (kind : Kind) : Prop where
  within : q ≤ d
  trail : ZeroFront x s q
  unique : ∀ j, j ≤ d → (x (liftedSite s j)).bullet = if j=q then kind.bullet else .none
  binary : ∀ j, j ≤ d → (x (liftedSite s j)).signal ≠ .two
  shield : (x s).shield = kind.shield

def Ready {p c n : Nat} (x : Config p c n) (s : Fin n) (d : Nat) : Prop := ReturnFront x s d 0

private theorem sectorOrd {p c n d : Nat} (x : Config p c n) (s : Fin n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d) {j : Nat} (hj : j < d) :
    (x (liftedSite s j)).mark = false ∧
    (x (rightNeighbor (liftedSite s j))).residue = nextResidue (x (liftedSite s j)).residue ∧
    (x (rightNeighbor (liftedSite s j))).leader = false := by
  have h := coveredOrdinary hc ((covered_noRoot_iff hm).mpr
    (Bool.eq_false_iff.mpr (hF.before j hj)))
  exact ⟨h.1,h.2.1,h.2.2.1⟩

private theorem separate {n : Nat} (hn : 4≤n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have he : liftedSite e 1 = liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hh := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) he
  omega

private theorem right_snap {p c n : Nat} (hn : 4≤n) (x : Config p c n) (e : Fin n) :
    step x e (rightNeighbor e) = (pairStep (x e) (x (rightNeighbor e))).2 := by
  simp [step,separate hn e]

private theorem safe_responder {p c n : Nat} (x : Config p c n) (e : Fin n)
    (hv : (x (rightNeighbor e)).leader = true) (hE : event x e = false) :
    (fireInitiator (x e)).bullet ≠ .live ∨ (fireResponder (x (rightNeighbor e))).shield = true := by
  have hD := (Bool.or_eq_false_iff.mp hE).1
  by_cases hB : (fireInitiator (x e)).bullet = .live
  · right
    cases hh : (fireResponder (x (rightNeighbor e))).shield
    · have hk := (death_iff_nativeKill x e).mpr ⟨hv,hB,hh⟩
      rw [hD] at hk
      cases hk
    · rfl
  · exact .inl hB

private theorem shield_follower {p c : Nat} (u v : Site p c)
    (hm : u.mark=false) (hr : v.residue=nextResidue u.residue) (hv : v.leader=false) :
    (pairStep u v).1.shield = (fireInitiator u).shield ∧ (pairStep u v).2.shield = v.shield := by
  have h := ordinary_native_payload u v hm hr hv
  have A := congrArg (fun a => (a.2.2.1,a.2.2.2.2.2.1)) h
  simp only [Prod.mk.injEq] at A
  generalize e : fireInitiator u = a at A
  have hm' : a.mark=false := by
    rw [← e]; unfold fireInitiator; split <;> exact hm
  cases hb : a.bullet <;> simp [native,e,hv,impact,fireResponder,pinned,hm',followerBullet,hb] at A
  · exact A
  · exact A
  · exact A

private theorem binary_max {u v : Signal} (hu : u≠.two) (hv : v≠.two) :
    Signal.max u v ≠ .two := by cases u <;> cases v <;> simp_all [Signal.max]

private theorem binary_one (u : Signal) (h : u≠.two) : Signal.max u .one=.one := by
  cases u <;> simp_all [Signal.max]

private theorem source_zero {p c n d q : Nat} {x : Config p c n} {s : Fin n} {k : Kind}
    (h : SealedFront x s d q k) : (x s).signal=.zero := by
  by_cases hq : q=0
  · simpa [hq,liftedSite_zero] using h.trail.signal
  · simpa [liftedSite_zero] using (h.trail.swept 0 (Nat.pos_of_ne_zero hq)).1

private theorem source_fire_identity {p c : Nat} (u : Site p c)
    (h : u.leader=false ∨ u.signal=.zero) : fireInitiator u = u := by
  rcases h with h|h <;> simp [fireInitiator,h]

private theorem front_bullet_nonempty (k : Kind) : k.bullet≠.none := by cases k <;> decide

/-- Every initial READY incoming orientation really produces a unique
dummy at the physical source, with its shield off. On a lethal incoming
impact this continuing premise is false (the stop is on that same mark). -/
theorem ready_incoming {p c n d : Nat} (hn : 4≤n) (x : Config p c n) (s e : Fin n)
    (bd : d+1<n) (hR : rightNeighbor e=s) (hL : (x s).leader=true)
    (h : Ready x s d) (he : event x e=false) :
    SealedFront (step x e) s d 0 .dummy := by
  have hs : (x s).signal=.one := by simpa [liftedSite_zero] using h.one
  have hh := sourceIncoming_starts_front hn x e s hR hL (by rw [hs]; decide) he
  have hp : (step x e s).bullet=.dummy ∧ (step x e s).shield=false := by
    simpa [hs] using hh.2
  refine ⟨Nat.zero_le _,hh.1,?_,?_,hp.2⟩
  · intro j hj
    by_cases hz : j=0
    · subst j; simpa [liftedSite_zero,Kind.bullet] using hp.1
    · have hV : liftedSite s j≠rightNeighbor e := by
        rw [hR]
        intro H
        have eq := liftedSite_inj s (by omega : j<n) (by omega : 0<n) (H.trans (liftedSite_zero s).symm)
        exact hz eq
      have hE : liftedSite s j≠e := by
        intro H
        have eq : liftedSite s (j+1)=liftedSite s 0 := by rw [liftedSite_succ,H,hR,liftedSite_zero]
        have eq' := liftedSite_inj s (by omega : j+1<n) (by omega : 0<n) eq
        omega
      simpa [step,hE,hV,hz] using h.empty j hj
  · intro j hj
    by_cases hz : j=0
    · subst j; simp [hh.1.signal]
    · have hV : liftedSite s j≠rightNeighbor e := by
        rw [hR]
        intro H
        exact hz (liftedSite_inj s (by omega : j<n) (by omega : 0<n) (H.trans (liftedSite_zero s).symm))
      have hE : liftedSite s j≠e := by
        intro H
        have eq : liftedSite s (j+1)=liftedSite s 0 := by rw [liftedSite_succ,H,hR,liftedSite_zero]
        have eq' := liftedSite_inj s (by omega : j+1<n) (by omega : 0<n) eq
        omega
      simpa [step,hE,hV] using h.binary j hj

private theorem lead_boundary {p c n d : Nat} (x : Config p c n) (s : Fin n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (_hT : (x (liftedSite s (d+1))).leader=true)
    (hz : (x s).signal=.zero) (j : Nat) (hj : j≤d) :
    (x (liftedSite s j)).leader=false ∨ (x (liftedSite s j)).signal=.zero := by
  cases j with
  | zero => exact .inr (by simpa [liftedSite_zero] using hz)
  | succ j =>
    have h := sectorOrd x s hm hc hF (show j<d by omega)
    left
    simpa [liftedSite_succ] using h.2.2

/-- Source shield remains unchanged throughout a zero-signal front or
return, provided the actual selected mark does not end the trial. -/
theorem zero_source_shield {p c n d : Nat} (hn : 4≤n) (x : Config p c n) (s e : Fin n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hL : (x s).leader=true) (hT : (x (liftedSite s (d+1))).leader=true)
    (hz : (x s).signal=.zero) (he : event x e=false) :
    (step x e s).shield=(x s).shield := by
  by_cases hh : s=e
  · subst e
    have hi := source_fire_identity (x s) (.inr hz)
    by_cases hd : d=0
    · subst d
      have hR : (x (rightNeighbor s)).leader=true := by
        simpa [liftedSite_succ,liftedSite_zero] using hT
      have h := surviving_terminal (x s) (x (rightNeighbor s)) hR (safe_responder x s hR he)
      simpa [step,hi] using h.2.2.1
    · have hh := sectorOrd x s hm hc hF (show 0<d by omega)
      rw [liftedSite_zero] at hh
      have h := shield_follower _ _ hh.1 hh.2.1 hh.2.2
      simpa [step,hi] using h.1
  · by_cases hS : s=rightNeighbor e
    · have hR : (x (rightNeighbor e)).leader=true := hS ▸ hL
      have hZ : (x (rightNeighbor e)).signal=.zero := hS ▸ hz
      have H := surviving_terminal (x e) (x (rightNeighbor e)) hR (safe_responder x e hR he)
      rw [hS,right_snap hn]
      simpa [fireResponder,hR,hZ] using H.2.2.2.2.2.1
    · simp [step,hh,hS]

/-- Away from the sole nominated forward bond the prepared front
cannot be overwritten, and no other bullet or colour two appears. -/
theorem sealed_wait_payload {p c n d q : Nat} (hn : 4≤n) (x : Config p c n) (s e : Fin n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hL : (x s).leader=true) (hT : (x (liftedSite s (d+1))).leader=true)
    (kind : Kind) (h : SealedFront x s d q kind)
    (he : event x e=false) (hw : e ≠ liftedSite s q) (j : Nat) (hj : j≤d) :
    (step x e (liftedSite s j)).bullet=(x (liftedSite s j)).bullet ∧
      (step x e (liftedSite s j)).signal≠.two := by
  have hz := source_zero h
  have quiet (i : Nat) (hi : i≤d) := lead_boundary x s hm hc hF hT hz i hi
  have noneAt (i : Nat) (hi : i≤d) (hI : i≠q) :
      (x (liftedSite s i)).bullet=.none := by rw [h.unique i hi,if_neg hI]
  by_cases hl : liftedSite s j=e
  · have hJ : j≠q := by intro H; subst j; exact hw hl.symm
    rw [← hl]
    have hb := noneAt j hj hJ
    by_cases hd : j=d
    · subst j
      have hR : (x (rightNeighbor (liftedSite s d))).leader=true := by
        simpa [liftedSite_succ] using hT
      have HH := surviving_terminal _ _ hR (safe_responder x (liftedSite s d) hR (hl.symm ▸ he))
      have hi := source_fire_identity _ (quiet d hj)
      rw [hi] at HH
      simp [step,HH.1,HH.2.1,hb,binary_one _ (h.binary d hj)]
    · have H := sectorOrd x s hm hc hF (show j<d by omega)
      have HH := ordinary_empty_donor _ _ H.1 H.2.1 H.2.2 hb (quiet j hj)
      have sb := binary_max (h.binary j hj)
        (show (x (rightNeighbor (liftedSite s j))).signal≠.two by
          rw [← liftedSite_succ]
          exact h.binary (j+1) (by omega))
      simp [step,HH.1,HH.2.1,hb,sb]
  · by_cases hr : liftedSite s j=rightNeighbor e
    · cases j with
      | zero =>
        have hR : rightNeighbor e=s := by simpa [liftedSite_zero] using hr.symm
        have hV : (x (rightNeighbor e)).leader=true := hR.symm ▸ hL
        have hZ : (x (rightNeighbor e)).signal=.zero := hR.symm ▸ hz
        have HH := surviving_terminal _ _ hV (safe_responder x e hV he)
        have hh : fireResponder (x (rightNeighbor e))=x (rightNeighbor e) := by
          simp [fireResponder,hV,hZ]
        rw [hh] at HH
        rw [hr,right_snap hn]
        exact ⟨HH.2.2.2.1,by rw [HH.2.2.2.2.1,hZ]; decide⟩
      | succ i =>
        have hE : liftedSite s i=e := FreshSeparation.succ_inj (by simpa [liftedSite_succ] using hr)
        have hI : i≠q := by intro H; subst i; exact hw hE.symm
        have ho := sectorOrd x s hm hc hF (show i<d by omega)
        have hh := ordinary_empty_donor _ _ ho.1 ho.2.1 ho.2.2 (noneAt i (by omega) hI) (quiet i (by omega))
        have H : (pairStep (x e) (x (rightNeighbor e))).2.bullet=(x (rightNeighbor e)).bullet ∧
            (pairStep (x e) (x (rightNeighbor e))).2.signal=(x (rightNeighbor e)).signal := by
          rw [← hE]
          exact ⟨hh.2.2.1,hh.2.2.2⟩
        rw [hr,right_snap hn]
        refine ⟨H.1,?_⟩
        rw [H.2,← hr]
        exact h.binary (i+1) hj
    · simp [step,hl,hr,h.binary j hj]

/-- Exact nonnominated closure of all four prepared-front coordinates. -/
theorem sealed_front_wait {p c n d q : Nat} (hn : 4≤n) (x : Config p c n) (s e : Fin n)
    (bd : d+1<n) (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hL : (x s).leader=true) (hT : (x (liftedSite s (d+1))).leader=true)
    (kind : Kind) (h : SealedFront x s d q kind) (he : event x e=false)
    (hw : e ≠ liftedSite s q) :
    SealedFront (step x e) s d q kind := by
  have snap := sealed_wait_payload hn x s e hm hc hF hL hT kind h he hw
  exact ⟨h.within,zeroFront_wait hn x s e hm hc hF bd hL h.within h.trail he hw,
    fun j hj => (snap j hj).1.trans (h.unique j hj),fun j hj => (snap j hj).2,
    (zero_source_shield hn x s e hm hc hF hL hT (source_zero h) he).trans h.shield⟩

/-- The nominated forward edge transports precisely the old prepared
bullet. This is stronger than the dirty-sweep collision observer. -/
theorem sealed_front_progress {p c n d q : Nat} (hn : 4≤n) (x : Config p c n) (s : Fin n)
    (bd : d+1<n) (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hL : (x s).leader=true) (hT : (x (liftedSite s (d+1))).leader=true)
    (kind : Kind) (h : SealedFront x s d q kind) (hq : q<d)
    (he : event x (liftedSite s q)=false) :
    SealedFront (step x (liftedSite s q)) s d (q+1) kind := by
  let e := liftedSite s q
  have ho := sectorOrd x s hm hc hF hq
  have hh := ordinary_front_step _ _ ho.1 ho.2.1 ho.2.2 h.trail.signal h.trail.bullet
  have hr : liftedSite s (q+1)=rightNeighbor e := liftedSite_succ _ _
  have oldR : (x (rightNeighbor e)).bullet=.none := by
    rw [← hr]
    exact (h.unique _ (by omega)).trans (if_neg (by omega))
  have oldL : (x e).bullet=kind.bullet := (h.unique q (by omega)).trans (if_pos rfl)
  have fL : (step x e e).bullet=.none ∧ (step x e e).signal=.zero := by
    exact ⟨by simpa [step] using hh.1,by simpa [step] using hh.2.2.1⟩
  have fR : (step x e (liftedSite s (q+1))).bullet=kind.bullet ∧
      (step x e (liftedSite s (q+1))).signal=.zero := by
    rw [hr,right_snap hn]
    refine ⟨?_,hh.2.2.2⟩
    simpa [e,oldR,oldL] using hh.2.1
  have outside (j : Nat) (hj : j≤d) (h1 : j≠q) (h2 : j≠q+1) :
      step x e (liftedSite s j)=x (liftedSite s j) := by
    have hL : liftedSite s j≠e := fun H => h1 (liftedSite_inj s (by omega) (by omega) H)
    have hR : liftedSite s j≠rightNeighbor e := by
      rw [← hr]
      exact fun H => h2 (liftedSite_inj s (by omega) (by omega) H)
    simp [step,hL,hR]
  refine ⟨by omega,zeroFront_progress hn x s hm hc hF bd hq h.trail,?_,?_,?_⟩
  · intro j hj
    by_cases h1 : j=q
    · subst j
      have ne : q≠q+1 := by omega
      simpa [e,ne] using fL.1
    · by_cases h2 : j=q+1
      · subst j; simpa using fR.1
      · rw [outside j hj h1 h2,h.unique j hj,if_neg h1,if_neg h2]
  · intro j hj
    by_cases h1 : j=q
    · subst j
      change (step x e e).signal ≠ .two
      simp [fL.2]
    · by_cases h2 : j=q+1
      · subst j
        change (step x e (liftedSite s (q+1))).signal ≠ .two
        rw [fR.2]; decide
      · rw [outside j hj h1 h2]
        exact h.binary j hj
  · exact (zero_source_shield hn x s e hm hc hF hL hT (source_zero h) he).trans h.shield

/-- Terminal service changes to the exact binary return seed; the
source's shield records the just-finished front kind. -/
theorem sealed_front_finish {p c n d : Nat} (hn : 4≤n) (x : Config p c n) (s : Fin n)
    (bd : d+1<n) (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hL : (x s).leader=true) (hT : (x (liftedSite s (d+1))).leader=true)
    (kind : Kind) (h : SealedFront x s d d kind)
    (he : event x (liftedSite s d)=false) :
    ReturnFront (step x (liftedSite s d)) s d d ∧
      (step x (liftedSite s d) s).shield=kind.shield :=
  ⟨(zeroFront_terminal x s bd h.trail hT he).front,
    (zero_source_shield hn x s (liftedSite s d) hm hc hF hL hT (source_zero h) he).trans h.shield⟩

/-- In a nontrivial READY sector, outgoing service starts one live
bullet at physical offset one and makes no second bullet. -/
theorem ready_outgoing {p c n d : Nat} (hn : 4≤n)
    (x : Config p c n) (s : Fin n) (bd : d+1<n) (hd : 0<d)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hL : (x s).leader=true) (h : Ready x s d) :
    SealedFront (step x s) s d 1 .live := by
  have hS : (x s).signal=.one := by simpa [liftedSite_zero] using h.one
  have hnZ : (x s).signal≠.zero := by rw [hS]; decide
  have H := sourceOutgoing_starts_front hn x s hm hc hF hd hL hnZ
  have ho := sectorOrd x s hm hc hF hd
  rw [liftedSite_zero] at ho
  have hh := outgoing_first_front _ _ ho.1 ho.2.1 ho.2.2 hL hnZ
  have hR : liftedSite s 1=rightNeighbor s := by
    rw [show 1=0+1 by rfl,liftedSite_succ,liftedSite_zero]
  have rb : (x (rightNeighbor s)).bullet=.none := hR ▸ h.empty 1 (by omega)
  have live : (step x s (liftedSite s 1)).bullet=.live := by
    rw [hR,right_snap hn]
    simpa [rb] using hh.2.2.2.1
  have outside (j : Nat) (hj : j≤d) (h0 : j≠0) (h1 : j≠1) :
      step x s (liftedSite s j)=x (liftedSite s j) := by
    have e0 : liftedSite s j≠s := fun E => h0
      (liftedSite_inj s (by omega : j<n) (by omega : 0<n) (E.trans (liftedSite_zero _).symm))
    have e1 : liftedSite s j≠rightNeighbor s := fun E => h1
      (liftedSite_inj s (by omega : j<n) (by omega : 1<n) (E.trans hR.symm))
    simp [step,e0,e1]
  refine ⟨by omega,H.1,?_,?_,H.2⟩
  · intro j hj
    by_cases h0 : j=0
    · subst j; simpa [liftedSite_zero] using (H.1.swept 0 (by decide)).2
    · by_cases h1 : j=1
      · subst j; simpa [Kind.bullet] using live
      · rw [outside j hj h0 h1]
        simpa [h1] using h.empty j hj
  · intro j hj
    by_cases h0 : j=0
    · subst j; simp [(H.1.swept 0 (by decide)).1]
    · by_cases h1 : j=1
      · subst j; simp [H.1.signal]
      · rw [outside j hj h0 h1]
        exact h.binary j hj

private theorem interior_follower {p c n d : Nat} (x : Config p c n) (s : Fin n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d) (j : Nat) (hj : 0<j) (hD : j≤d) :
    (x (liftedSite s j)).leader=false := by
  cases j with
  | zero => omega
  | succ j =>
    have H := (sectorOrd x s hm hc hF (show j<d by omega)).2.2
    simpa [liftedSite_succ] using H

/-- All services not incident with a READY source keep its phase,
including its entire binary, bullet-free sector. -/
theorem ready_wait {p c n d : Nat} (hn : 4≤n) (x : Config p c n) (s e : Fin n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hT : (x (liftedSite s (d+1))).leader=true)
    (h : Ready x s d) (he : event x e=false) (hE : e≠s) (hR : rightNeighbor e≠s) :
    Ready (step x e) s d := by
  have hold (j : Nat) (hj : j≤d) :
      (step x e (liftedSite s j)).bullet=.none ∧
        (step x e (liftedSite s j)).signal≠.two := by
    by_cases hJ : liftedSite s j=e
    · have jpos : 0<j := by
        apply Nat.pos_of_ne_zero
        intro a
        exact hE (by simpa [a,liftedSite_zero] using hJ.symm)
      have qf := interior_follower x s hm hc hF j jpos hj
      rw [← hJ]
      by_cases hJd : j=d
      · subst j
        have H : (x (rightNeighbor (liftedSite s d))).leader=true := by
          rw [← liftedSite_succ]
          exact hT
        have HH := surviving_terminal _ _ H (safe_responder x _ H (hJ.symm ▸ he))
        rw [source_fire_identity _ (.inl qf)] at HH
        simp [step,HH.1,HH.2.1,binary_one _ (h.binary d hj)]
      · have ho := sectorOrd x s hm hc hF (show j<d by omega)
        have HH := ordinary_empty_donor _ _ ho.1 ho.2.1 ho.2.2 (h.empty j hj) (.inl qf)
        have Hb : (x (rightNeighbor (liftedSite s j))).signal≠.two := by
          rw [← liftedSite_succ]
          exact h.binary (j+1) (by omega)
        simp [step,HH.1,HH.2.1,binary_max (h.binary j hj) Hb]
    · by_cases hN : liftedSite s j=rightNeighbor e
      · cases j with
        | zero => exact (hR (by simpa [liftedSite_zero] using hN.symm)).elim
        | succ j =>
          have hi : liftedSite s j=e := FreshSeparation.succ_inj (by simpa [liftedSite_succ] using hN)
          have pos : 0<j := by
            apply Nat.pos_of_ne_zero
            intro a
            exact hE (by simpa [a,liftedSite_zero] using hi.symm)
          have ho := sectorOrd x s hm hc hF (show j<d by omega)
          have H := ordinary_empty_donor _ _ ho.1 ho.2.1 ho.2.2 (h.empty j (by omega))
            (.inl (interior_follower x s hm hc hF j pos (by omega)))
          have hp : (pairStep (x e) (x (rightNeighbor e))).2.bullet=(x (rightNeighbor e)).bullet ∧
              (pairStep (x e) (x (rightNeighbor e))).2.signal=(x (rightNeighbor e)).signal := by
            rw [← hi]
            exact ⟨H.2.2.1,H.2.2.2⟩
          rw [hN,right_snap hn,hp.1,hp.2,←hN]
          exact ⟨h.empty (j+1) hj,h.binary (j+1) hj⟩
      · simpa [step,hJ,hN] using And.intro (h.empty j hj) (h.binary j hj)
  refine ⟨Nat.zero_le _,fun j hj => (hold j hj).1,fun j hj => (hold j hj).2,?_,?_⟩
  · simpa [liftedSite_zero,step,Ne.symm hE,Ne.symm hR] using h.one
  · intro j hj
    omega

/-- A binary return preserves the source shield, including the exact
mark that first makes the source READY. -/
theorem sealed_return_progress {p c n d q : Nat} (hn : 4≤n)
    (x : Config p c n) (s e : Fin n) (bd : d+1<n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hL : (x s).leader=true) (hT : (x (liftedSite s (d+1))).leader=true)
    (h : ReturnFront x s d (q+1)) (he : event x e=false) :
    ReturnFront (step x e) s d (if e=liftedSite s q then q else q+1) ∧
      (step x e s).shield=(x s).shield :=
  ⟨returnFront_step x s e hm hc hF bd hL hT h he,
    zero_source_shield hn x s e hm hc hF hL hT (by
      have hZ := h.before 0 (Nat.zero_lt_succ q)
      simpa [liftedSite_zero] using hZ) he⟩

/-- Phase after a sector has been sealed. A returning q is a colour
one at physical offset q+1; offset zero is READY. -/
inductive Phase where
  | ready
  | forward (kind : Kind) (q : Nat)
  | returning (kind : Kind) (q : Nat)
  deriving DecidableEq

def Phase.Holds {p c n : Nat} (x : Config p c n) (s : Fin n) (d : Nat) : Phase → Prop
  | .ready => Ready x s d
  | .forward k q => SealedFront x s d q k
  | .returning k q => ReturnFront x s d (q+1) ∧ (x s).shield=k.shield

def Phase.isReady : Phase → Bool
  | .ready => true
  | _ => false

def Phase.tick {n : Nat} (s : Fin n) (d : Nat) (ph : Phase) (e : Fin n) : Phase :=
  match ph with
  | .ready =>
    if e=s then if d=0 then .ready else .forward .live 1
    else if rightNeighbor e=s then .forward .dummy 0 else .ready
  | .forward k q =>
    if e=liftedSite s q then
      if q<d then .forward k (q+1) else
        if d=0 then .ready else .returning k (d-1)
    else ph
  | .returning k q =>
    if e=liftedSite s q then if q=0 then .ready else .returning k (q-1) else ph

/-- READY is an exact physical observation, not a lookahead test. -/
theorem ready_iff_signal_one {p c n d : Nat} (x : Config p c n) (s : Fin n) (ph : Phase)
    (h : ph.Holds x s d) : ph.isReady=true ↔ (x s).signal=.one := by
  cases ph with
  | ready => simpa [Phase.isReady,liftedSite_zero] using h.one
  | forward k q => simp [Phase.isReady,source_zero h]
  | returning k q =>
    have hs := h.1.before 0 (Nat.zero_lt_succ q)
    have hz : (x s).signal=.zero := by simpa [liftedSite_zero] using hs
    simp [Phase.isReady,hz]

/-- Complete physical continuation table of one prepared sector. There
is no assumption about payloads outside this sector. -/
theorem phase_tick_literal {p c n d : Nat} (hn : 4≤n)
    (x : Config p c n) (s e : Fin n) (bd : d+1<n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hL : (x s).leader=true) (hT : (x (liftedSite s (d+1))).leader=true)
    (ph : Phase) (h : ph.Holds x s d) (he : event x e=false) :
    (ph.tick s d e).Holds (step x e) s d := by
  cases ph with
  | ready =>
    by_cases ho : e=s
    · subst e
      simp only [Phase.tick]
      by_cases hd : d=0
      · subst d
        have H : (x (rightNeighbor s)).leader=true := by simpa [liftedSite_succ,liftedSite_zero] using hT
        have hs : (x s).signal=.one := by simpa [liftedSite_zero] using h.one
        simp only [if_true,Phase.Holds,Ready]
        exact (sourceOutgoing_adjacent_ready x s hL H (by rw [hs]; decide) he).1
      · rw [if_neg hd]
        exact ready_outgoing hn x s bd (Nat.pos_of_ne_zero hd) hm hc hF hL h
    · by_cases hi : rightNeighbor e=s
      · simp only [Phase.tick,if_neg ho,if_pos hi]
        exact ready_incoming hn x s e bd hi hL h he
      · simp only [Phase.tick,if_neg ho,if_neg hi]
        exact ready_wait hn x s e hm hc hF hT h he ho hi
  | forward kind q =>
    have H : SealedFront x s d q kind := h
    by_cases hh : e=liftedSite s q
    · subst e
      simp only [Phase.tick]
      by_cases hq : q<d
      · rw [if_pos hq]
        exact sealed_front_progress hn x s bd hm hc hF hL hT kind H hq he
      · have hqd : q=d := by have hh := H.within; omega
        subst q
        have H' := sealed_front_finish hn x s bd hm hc hF hL hT kind H he
        simp only [if_neg (Nat.lt_irrefl _)]
        by_cases hd : d=0
        · subst d
          simp only [if_true,Phase.Holds,Ready]
          exact H'.1
        · rw [if_neg hd]
          change ReturnFront (step x (liftedSite s d)) s d ((d-1)+1) ∧ _
          rw [show d-1+1=d by omega]
          exact H'
    · simp only [Phase.tick,if_neg hh]
      exact sealed_front_wait hn x s e bd hm hc hF hL hT kind H he hh
  | returning k q =>
    have H := sealed_return_progress hn x s e bd hm hc hF hL hT h.1 he
    by_cases hp : e=liftedSite s q
    · simp only [Phase.tick,if_pos hp]
      rw [if_pos hp] at H
      by_cases hz : q=0
      · subst q
        simp only [if_true,Phase.Holds,Ready]
        exact H.1
      · rw [if_neg hz]
        change ReturnFront (step x e) s d ((q-1)+1) ∧ _
        rw [show q-1+1=q by omega]
        exact ⟨H.1,H.2.trans h.2⟩
    · simp only [Phase.tick,if_neg hp]
      rw [if_neg hp] at H
      exact ⟨H.1,H.2.trans h.2⟩

/-- Two consecutive prepared sectors, including rank two where the
second terminal is the first source. -/
structure Paired {p c n : Nat} (x : Config p c n) (v : Fin n)
    (a b : Nat) (left right : Phase) : Prop where
  geom : Start x v a b
  attacker : left.Holds x v a
  target : right.Holds x (liftedSite v (a+1)) b

/-- The two coordinates consume the same literal old physical mark;
neither observes the other's partially updated phase. -/
theorem paired_tick_literal {p c n a b : Nat} (hn : 4≤n) (x : Config p c n)
    (v e : Fin n) (hm : MCOV x) (hc : COV x) (left right : Phase)
    (h : Paired x v a b left right) (he : event x e=false) :
    Paired (step x e) v a b (left.tick v a e) (right.tick (liftedSite v (a+1)) b e) := by
  have hb : b+1<n := by rcases h.geom.arity with hh|⟨hh,_⟩ <;> omega
  exact ⟨no_event_preserves_start hn x e v hm hc he h.geom,
    phase_tick_literal hn x v e h.geom.at_least_two hm hc h.geom.first_gap
      h.geom.first_leader h.geom.second_leader left h.attacker he,
    phase_tick_literal hn x _ e hb hm hc h.geom.second_gap h.geom.second_leader
      h.geom.third_leader right h.target he⟩

end L4.TriplePhase
