import Leader.L4.Barrier
import Leader.L4.TaggedTrace
import Init.Data.List.Nat.Find
import Lean.Elab.Tactic.Omega

/-!
# Clockwise geometry of a tagged carrier

Use the first marked *incoming edge* clockwise from the carrier. A marked
edge at offset zero is a root one site ahead; an incoming mark immediately
behind the carrier is reached after an entire lap. The marked-edge view
avoids assigning a new ghost an identity on a merge edge.
-/

namespace L4

/-- Index a ring by clockwise offsets from a fixed carrier. -/
def liftedSite {n : Nat} (b : Fin n) (d : Nat) : Fin n :=
  ⟨(b.val+d)%n, Nat.mod_lt _ (Nat.zero_lt_of_lt b.isLt)⟩

theorem liftedSite_zero {n : Nat} (b : Fin n) : liftedSite b 0 = b := by
  apply Fin.ext
  simp [liftedSite, Nat.mod_eq_of_lt b.isLt]

theorem liftedSite_succ {n : Nat} (b : Fin n) (d : Nat) :
    liftedSite b (d+1) = rightNeighbor (liftedSite b d) := by
  apply Fin.ext
  simp [liftedSite, rightNeighbor, Nat.add_assoc]

theorem liftedSite_full {n : Nat} (b : Fin n) : liftedSite b n = b := by
  apply Fin.ext
  simp [liftedSite, Nat.mod_eq_of_lt b.isLt]

theorem liftedSite_advance {n : Nat} (b : Fin n) (d : Nat) :
    liftedSite (rightNeighbor b) d = liftedSite b (d+1) := by
  apply Fin.ext
  simp [liftedSite, rightNeighbor]
  congr 1
  omega

theorem liftedSite_of_site {n : Nat} (b i : Fin n) :
    ∃ d : Nat, d < n ∧ liftedSite b d = i := by
  have hb := b.isLt
  have hi := i.isLt
  by_cases h : b.val ≤ i.val
  · refine ⟨i.val - b.val, by omega, Fin.ext ?_⟩
    change (b.val + (i.val - b.val)) % n = i.val
    rw [show b.val + (i.val - b.val) = i.val by omega, Nat.mod_eq_of_lt hi]
  · refine ⟨n - b.val + i.val, by omega, Fin.ext ?_⟩
    change (b.val + (n - b.val + i.val)) % n = i.val
    rw [show b.val + (n - b.val + i.val) = n + i.val by omega]
    simpa [Nat.add_comm] using Nat.mod_eq_of_lt hi

theorem liftedSite_inj {n : Nat} (b : Fin n) {i j : Nat}
    (hi : i < n) (hj : j < n) :
    liftedSite b i = liftedSite b j → i = j := by
  intro h
  have h := congrArg Fin.val h
  change (b.val + i) % n = (b.val + j) % n at h
  have hb := b.isLt
  by_cases h₁ : b.val + i < n <;> by_cases h₂ : b.val + j < n
  · rw [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at h; omega
  · rw [Nat.mod_eq_of_lt h₁, Nat.mod_eq_sub_mod (by omega : n ≤ b.val + j),
        Nat.mod_eq_of_lt (by omega : b.val + j - n < n)] at h; omega
  · rw [Nat.mod_eq_sub_mod (by omega : n ≤ b.val + i),
        Nat.mod_eq_of_lt (by omega : b.val + i - n < n), Nat.mod_eq_of_lt h₂] at h; omega
  · rw [Nat.mod_eq_sub_mod (by omega : n ≤ b.val + i),
        Nat.mod_eq_of_lt (by omega : b.val + i - n < n),
        Nat.mod_eq_sub_mod (by omega : n ≤ b.val + j),
        Nat.mod_eq_of_lt (by omega : b.val + j - n < n)] at h
    omega

private theorem rightNe {n : Nat} (hn : 4 ≤ n) (b : Fin n) : rightNeighbor b ≠ b := by
  intro h
  apply Nat.one_ne_zero
  apply liftedSite_inj b (by omega : 1 < n) (by omega : 0 < n)
  rw [liftedSite_succ b 0, liftedSite_zero b, h]

/-- The first covered root strictly clockwise of the carrier enters at
offset `d+1`, through the marked edge whose donor is at offset `d`. -/
structure FirstMark {p c1 n : Nat} (x : Config p c1 n) (b : Fin n) (d : Nat) : Prop where
  lt : d < n
  marked : (x (liftedSite b d)).mark = true
  before : ∀ j : Nat, j < d → (x (liftedSite b j)).mark ≠ true

private theorem least_bounded (P : Nat → Prop) (n : Nat) :
    (∃ j, j < n ∧ P j) → ∃ j, j < n ∧ P j ∧ ∀ i, i < j → ¬ P i := by
  induction n with
  | zero => rintro ⟨_,h,_⟩; omega
  | succ n ih =>
    intro hs
    classical
    by_cases h : ∃ j, j < n ∧ P j
    · obtain ⟨j,hj,hP,hmin⟩ := ih h
      exact ⟨j, by omega, hP, hmin⟩
    · obtain ⟨j,hj,hP⟩ := hs
      have he : j = n := by
        by_cases hjn : j < n
        · exact False.elim (h ⟨j,hjn,hP⟩)
        · omega
      subst j
      exact ⟨n, by omega, hP, fun i hi hPi => h ⟨i,hi,hPi⟩⟩

theorem firstMark_exists {p c1 n : Nat} (x : Config p c1 n) (b : Fin n)
    (h : ∃ u, (x u).mark = true) : ∃ d, FirstMark x b d := by
  obtain ⟨u,hu⟩ := h
  obtain ⟨j,hj,he⟩ := liftedSite_of_site b u
  obtain ⟨d,hd,hm,hbefore⟩ := least_bounded (fun j => (x (liftedSite b j)).mark = true)
    n ⟨j,hj,by simpa [he] using hu⟩
  exact ⟨d,hd,hm,hbefore⟩

theorem FirstMark.min_le {p c1 n d j : Nat} {x : Config p c1 n} {b : Fin n}
    (h : FirstMark x b d) (hm : (x (liftedSite b j)).mark = true) : d ≤ j := by
  by_cases hj : j < d
  · exact False.elim (h.before j hj hm)
  · omega

theorem FirstMark.unique {p c1 n d j : Nat} {x : Config p c1 n} {b : Fin n}
    (h : FirstMark x b d) (h' : FirstMark x b j) : d = j :=
  Nat.le_antisymm (h.min_le h'.marked) (h'.min_le h.marked)

/-- The exact P3 guard, evaluated after R0 and N0–N5. -/
def geometricPay {p c1 : Nat} (u v : Site p c1) : Bool :=
  let a := native (materialize u v) v
  (!a.2.leader) && a.1.mark && payer a.1

private theorem pair_mark_prefix {p c1 : Nat} (u v : Site p c1) :
    (pairStep u v).1.mark = (stepPrefix u v).1.mark ∧
    (pairStep u v).2.mark = (stepPrefix u v).2.mark := by
  unfold pairStep
  generalize stepPrefix u v = z
  cases z with
  | mk a b =>
    dsimp [patrolWrite]
    unfold finishBirth
    split <;> exact ⟨rfl,rfl⟩

private theorem native_marks {p c1 : Nat} (u v : Site p c1) :
    (native u v).1.mark = u.mark ∧ (native u v).2.mark = v.mark ∧
    ((native u v).2.leader = true → v.leader = true) := by
  have hFi : (fireInitiator u).mark = u.mark := by unfold fireInitiator; split <;> rfl
  have hFr : (fireResponder v).mark = v.mark ∧ (fireResponder v).leader = v.leader := by
    unfold fireResponder
    split
    · cases v.signal <;> exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
  unfold native
  generalize fireInitiator u = a at hFi ⊢
  generalize fireResponder v = b at hFr ⊢
  have hi : (impact a b).1.mark = a.mark ∧ (impact a b).2.mark = b.mark ∧
      ((impact a b).2.leader = true → b.leader = true) := by
    unfold impact
    split
    · split <;> simp
    · simp
  generalize impact a b = z at hi ⊢
  cases z with
  | mk au bv =>
    have hf (c : Bool) : (followerBullet c au bv).1.mark = au.mark ∧
        (followerBullet c au bv).2.mark = bv.mark ∧
        (followerBullet c au bv).2.leader = bv.leader := by
      unfold followerBullet
      split
      · split <;> exact ⟨rfl,rfl,rfl⟩
      · exact ⟨rfl,rfl,rfl⟩
    exact ⟨(hf _).1.trans (hi.1.trans hFi),
      (hf _).2.1.trans (hi.2.1.trans hFr.1), fun h =>
        hFr.2.symm.trans (hi.2.2 ((hf _).2.2.symm ▸ h))⟩

/-- On a covered bond, the two outgoing mark bytes can change only by the
literal P3 shift. The old responder's mark may already be set (retirement
by merging with the next root). -/
theorem covered_pair_marks {p c1 : Nat} (u v : Site p c1)
    (hc : (v.leader = true ∨ v.residue ≠ nextResidue u.residue) → u.mark = true) :
    if geometricPay u v then
      u.mark = true ∧ (pairStep u v).1.mark = false ∧ (pairStep u v).2.mark = true
    else (pairStep u v).1.mark = u.mark ∧ (pairStep u v).2.mark = v.mark := by
  have hx : materialize u v = u := by
    by_cases hm : u.mark = true
    · cases u; simp_all [materialize]
    · have hm' : u.mark = false := by cases hu : u.mark <;> simp_all
      have hl : v.leader = false := by
        cases hv : v.leader
        · rfl
        · exact False.elim (hm (hc (Or.inl hv)))
      have hr : v.residue = nextResidue u.residue := by
        by_cases he : v.residue = nextResidue u.residue
        · exact he
        · exact False.elim (hm (hc (Or.inr he)))
      simp [materialize, hm', hl, defect, hr]
  have hpair := pair_mark_prefix u v
  simp only [hpair.1,hpair.2,stepPrefix,geometricPay,hx]
  have hn := native_marks u v
  generalize native u v = a at hn ⊢
  cases a with
  | mk aa bb =>
    dsimp only at *
    have hlb : bb.leader = true → aa.mark = true := fun hl => hn.1.trans (hc (Or.inl (hn.2.2 hl)))
    cases hL : bb.leader <;> cases hM : aa.mark <;> cases hP : payer aa <;> cases hS : bb.stock <;>
      simp_all [payment]

/-- Only the selected paid P3 can clear a mark. Its responder gets a mark;
all other bytes are unchanged (native death and P5 do not change marks). -/
theorem covered_step_mark {p c1 n : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (hc : MCOV x) (e i : Fin n) :
    (step x e i).mark =
      if geometricPay (x e) (x (rightNeighbor e)) then
        if i = e then false else if i = rightNeighbor e then true else (x i).mark
      else (x i).mark := by
  have hm := covered_pair_marks (x e) (x (rightNeighbor e)) (hc e)
  by_cases hp : geometricPay (x e) (x (rightNeighbor e)) = true
  · simp only [hp, if_true] at hm ⊢
    by_cases he : i = e
    · subst i; simpa [step] using hm.2.1
    · by_cases hi : i = rightNeighbor e
      · subst i; simp [step, rightNe hn e, hm.2.2]
      · simp [step, he, hi]
  · have hf : geometricPay (x e) (x (rightNeighbor e)) = false := Bool.eq_false_iff.mpr hp
    simp only [hf, Bool.false_eq_true, if_false] at hm ⊢
    by_cases he : i = e
    · subst i; simpa [step] using hm.1
    · by_cases hi : i = rightNeighbor e
      · subst i; simpa [step, rightNe hn e] using hm.2
      · simp [step, he, hi]

private theorem native_fixed_fields {p c1 : Nat} (u v : Site p c1) :
    (native u v).1.residue = u.residue ∧ (native u v).1.leader = u.leader ∧
      (native u v).2.residue = v.residue := by
  have hFi : (fireInitiator u).residue = u.residue ∧ (fireInitiator u).leader = u.leader := by
    unfold fireInitiator
    split <;> exact ⟨rfl,rfl⟩
  have hFr : (fireResponder v).residue = v.residue := by
    unfold fireResponder
    split
    · cases v.signal <;> rfl
    · rfl
  unfold native
  generalize fireInitiator u = a at hFi ⊢
  generalize fireResponder v = b at hFr ⊢
  have hi : (impact a b).1.residue = a.residue ∧ (impact a b).1.leader = a.leader ∧
      (impact a b).2.residue = b.residue := by
    unfold impact
    split
    · split <;> exact ⟨rfl,rfl,rfl⟩
    · exact ⟨rfl,rfl,rfl⟩
  generalize impact a b = z at hi ⊢
  cases z with
  | mk au bv =>
    have hf (c : Bool) : (followerBullet c au bv).1.residue = au.residue ∧
        (followerBullet c au bv).1.leader = au.leader ∧
        (followerBullet c au bv).2.residue = bv.residue := by
      unfold followerBullet
      split
      · split <;> exact ⟨rfl,rfl,rfl⟩
      · exact ⟨rfl,rfl,rfl⟩
    exact ⟨(hf _).1.trans (hi.1.trans hFi.1),
      (hf _).2.1.trans (hi.2.1.trans hFi.2),
      (hf _).2.2.trans (hi.2.2.trans hFr)⟩

private theorem suffix_fields {p c1 : Nat} (u v : Site p c1) :
    (pairStep u v).1.residue = (stepPrefix u v).1.residue ∧
    (pairStep u v).1.leader = (stepPrefix u v).1.leader ∧
    (pairStep u v).2.residue = (stepPrefix u v).2.residue ∧
    ((stepPrefix u v).1.mark = false →
      (pairStep u v).2.leader = (stepPrefix u v).2.leader) := by
  unfold pairStep
  generalize stepPrefix u v = z
  cases z with
  | mk a b =>
    dsimp [patrolWrite]
    refine ⟨?_,?_,?_,?_⟩
    all_goals unfold finishBirth
    · split <;> rfl
    · split <;> rfl
    · split <;> rfl
    · intro h
      simp [pinned,h]

/-- Residues write only in P3, on its responder, and a paid responder
remains ordinary after this selected step. The donor is never killed. -/
theorem pair_geometric_fields {p c1 : Nat} (u v : Site p c1) :
    (pairStep u v).1.residue = u.residue ∧
    (pairStep u v).1.leader = u.leader ∧
    (if geometricPay u v then
      (pairStep u v).2.residue = nextResidue u.residue ∧ (pairStep u v).2.leader = false
      else (pairStep u v).2.residue = v.residue) := by
  have hp := suffix_fields u v
  have hf := native_fixed_fields (materialize u v) v
  have hr : (materialize u v).residue = u.residue := by
    unfold materialize; split <;> rfl
  have hl : (materialize u v).leader = u.leader := by
    unfold materialize; split <;> rfl
  unfold geometricPay
  generalize hnat : native (materialize u v) v = z at hf ⊢
  have hpre : stepPrefix u v = payment z.1 z.2 := by
    unfold stepPrefix
    rw [hnat]
  rw [hpre] at hp
  cases z with
  | mk a b =>
    dsimp only at *
    have h1 : (payment a b).1.residue = a.residue ∧ (payment a b).1.leader = a.leader := by
      unfold payment
      split
      · exact ⟨rfl,rfl⟩
      · split
        · exact ⟨rfl,rfl⟩
        · split <;> exact ⟨rfl,rfl⟩
    refine ⟨hp.1.trans (h1.1.trans (hf.1.trans hr)),
      hp.2.1.trans (h1.2.trans (hf.2.1.trans hl)),?_⟩
    by_cases hL : b.leader = true
    · have hh : (payment a b).2.residue = b.residue := by simp [payment,hL]
      simpa [hL] using hp.2.2.1.trans (hh.trans hf.2.2)
    · have hLF : b.leader = false := Bool.eq_false_iff.mpr hL
      by_cases hm : a.mark = true
      · by_cases hP : payer a = true
        · have hM : (payment a b).1.mark = false := by simp [payment,hLF,hm,hP]
          have hlead := hp.2.2.2 hM
          simp only [hLF, hm, hP, Bool.not_false, Bool.true_and, if_true]
          constructor
          · simpa [payment,hLF,hm,hP,hf.1,hr] using hp.2.2.1
          · simpa [payment,hLF,hm,hP] using hlead
        · have hfP := Bool.eq_false_iff.mpr hP
          have hh : (payment a b).2.residue = b.residue := by simp [payment,hLF,hm,hfP]
          simpa [hLF,hm,hfP] using hp.2.2.1.trans (hh.trans hf.2.2)
      · have hfM := Bool.eq_false_iff.mpr hm
        have ht : (payment a b).2.residue = b.residue := by
          simp [payment,hLF,hfM]
          split <;> rfl
        simpa [hLF,hfM] using hp.2.2.1.trans (ht.trans hf.2.2)

private theorem successor_injective {n : Nat} {a b : Fin n}
    (h : rightNeighbor a = rightNeighbor b) : a = b := by
  have hh := congrArg Fin.val h
  change (a.val+1)%n = (b.val+1)%n at hh
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  by_cases ha' : a.val+1 < n <;> by_cases hb' : b.val+1 < n
  · rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hh
    omega
  · rw [Nat.mod_eq_of_lt ha', show b.val+1 = n by omega, Nat.mod_self] at hh
    omega
  · rw [show a.val+1 = n by omega, Nat.mod_self, Nat.mod_eq_of_lt hb'] at hh
    omega
  · omega

/-- MARK-COVER is closed under every literal raw edge at n≥4. -/
theorem mcov_step {p c1 n : Nat} (hn : 4 ≤ n) (x : Config p c1 n)
    (hc : MCOV x) (e : Fin n) : MCOV (step x e) := by
  let v := rightNeighbor e
  have hne : v ≠ e := rightNe hn e
  have ha : step x e e = (pairStep (x e) (x v)).1 := by simp [step,v]
  have hb : step x e v = (pairStep (x e) (x v)).2 := by simp [step,v,hne]
  have hpair := pair_geometric_fields (x e) (x v)
  have hmark (i : Fin n) := covered_step_mark hn x hc e i
  intro i hbad
  by_cases hI : i = e
  · subst i
    rw [hb,ha] at hbad
    by_cases hp : geometricPay (x e) (x v) = true
    · have hP := hpair.2.2
      rw [if_pos hp] at hP
      simp [hpair.1,hP.1,hP.2] at hbad
    · rw [hmark e]
      simp only [v,hp]
      by_cases hm : (x e).mark = true
      · exact hm
      · have hm' := Bool.eq_false_iff.mpr hm
        have hor := (covered_noRoot_iff hc).2 hm'
        have hres : (x v).residue = nextResidue (x e).residue := by
          by_cases hz : (x v).residue = nextResidue (x e).residue
          · exact hz
          · exact False.elim (hor (Or.inr (Or.inr hz)))
        have hlead : (x v).leader = false := by
          cases hz : (x v).leader
          · rfl
          · exact False.elim (hor (Or.inl hz))
        have hOrd := ordinary_pair_geometry (x e) (x v) hm' hres hlead
        have hl' := hOrd.2.1.trans hlead
        have hr' := hOrd.2.2.2.1.trans hres
        rw [hl',hr',hOrd.1.2.2] at hbad
        simp at hbad
  · by_cases hV : i = v
    · subst i
      by_cases hp : geometricPay (x e) (x v) = true
      · simp [hmark v,v,hp,hne]
      · have hiE : rightNeighbor v ≠ e := by
          intro h
          have he := congrArg Fin.val h
          change (((e.val+1)%n)+1)%n = e.val at he
          rw [Nat.mod_add_mod] at he
          have hh := e.isLt
          by_cases he' : e.val+2 < n
          · rw [Nat.mod_eq_of_lt he'] at he; omega
          · rw [Nat.mod_eq_sub_mod (by omega : n ≤ e.val+2),
                Nat.mod_eq_of_lt (by omega : e.val+2-n<n)] at he
            omega
        have hiV : rightNeighbor v ≠ v := rightNe hn v
        have hout : step x e (rightNeighbor v) = x (rightNeighbor v) := by
          simp [step,hiE,hiV,v]
        rw [hout,hb] at hbad
        have hres : (pairStep (x e) (x v)).2.residue = (x v).residue := by
          simpa [hp] using hpair.2.2
        rw [hres] at hbad
        have hh := hc v hbad
        simpa [hmark v,v,hp] using hh
    · have horig : step x e i = x i := by simp [step,hI,hV,v]
      rw [horig] at hbad
      by_cases hE : rightNeighbor i = e
      · rw [hE,ha,hpair.1,hpair.2.1] at hbad
        have hh := hc i (by simpa [hE] using hbad)
        simp [hmark i,hI,hV,v,hh]
      · have hv' : rightNeighbor i ≠ v := fun h => hI (successor_injective h)
        have hout : step x e (rightNeighbor i) = x (rightNeighbor i) := by
          simp [step,hE,hv',v]
        rw [hout] at hbad
        have hh := hc i hbad
        simp [hmark i,hI,hV,v,hh]

/-- If all incoming marks vanish in a covered ring, the residue increments
telescope around the circumference, forcing divisibility by the modulus. -/
theorem covered_mark_exists_of_not_dvd {p c1 n : Nat}
    (x : Config p c1 n) (base : Fin n) (hc : MCOV x) (hnd : ¬ p ∣ n) :
    ∃ e, (x e).mark = true := by
  classical
  by_cases hm : ∃ e, (x e).mark = true
  · exact hm
  · exfalso
    have hres (e : Fin n) : (x (rightNeighbor e)).residue = nextResidue (x e).residue := by
      by_cases hh : (x (rightNeighbor e)).residue = nextResidue (x e).residue
      · exact hh
      · exact False.elim (hm ⟨e,hc e (Or.inr hh)⟩)
    let a := (x base).residue.val
    have ha : a < p := (x base).residue.isLt
    have hcycle (d : Nat) : (x (liftedSite base d)).residue.val = (a+d)%p := by
      induction d with
      | zero => simp [liftedSite_zero, a, Nat.mod_eq_of_lt ha]
      | succ d ih =>
        rw [liftedSite_succ, hres]
        change ((x (liftedSite base d)).residue.val + 1) % p = (a + (d+1)) % p
        rw [ih, Nat.mod_add_mod, Nat.add_assoc]
    have hend : (a+n)%p = a := by simpa [liftedSite_full, a] using (hcycle n).symm
    have hend' : (a + n % p)%p = a := by simpa using hend
    have hp : 0 < p := by omega
    have hmod : n % p < p := Nat.mod_lt _ hp
    apply hnd
    apply Nat.dvd_of_mod_eq_zero
    by_cases hsmall : a + n % p < p
    · rw [Nat.mod_eq_of_lt hsmall] at hend'
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : p ≤ a + n % p),
          Nat.mod_eq_of_lt (by omega : a + n % p - p < p)] at hend'
      omega

/-- Count a P3 advance only when the old selected donor was the first
marked donor clockwise from the carrier. Merges still count as a paid
advance of that position; root labels are not needed here. -/
def frontPayment {p c1 n : Nat} (x : Config p c1 n) (b e : Fin n) (d : Nat) : Nat :=
  if e = liftedSite b d ∧ geometricPay (x e) (x (rightNeighbor e)) = true
  then 1 else 0

/-- With a stationary carrier, the distance potential grows by at most one
on a paid movement of its old first barrier. A P3 elsewhere can only leave
the bound unchanged or improve it. -/
theorem firstMark_stationary_step {p c1 n d : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (hc : MCOV x) (b e : Fin n) (h : FirstMark x b d) :
    ∃ d', FirstMark (step x e) b d' ∧ d' ≤ d + frontPayment x b e d := by
  have hs (i : Fin n) := covered_step_mark hn x hc e i
  by_cases hp : geometricPay (x e) (x (rightNeighbor e)) = true
  · by_cases he : e = liftedSite b d
    · have hv : (step x e (rightNeighbor e)).mark = true := by
        simp [hs, hp, rightNe hn e]
      obtain ⟨d', hd'⟩ := firstMark_exists (step x e) b ⟨rightNeighbor e, hv⟩
      have hv' : (step x e (liftedSite b (d+1))).mark = true := by
        rw [liftedSite_succ, ← he]
        exact hv
      have hf : frontPayment x b e d = 1 := if_pos ⟨he,hp⟩
      exact ⟨d',hd',by simpa [hf] using hd'.min_le hv'⟩
    · have hv : (step x e (liftedSite b d)).mark = true := by
        simp [hs, hp, Ne.symm he, h.marked]
      obtain ⟨d',hd'⟩ := firstMark_exists (step x e) b ⟨liftedSite b d,hv⟩
      exact ⟨d',hd',by simpa [frontPayment,he,hp] using hd'.min_le hv⟩
  · have hv : (step x e (liftedSite b d)).mark = true := by
      simp [hs, hp, h.marked]
    obtain ⟨d',hd'⟩ := firstMark_exists (step x e) b ⟨liftedSite b d,hv⟩
    exact ⟨d',hd',by simpa [frontPayment,hp] using hd'.min_le hv⟩

/-- A surviving live-tag transport cannot step into an existing root. Its
old first mark is unchanged *and* one offset closer. -/
theorem firstMark_transport_step {p c1 n d : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (hc : MCOV x) (b : Fin n) (h : FirstMark x b d)
    (ht : tagTransfer (x b) (x (rightNeighbor b)) = true) :
    ∃ d', FirstMark (step x b) (rightNeighbor b) d' ∧
          1 + d' ≤ d + frontPayment x b b d := by
  have hm := (tagTransfer_iff (x b) (x (rightNeighbor b))).mp ht |>.2.2.2.1
  have hd : 0 < d := by
    by_cases hzero : d = 0
    · exact False.elim (by simpa [hzero,liftedSite_zero,hm] using h.marked)
    · omega
  have hp : geometricPay (x b) (x (rightNeighbor b)) ≠ true := by
    intro hpay
    have hmark := covered_pair_marks (x b) (x (rightNeighbor b)) (hc b)
    simp [hpay,hm] at hmark
  have hv : (step x b (liftedSite b d)).mark = true := by
    rw [covered_step_mark hn x hc b]
    simp [hp, h.marked]
  obtain ⟨d',hd'⟩ := firstMark_exists (step x b) (rightNeighbor b) ⟨_,hv⟩
  have hmark : (step x b (liftedSite (rightNeighbor b) (d-1))).mark = true := by
    rw [liftedSite_advance, show d-1+1=d by omega]
    exact hv
  have hle := hd'.min_le hmark
  refine ⟨d',hd',?_⟩
  simp [frontPayment,hp]
  omega

/-- The proof-side minimum and the executable first-mark scan select the
same edge; the scan examines the colocated root only at the end of a lap. -/
theorem firstMarkedEdge_eq_lifted {p c1 n d : Nat} {x : Config p c1 n} {b : Fin n}
    (h : FirstMark x b d) :
    TaggedFront.firstMarkedEdge x b = some (liftedSite b d) := by
  unfold TaggedFront.firstMarkedEdge
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨h.marked, d, by simpa using h.lt, ?_, ?_⟩
  · simp [TaggedFront.plusOffset, liftedSite]
  · intro j hj
    rw [List.getElem_ofFn]
    simpa [TaggedFront.plusOffset,liftedSite] using h.before j hj

theorem paidFirst_toNat {p c1 n d : Nat} {x : Config p c1 n} {b : Fin n}
    (hc : MCOV x) (e : Fin n) (h : FirstMark x b d) :
    (TaggedTrace.paidFirst x b e).toNat = frontPayment x b e d := by
  have hm := covered_pair_marks (x e) (x (rightNeighbor e)) (hc e)
  unfold TaggedTrace.paidFirst frontPayment
  rw [firstMarkedEdge_eq_lifted h]
  by_cases hp : geometricPay (x e) (x (rightNeighbor e)) = true
  · simp only [hp,if_true] at hm
    by_cases he : e = liftedSite b d
    · simp only [hm.1,hm.2.1,Bool.not_false]
      rw [if_pos ⟨he,hp⟩]
      simp [he]
    · have hh : liftedSite b d ≠ e := Ne.symm he
      simp [he,hh]
  · have hf : geometricPay (x e) (x (rightNeighbor e)) = false := Bool.eq_false_iff.mpr hp
    simp only [hf,Bool.false_eq_true,if_false] at hm
    simp [hp,hm.1]

/-- Cover of every pre-mark configuration on the finite observer trace.
This module does not assume post-cover permanence unless supplied by the
separate literal row proof for MCOV. -/
def CoveredGeometryWord {p c1 n : Nat} (x : Config p c1 n) : List (Fin n) → Prop
  | [] => True
  | e :: w => MCOV x ∧ CoveredGeometryWord (step x e) w

/-- The literal surviving observation pays for every clockwise transport
either out of its current first-mark distance or out of a P3 of that mark. -/
theorem geometry_advance {p c1 n d : Nat} (hn : 4 ≤ n)
    (s : TaggedTrace.Obs p c1 n) (hc : MCOV s.config) (b e : Fin n)
    (hb : s.carrier = some b) (h : FirstMark s.config b d)
    (alive : ¬ TaggedTrace.ended (TaggedTrace.advance s e)) :
    ∃ (b' : Fin n) (d' : Nat),
      (TaggedTrace.advance s e).carrier = some b' ∧
      FirstMark (TaggedTrace.advance s e).config b' d' ∧
      (TaggedTrace.advance s e).moveCount + d' + s.paidCount ≤
        s.moveCount + d + (TaggedTrace.advance s e).paidCount := by
  obtain ⟨b', hb'⟩ : ∃ b', TaggedTrace.carrierStep s.config e (some b) = some b' := by
    cases hh : TaggedTrace.carrierStep s.config e (some b) with
    | some j => exact ⟨j,rfl⟩
    | none =>
      exact False.elim (alive (by simp [TaggedTrace.ended,TaggedTrace.advance,hb,hh]))
  have hNext : (TaggedTrace.advance s e).carrier = some b' := by
    simp [TaggedTrace.advance,hb,hb']
  have hpay : (TaggedTrace.advance s e).paidCount = s.paidCount + frontPayment s.config b e d := by
    simp [TaggedTrace.advance,hb,paidFirst_toNat hc e h]
  by_cases he : b = e
  · subst e
    obtain ⟨hj,ht⟩ := TaggedTrace.carrierStep_selected_survives s.config b b' hb'
    obtain ⟨d',hd',hle⟩ := firstMark_transport_step hn s.config hc b h ht
    refine ⟨b',d',hNext,?_,?_⟩
    · simpa [TaggedTrace.projection_step,hj] using hd'
    · rw [hpay]
      simp only [TaggedTrace.advance,hb,hb',BEq.rfl,Option.isSome_some,
        Bool.and_self,Bool.toNat_true]
      omega
  · have hj := TaggedTrace.carrierStep_not_selected_stays s.config e b b' he hb'
    obtain ⟨d',hd',hle⟩ := firstMark_stationary_step hn s.config hc b e h
    refine ⟨b',d',hNext,?_,?_⟩
    · simpa [TaggedTrace.projection_step,hj] using hd'
    · rw [hpay]
      have hnbe : (b == e) = false := by simpa using he
      simp only [TaggedTrace.advance,hb,hb',hnbe,Bool.false_and,Bool.toNat_false,Nat.add_zero]
      omega

/-- Pathwise geometric potential on a covered, surviving observer trace. -/
theorem geometry_track {p c1 n d : Nat} (hn : 4 ≤ n)
    (s : TaggedTrace.Obs p c1 n) (b : Fin n) (w : List (Fin n))
    (hb : s.carrier = some b) (h : FirstMark s.config b d)
    (hc : CoveredGeometryWord s.config w)
    (alive : ¬ TaggedTrace.ended (TaggedTrace.track s w)) :
    ∃ (b' : Fin n) (d' : Nat),
      (TaggedTrace.track s w).carrier = some b' ∧
      FirstMark (TaggedTrace.track s w).config b' d' ∧
      (TaggedTrace.track s w).moveCount + d' + s.paidCount ≤
        s.moveCount + d + (TaggedTrace.track s w).paidCount := by
  induction w generalizing s b d with
  | nil => exact ⟨b,d,hb,h,Nat.le_refl _⟩
  | cons e w ih =>
    have liveNext : ¬ TaggedTrace.ended (TaggedTrace.advance s e) :=
      fun hx => alive (TaggedTrace.ended_run (TaggedTrace.advance s e) w hx)
    obtain ⟨b₁,d₁,hb₁,h₁,hStep⟩ := geometry_advance hn s hc.1 b e hb h liveNext
    have hc' : CoveredGeometryWord (TaggedTrace.advance s e).config w := by
      simpa only [TaggedTrace.projection_step] using hc.2
    obtain ⟨b',d',hb',h',hTrace⟩ := ih (TaggedTrace.advance s e) b₁ hb₁ h₁ hc' alive
    refine ⟨b',d',hb',h',?_⟩
    simp only [TaggedTrace.track]
    omega

/-- The paper's geometric debt bound for a finite surviving tagged trace,
given cover on its pre-mark configurations and initial root nonemptiness. -/
theorem tagged_moves_le_size_add_paid {p c1 n : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (b : Fin n) (w : List (Fin n))
    (hm : ∃ e, (x e).mark = true)
    (hc : CoveredGeometryWord x w)
    (alive : ¬ TaggedTrace.ended (TaggedTrace.track (TaggedTrace.init x b) w)) :
    (TaggedTrace.track (TaggedTrace.init x b) w).moveCount ≤
      n + (TaggedTrace.track (TaggedTrace.init x b) w).paidCount := by
  let s := TaggedTrace.init x b
  have hb : s.carrier = some b := by
    cases h : s.carrier with
    | none => exact False.elim (alive (TaggedTrace.ended_run s w h))
    | some i =>
      have hbi : i = b := by
        unfold s TaggedTrace.init at h
        split at h
        · exact (Option.some.inj h).symm
        · contradiction
      simp [hbi]
  obtain ⟨d,hmark⟩ := firstMark_exists x b hm
  obtain ⟨_,d',_,_,hbound⟩ := geometry_track hn s b w hb hmark hc alive
  have hd := hmark.lt
  change (TaggedTrace.track s w).moveCount ≤ n + (TaggedTrace.track s w).paidCount
  have hm0 : s.moveCount = 0 := rfl
  have hp0 : s.paidCount = 0 := rfl
  omega

/-- One cover cut suffices for every pre-mark of the finite word. -/
theorem coveredGeometryWord_of_mcov {p c1 n : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (w : List (Fin n)) (hc : MCOV x) :
    CoveredGeometryWord x w := by
  induction w generalizing x with
  | nil => trivial
  | cons e w ih => exact ⟨hc,ih (step x e) (mcov_step hn x hc e)⟩

/-- Literal tagged geometry from a single covered initial state on the
paper's nondivisible domain. Its marker budget counts only actual P3
movements of the first marked donor, even when the mover retires. -/
theorem tagged_moves_le_size_add_paid_of_mcov {p c1 n : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (b : Fin n) (w : List (Fin n))
    (hc : MCOV x) (hnd : ¬ p ∣ n)
    (alive : ¬ TaggedTrace.ended (TaggedTrace.track (TaggedTrace.init x b) w)) :
    (TaggedTrace.track (TaggedTrace.init x b) w).moveCount ≤
      n + (TaggedTrace.track (TaggedTrace.init x b) w).paidCount :=
  tagged_moves_le_size_add_paid hn x b w (covered_mark_exists_of_not_dvd x b hc hnd)
    (coveredGeometryWord_of_mcov hn x w hc) alive

end L4

#print axioms L4.covered_pair_marks
#print axioms L4.firstMark_stationary_step
#print axioms L4.firstMark_transport_step
#print axioms L4.firstMarkedEdge_eq_lifted
#print axioms L4.geometry_advance
#print axioms L4.geometry_track
#print axioms L4.tagged_moves_le_size_add_paid

#print axioms L4.pair_geometric_fields
#print axioms L4.mcov_step
#print axioms L4.covered_mark_exists_of_not_dvd
#print axioms L4.tagged_moves_le_size_add_paid_of_mcov
