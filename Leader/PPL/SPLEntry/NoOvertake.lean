import Leader.PPL.SPLEntry.IdGhostProvenance

/-!
# L18: fresh lineages are never overtaken by old ones

In the Lemma-4 window at `k` with `Cd`, every live owner sits on the canonical
trajectory with key `q6Key`.  `NoOvertake`: every old (not `FreshAt k`) owner
in the window has a key strictly larger than the move count of every fresh
owner.  It survives every prime ghost step (`q8_noOvertake_step`):

* a post-step old owner in the window is an unchanged pre-owner or the bump of
  an old pre-owner in the window by one move, whose key grows by exactly one
  (`q8_old_prov`); a birth is fresh, and entry from outside the window is
  impossible by validity;
* a post-step fresh owner is an unchanged fresh pre-owner, a bump of one (one
  more move), or a newborn with one move;
* two distinct owners never share a key (`q6_key_inj`), and when the newborn
  meets a key-0 old owner the right output is unchanged (`q7_LR`).

`q8_oldAbove_step`: the bound "every old owner in the window has key > K"
survives every step.
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false

open PPL

/-- Every old owner in the window is strictly ahead of every fresh owner. -/
def NoOvertake {n psi kappa : Nat} (ring : DirectedRing n) (kind : TokenKind) (k : Fin n)
    (G : GhostConfig n psi kappa) : Prop :=
  ∀ (i : Fin n) (zO : GhostToken n psi) (x : Nat) (j : Fin n) (zF : GhostToken n psi),
    ghostTokenAt kind G i = some zO → x < 2 * psi → i = shiftRight ring k x →
    ¬ FreshAt kind k zO.lmeta →
    ghostTokenAt kind G j = some zF → FreshAt kind k zF.lmeta →
    zF.lmeta.moves < q6Key psi x (decodeOffset psi (tokenCode zO.value))

/-- Every old owner in the window has key larger than `K`. -/
def OldAbove {n psi kappa : Nat} (ring : DirectedRing n) (kind : TokenKind) (k : Fin n)
    (K : Nat) (G : GhostConfig n psi kappa) : Prop :=
  ∀ (i : Fin n) (zO : GhostToken n psi) (x : Nat),
    ghostTokenAt kind G i = some zO → x < 2 * psi → i = shiftRight ring k x →
    ¬ FreshAt kind k zO.lmeta →
    K < q6Key psi x (decodeOffset psi (tokenCode zO.value))

/-- Ghost soundness in public form. -/
theorem q8_sound {n psi kappa : Nat} (G : GhostConfig n psi kappa) (hs : GhostSound G)
    (kind : TokenKind) (i : Fin n) (z : GhostToken n psi)
    (h : ghostTokenAt kind G i = some z) :
    tokenAt kind (G.phys i) = some z.value ∧ q3GLocalValid kind (G.phys i) z.value := by
  cases kind
  · exact hs.1 i z h
  · exact hs.2 i z h

/-- Window validity of an owner. -/
theorem q8_valid {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) (hs : GhostSound G)
    (hCd : Cd ring k kind G.phys) (i : Fin n) (z : GhostToken n psi) (x : Nat)
    (h : ghostTokenAt kind G i = some z) (hx : x < 2 * psi) (hi : i = shiftRight ring k x) :
    q6ValidPt psi x (decodeOffset psi (tokenCode z.value)) := by
  have hv := (q8_sound G hs kind i z h).2
  rw [hi] at hv
  exact q6_validPt_of_local hpsi ring k kind G.phys hCd x hx z.value hv

theorem q8_sr_inj {n : Nat} (ring : DirectedRing n) (k : Fin n) (x y : Nat)
    (hx : x < n) (hy : y < n) (h : shiftRight ring k x = shiftRight ring k y) : x = y := by
  have := congrArg (cyclicOffset ring k) h
  rwa [l18Gapped_cyclicOffset_shiftRight_of_lt ring k _ hx,
    l18Gapped_cyclicOffset_shiftRight_of_lt ring k _ hy] at this

theorem q8_rn {n : Nat} (ring : DirectedRing n) (k : Fin n) (x : Nat) :
    ring.rightNeighbor (shiftRight ring k x) = shiftRight ring k (x + 1) := by
  rw [← l18Gapped_shiftRight_add]
  rfl

/-- Provenance of a post-step owner of one colour. -/
theorem q8_post {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n) (hn2 : 2 ≤ n)
    (st : Nat) (G : GhostConfig n psi kappa) (e : Fin n) (kind : TokenKind)
    (L R : State psi kappa)
    (hL : L = q3LState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e)))
    (hR : R = q3RState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e)))
    (s : Fin n) (z' : GhostToken n psi)
    (h : ghostTokenAt kind (ghostStepPrime hpsi ring st G e) s = some z') :
    ghostTokenAt kind G s = some z' ∨
      (s = ring.rightNeighbor e ∧ ∃ z0 v,
        ((ghostTokenAt kind G e = some z0 ∧ q3GLiveValue kind L = some z0.value) ∨
          (z0 = q3GBirth hpsi kind st e L.id ∧ L.dist.val = tokenD' psi kind ∧
            q3GLiveValue kind L = none)) ∧
        q3MoveR hpsi z0.value v ∧ z' = q3Bump z0 v ∧
        (L.last = false ∧ R.last = false) ∧ q3GLiveValue kind R = none) ∨
      (s = e ∧ ∃ z0 v, ghostTokenAt kind G (ring.rightNeighbor e) = some z0 ∧
        q3MoveL hpsi L z0.value v ∧ z' = q3Bump z0 v) := by
  by_cases hse : s = e
  · rw [hse] at h ⊢
    rw [ghostTokenAt_ghostStep_initiator_prime, q3_selected_eq', ← hL, ← hR] at h
    rcases q3_left_cases hpsi kind st e L R _ _ z' h with hk | ⟨z0, v, hgr, hmv, hz, _⟩
    · exact Or.inl hk
    · exact Or.inr (Or.inr ⟨rfl, z0, v, hgr, hmv, hz⟩)
  · by_cases hsr : s = ring.rightNeighbor e
    · rw [hsr] at h ⊢
      rw [ghostTokenAt_ghostStep_responder_of_ne_prime hpsi ring st G e kind
        (rightNeighbor_ne ring hn2 e), q3_selected_eq', ← hL, ← hR] at h
      rcases q7_right_cases hpsi kind st e L R _ _ z' h with hk |
          ⟨z0, v, hsrc, hmv, hz, _, hgate, hrn⟩
      · exact Or.inl hk
      · exact Or.inr (Or.inl ⟨rfl, z0, v, hsrc, hmv, hz, hgate, hrn⟩)
    · left
      rw [ghostTokenAt_ghostStep_frame_prime hpsi ring st G e s kind hse hsr] at h
      exact h

/-- Step-level form of `q7_LR`. -/
theorem q8_LR {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n) (hn2 : 2 ≤ n)
    (st : Nat) (G : GhostConfig n psi kappa) (e : Fin n) (kind : TokenKind)
    (zl zr : GhostToken n psi)
    (hl : ghostTokenAt kind (ghostStepPrime hpsi ring st G e) e = some zl)
    (hr : ghostTokenAt kind (ghostStepPrime hpsi ring st G e) (ring.rightNeighbor e) = some zr) :
    ghostTokenAt kind G (ring.rightNeighbor e) = some zr := by
  rw [ghostTokenAt_ghostStep_initiator_prime, q3_selected_eq'] at hl
  rw [ghostTokenAt_ghostStep_responder_of_ne_prime hpsi ring st G e kind
    (rightNeighbor_ne ring hn2 e), q3_selected_eq'] at hr
  exact q7_LR hpsi kind st e _ _ _ _ zl zr hl hr

/-- A right-moved valid point is not at window position 0. -/
theorem q8_moveR_pos {psi x : Nat} (hpsi : 2 ≤ psi) (t v : TokenData psi)
    (hV : q6ValidPt psi x (decodeOffset psi (tokenCode v))) (hmv : q3MoveR hpsi t v) :
    1 ≤ x := by
  have hvo := decodeOffset_valid psi (by omega) (tokenCode t)
  unfold ValidOffset at hvo
  unfold q6ValidPt at hV
  rcases hmv with ⟨h1, hv⟩ | ⟨h2, hdv, _, _⟩
  · rw [hv, q6_decode_negPsi] at hV
    omega
  · rw [hdv] at hV
    omega

/-- A left-moved valid point is not at the last window position. -/
theorem q8_moveL_pos {psi kappa x : Nat} (hpsi : 2 ≤ psi) (l : State psi kappa)
    (t v : TokenData psi)
    (hV : q6ValidPt psi x (decodeOffset psi (tokenCode v))) (hmv : q3MoveL hpsi l t v) :
    x + 1 < 2 * psi := by
  have hvo := decodeOffset_valid psi (by omega) (tokenCode t)
  unfold ValidOffset at hvo
  unfold q6ValidPt at hV
  rcases hmv with ⟨h1, hv⟩ | ⟨h2, hdv, _, _⟩
  · rw [hv, q6_decode_turn] at hV
    omega
  · rw [hdv] at hV
    omega

/-- Under `Cd`, the only window position with `dist = d'` is `0`. -/
theorem q8_dist_zero {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (C : Config n psi kappa) (hCd : Cd ring k kind C) (y : Nat)
    (hy : y < 2 * psi) (hd : (C (shiftRight ring k y)).dist.val = tokenD' psi kind) : y = 0 := by
  have h := (hCd ⟨y, hy⟩).1
  dsimp only at h
  rw [hd] at h
  cases kind with
  | black =>
      simp only [tokenD', Nat.add_zero] at h
      rw [Nat.mod_eq_of_lt hy] at h
      omega
  | white =>
      simp only [tokenD'] at h
      by_cases hyp : y < psi
      · rw [Nat.mod_eq_of_lt (by omega)] at h
        omega
      · rw [show y + psi = (y - psi) + 2 * psi by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)] at h
        omega

/-- Provenance of a post-step old owner in the window. -/
theorem q8_old_prov {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (h2n : 2 * psi < n) (k : Fin n) (kind : TokenKind) (st : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (ghostStepPrime hpsi ring st G e).phys)
    (hs : GhostSound G) (hs' : GhostSound (ghostStepPrime hpsi ring st G e))
    (i' : Fin n) (zO' : GhostToken n psi) (x' : Nat)
    (hO' : ghostTokenAt kind (ghostStepPrime hpsi ring st G e) i' = some zO')
    (hx' : x' < 2 * psi) (hi' : i' = shiftRight ring k x')
    (hold : ¬ FreshAt kind k zO'.lmeta) :
    ∃ (i : Fin n) (zO : GhostToken n psi) (x : Nat),
      ghostTokenAt kind G i = some zO ∧ x < 2 * psi ∧ i = shiftRight ring k x ∧
      ¬ FreshAt kind k zO.lmeta ∧
      ((i = i' ∧ zO = zO' ∧ x = x') ∨
        q6Key psi x (decodeOffset psi (tokenCode zO.value)) + 1 =
          q6Key psi x' (decodeOffset psi (tokenCode zO'.value))) := by
  have hn2 : 2 ≤ n := by omega
  have hVO' := q8_valid hpsi ring k kind _ hs' hCd' i' zO' x' hO' hx' hi'
  rcases q8_post hpsi ring hn2 st G e kind _ _ rfl rfl i' zO' hO' with hk |
      ⟨hs0, z0, v, hsrc, hmv, hz, _, _⟩ | ⟨hs0, z0, v, hgr, hmv, hz⟩
  · exact ⟨i', zO', x', hk, hx', hi', hold, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · subst hz
    have hx1 : 1 ≤ x' := q8_moveR_pos hpsi z0.value v hVO' hmv
    have he : e = shiftRight ring k (x' - 1) := by
      apply pred_of_rightNeighbor ring e k (x' - 1) (by omega)
      rw [← hs0, hi', show x' - 1 + 1 = x' by omega]
    rcases hsrc with ⟨hgl, _⟩ | ⟨hbirth, hdist, _⟩
    · have hold0 : ¬ FreshAt kind k z0.lmeta := hold
      have hV0 := q8_valid hpsi ring k kind G hs hCd e z0 (x' - 1) hgl (by omega) he
      have hkey := q6_key_moveR hpsi z0.value v hV0 hmv
      rw [show x' - 1 + 1 = x' by omega] at hkey
      exact ⟨e, z0, x' - 1, hgl, by omega, he, hold0, Or.inr hkey.symm⟩
    · exfalso
      subst hbirth
      have hlf := lstate_frame hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))
      rw [hlf.2] at hdist
      rw [he] at hdist
      have hy0 := q8_dist_zero hpsi ring k kind G.phys hCd (x' - 1) (by omega) hdist
      apply hold
      refine ⟨st, rfl, ?_⟩
      show e = k
      rw [he, hy0]
      exact sr_zero ring k
  · subst hz
    have hx1 : x' + 1 < 2 * psi := q8_moveL_pos hpsi _ z0.value v hVO' hmv
    have hr : ring.rightNeighbor e = shiftRight ring k (x' + 1) := by
      rw [← hs0, hi']; exact q8_rn ring k x'
    have hold0 : ¬ FreshAt kind k z0.lmeta := hold
    have hV0 := q8_valid hpsi ring k kind G hs hCd _ z0 (x' + 1) hgr hx1 hr
    have hkey := q6_key_moveL hpsi _ z0.value v hV0 hmv
    rw [show x' + 1 - 1 = x' by omega] at hkey
    exact ⟨_, z0, x' + 1, hgr, hx1, hr, hold0, Or.inr hkey.symm⟩

/-- `OldAbove K` survives every step. -/
theorem q8_oldAbove_step {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (h2n : 2 * psi < n) (k : Fin n) (kind : TokenKind) (st : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (ghostStepPrime hpsi ring st G e).phys)
    (hs : GhostSound G) (hs' : GhostSound (ghostStepPrime hpsi ring st G e))
    (K : Nat) (hA : OldAbove ring kind k K G) :
    OldAbove ring kind k K (ghostStepPrime hpsi ring st G e) := by
  intro i' zO' x' hO' hx' hi' hold
  obtain ⟨i, zO, x, hO, hx, hi, hold0, hrel⟩ :=
    q8_old_prov hpsi ring h2n k kind st G e hCd hCd' hs hs' i' zO' x' hO' hx' hi' hold
  have hlt := hA i zO x hO hx hi hold0
  rcases hrel with ⟨_, rfl, rfl⟩ | h
  · exact hlt
  · omega

/-- The move count of a live fresh owner is the key of its window point. -/
theorem q8_fresh_point {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (k : Fin n) (kind : TokenKind) (G : GhostConfig n psi kappa)
    (hkin : Lemma4FreshKinematics ring k G) (hF : FreshPay ring kind k G)
    (j : Fin n) (zF : GhostToken n psi)
    (hj : ghostTokenAt kind G j = some zF) (hfr : FreshAt kind k zF.lmeta) :
    ∃ y, y < 2 * psi ∧ j = shiftRight ring k y ∧
      zF.lmeta.moves = q6Key psi y (decodeOffset psi (tokenCode zF.value)) := by
  obtain ⟨y, hy, htraj⟩ := hkin kind j zF hj hfr
  have hq := (hF j zF hj hfr).1
  refine ⟨y, ?_, hy, q6_key_of_traj _ _ _ _ htraj⟩
  rcases htraj with ⟨q, hc, hle, hx, hm⟩ | ⟨q, hc, hle, hx, hm⟩
  · rw [hm, divq _ _ _ (by omega)] at hq
    omega
  · rw [hm, divq _ _ _ (by omega)] at hq
    omega

/-- One prime ghost step preserves `NoOvertake`. -/
theorem q8_noOvertake_step {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (h2n : 2 * psi < n) (k : Fin n) (kind : TokenKind) (st : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (ghostStepPrime hpsi ring st G e).phys)
    (hs : GhostSound G) (hs' : GhostSound (ghostStepPrime hpsi ring st G e))
    (hkin' : Lemma4FreshKinematics ring k (ghostStepPrime hpsi ring st G e))
    (hF' : FreshPay ring kind k (ghostStepPrime hpsi ring st G e))
    (hNO : NoOvertake ring kind k G) :
    NoOvertake ring kind k (ghostStepPrime hpsi ring st G e) := by
  have hn2 : 2 ≤ n := by omega
  intro i' zO' x' j' zF' hO' hx' hi' hold hFj hfr
  obtain ⟨y', hy', hj', hmv⟩ := q8_fresh_point hpsi ring k kind _ hkin' hF' j' zF' hFj hfr
  have hVF := q8_valid hpsi ring k kind _ hs' hCd' j' zF' y' hFj hy' hj'
  have hVO := q8_valid hpsi ring k kind _ hs' hCd' i' zO' x' hO' hx' hi'
  suffices hle : zF'.lmeta.moves ≤ q6Key psi x' (decodeOffset psi (tokenCode zO'.value)) by
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      rw [hmv] at h
      obtain ⟨hxy, _⟩ := q6_key_inj hpsi hVF hVO h
      have hji : j' = i' := by rw [hj', hi', hxy]
      rw [hji, hO'] at hFj
      have hz : zO' = zF' := Option.some.inj hFj
      rw [hz] at hold
      exact hold hfr
  obtain ⟨i, zO, x, hO, hx, hi, hold0, hrel⟩ :=
    q8_old_prov hpsi ring h2n k kind st G e hCd hCd' hs hs' i' zO' x' hO' hx' hi' hold
  have hkle : q6Key psi x (decodeOffset psi (tokenCode zO.value)) ≤
      q6Key psi x' (decodeOffset psi (tokenCode zO'.value)) := by
    rcases hrel with ⟨_, rfl, rfl⟩ | h
    · exact Nat.le_refl _
    · omega
  rcases q8_post hpsi ring hn2 st G e kind _ _ rfl rfl j' zF' hFj with hk |
      ⟨hs0, z0, v, hsrc, hmvR, hz, _, _⟩ | ⟨hs0, z0, v, hgr, hmvL, hz⟩
  · have := hNO i zO x j' zF' hO hx hi hold0 hk hfr
    omega
  · subst hz
    rcases hsrc with ⟨hgl, _⟩ | ⟨hbirth, _, _⟩
    · have hfr0 : FreshAt kind k z0.lmeta := hfr
      have := hNO i zO x e z0 hO hx hi hold0 hgl hfr0
      show z0.lmeta.moves + 1 ≤ _
      omega
    · subst hbirth
      show 0 + 1 ≤ _
      by_cases h1 : 1 ≤ q6Key psi x' (decodeOffset psi (tokenCode zO'.value))
      · omega
      · exfalso
        have hk0 : q6Key psi x' (decodeOffset psi (tokenCode zO'.value)) = 0 := by omega
        have hx0 := q6_key_zero hpsi hVO hk0
        obtain ⟨tb, _, hsite⟩ := hfr
        have hek : e = k := hsite
        have hie : i' = e := by rw [hi', hx0, sr_zero, hek]
        rw [hie] at hO'
        rw [hs0] at hFj
        have hpre := q8_LR hpsi ring hn2 st G e kind zO' _ hO' hFj
        have hfr1 : FreshAt kind k (q3Bump (q3GBirth hpsi kind st e
            (q3LState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))).id) v).lmeta :=
          ⟨st, rfl, hek⟩
        have := hNO i zO x _ _ hO hx hi hold0 hpre hfr1
        omega
  · subst hz
    have hfr0 : FreshAt kind k z0.lmeta := hfr
    have := hNO i zO x _ z0 hO hx hi hold0 hgr hfr0
    show z0.lmeta.moves + 1 ≤ _
    omega

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.q8_old_prov
#print axioms PPL.Convergence.L18.q8_oldAbove_step
#print axioms PPL.Convergence.L18.q8_noOvertake_step
