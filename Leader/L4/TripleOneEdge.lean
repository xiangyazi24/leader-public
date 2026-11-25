import Leader.L4.TripleBoundary
import Leader.L4.TripleVulnerable

namespace L4.TripleOneEdge
open TripleResidual TriplePhase TripleControlled TripleVulnerable TripleBoundary

private def stop {p c n} (x : Physical p c n) : Prop := x.obs.stopped=true

private def admitted {p c n} (s : Fin n) (a : Nat) (x : Physical p c n) : Prop :=
  stop x ∨ (MCOV x.obs.config ∧ COV x.obs.config ∧
    Paired x.obs.config s a 0 x.left x.right)

/-- Includes a separate paid unit for the exceptional initially live target. -/
def value {p c n} (a : Nat) (x : Physical p c n) : Nat :=
  if x.obs.stopped then 0 else
    if x.right = .forward .live 0 then 5*(a+1)-1
    else (coordinate x.left).value (a+1)

private theorem keep {p c n} (hn : 4≤n) (s : Fin n) (a : Nat)
    (x : Physical p c n) (e : Fin n) (h : admitted s a x) :
    admitted s a (effectiveNext s a 0 x e) := by
  rcases h with h|⟨hm,hc,hp⟩
  · left; simp [stop,effectiveNext,advance,show x.obs.stopped=true from h]
  by_cases hs : x.obs.stopped=true
  · left; simp [stop,effectiveNext,advance,hs]
  have hf := Bool.eq_false_iff.mpr hs
  by_cases he : event x.obs.config e=true
  · left; simp [stop,effectiveNext,advance,hf,he]
  have he' := Bool.eq_false_iff.mpr he
  have H := paired_tick_literal hn x.obs.config s e hm hc x.left x.right hp he'
  have C := EntranceCover.cover_closed hn x.obs.config e ⟨hm,hc⟩
  right
  simpa [effectiveNext,advance,hf] using And.intro C.1 (And.intro C.2 H)

private theorem forms {p c n} (x : Config p c n) (s : Fin n) (q : Phase)
    (h : q.Holds x s 0) :
    q=.ready ∨ q=.forward .dummy 0 ∨ q=.forward .live 0 := by
  cases q with
  | ready => exact .inl rfl
  | returning k q => have H := h.1.le; omega
  | forward k q =>
    have H := (show SealedFront x s 0 q k from h).within
    have E : q=0 := by omega
    subst q
    cases k
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)

private theorem ordinary_keep {n} (s : Fin n) (q : Phase)
    (h : q=.ready ∨ q=.forward .dummy 0) (e : Fin n) :
    q.tick s 0 e ≠ .forward .live 0 := by
  rcases h with rfl|rfl
  · by_cases he : e=s <;> by_cases hi : rightNeighbor e=s <;> simp [Phase.tick,he,hi]
  · by_cases he : e=s <;> simp [Phase.tick,liftedSite_zero,he]

private theorem cap {p c n} (s : Fin n) (a : Nat) (x : Physical p c n)
    (h : admitted s a x) :
    value a x≤5*(a+1)-1 := by
  by_cases hs : x.obs.stopped=true
  · simp [value,hs]
  · obtain ⟨_,_,hp⟩ := h.resolve_left hs
    have hf := Bool.eq_false_iff.mpr hs
    have hc := Attack.value_le (a+1) _ (coordinate_valid _ s _ hp.attacker)
    by_cases hR : x.right=.forward .live 0 <;> simp [value,hf,hR] <;> omega

private theorem ordinary_value {p c n} (a : Nat) (x : Physical p c n)
    (h : x.right≠.forward .live 0) :
    value a x=(actualAttack x).value (a+1) := by
  cases hs : x.obs.stopped <;> simp [value,actualAttack,hs,h,Attack.value]

private theorem pred_distinct {n : Nat} (hn : 4≤n) (s : Fin n) :
    RearTrace.predecessor s≠s := by
  intro h
  have H := RearTrace.right_predecessor s
  rw [h] at H
  have H' : liftedSite s 1=liftedSite s 0 := by simpa [liftedSite_succ,liftedSite_zero] using H
  have hh := liftedSite_inj s (by omega : 1<n) (by omega : 0<n) H'
  omega

private theorem drift {p c n} (hn : 4≤n) (s : Fin n) (a : Nat)
    (x : Physical p c n) (h : admitted s a x) (hs : ¬ stop x) :
    1 ≤ BarrierIID.edgeSum (fun e => (value a x : Int)-(value a (effectiveNext s a 0 x e) : Int)) := by
  have hf : x.obs.stopped=false := Bool.eq_false_iff.mpr hs
  obtain ⟨_,_,hp⟩ := h.resolve_left hs
  let j := liftedSite s (a+1)
  by_cases hr : x.right=.forward .live 0
  · have hv : value a x=5*(a+1)-1 := by simp [value,hf,hr]
    rw [hv]
    apply progress_raw_drift _ j
    · have H : (effectiveNext s a 0 x j).right=.ready := by
        simp [effectiveNext,hr,Phase.tick,liftedSite_zero,j]
      have hg := keep hn s a x j h
      by_cases ht : (effectiveNext s a 0 x j).obs.stopped=true
      · simp [value,ht]; omega
      · have hF := Bool.eq_false_iff.mpr ht
        have hV := Attack.value_le (a+1) _ (coordinate_valid _ s _
          (hg.resolve_left ht).2.2.attacker)
        simp [value,hF,H]
        omega
    · exact fun e => cap s a _ (keep hn s a x e h)
  · have ho : x.right=.ready ∨ x.right=.forward .dummy 0 := by
      rcases forms x.obs.config j x.right hp.target with hR|hD|hL
      · exact .inl hR
      · exact .inr hD
      · exact (hr hL).elim
    have hd : DummyCycle x.right := by rcases ho with H|H <;> simp [H,DummyCycle]
    have hpv (e : Fin n) : value a (effectiveNext s a 0 x e)=
        (actualAttack (effectiveNext s a 0 x e)).value (a+1) :=
      ordinary_value a _ (ordinary_keep j x.right ho e)
    simp only [hpv,ordinary_value a x hr,actualAttack,hf,Bool.false_eq_true,if_false]
    by_cases hl : x.left=.ready
    · have hpair : Paired x.obs.config s a 0 .ready x.right := hl ▸ hp
      have R := effective_ready_bounds hn s x hf hpair hl hd
      rw [hl]
      change 1 ≤ BarrierIID.edgeSum (fun e => ((3*(a+1)-1 : Nat) : Int) -
        ((actualAttack (effectiveNext s a 0 x e)).value (a+1) : Int))
      exact ready_raw_drift (a+1) (by omega) (RearTrace.predecessor s) s
        (pred_distinct hn s) _ (R.1 _ rfl) (R.2.1 _ rfl) (fun e he _ => R.2.2 e he)
    · obtain ⟨q,_,H,J⟩ := effective_nonready_bounds s x hf hp hd hl
      exact progress_raw_drift _ (liftedSite s q) _ H J

private theorem cost_pullback {p c n} (s : Fin n) (a : Nat) (t : Nat) (x : Physical p c n) :
    iidHitCost (effectiveNext s a 0) stop t x =
      iidHitCost advance (fun z => z.stopped=true) t x.obs := by
  classical
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases hs : x.obs.stopped=true
    · simp only [iidHitCost,stop,hs,if_true]
    · simp only [iidHitCost,stop,hs,ih,effectiveNext]

/-- The exact literal one-edge boundary required by TripleBoundary,
valid even when the supplied right phase starts forward-live, and
without assumptions on the residue or counter parameters. -/
theorem oneEdge {p c n a : Nat} (hn : 4≤n) (s : Fin n) (z : Obs p c n)
    (hz : Certified s a 0 z) :
    IIDExpectedHittingTimeAtMost advance (fun u => u.stopped=true) z (6*n*(a+1+1)) := by
  obtain ⟨hm,hc,l,r,hp⟩ := hz
  let x : Physical p c n := ⟨z,l,r⟩
  have hx : admitted s a x := .inr ⟨hm,hc,hp⟩
  have H := mean_of_potential (effectiveNext s a 0) stop (admitted s a) (value a)
    (fun v e h _ => keep hn s a v e h) (drift hn s a) x hx
  intro t
  rw [←show x.obs=z from rfl,←cost_pullback s a t x]
  apply Nat.le_trans (H t)
  apply Nat.mul_le_mul_right
  apply Nat.le_trans (Nat.mul_le_mul_left n (cap s a x hx))
  rw [Nat.mul_comm 6 n, Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  omega

end L4.TripleOneEdge

#print axioms L4.TripleOneEdge.oneEdge
