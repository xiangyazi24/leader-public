import Leader.L4.BStarCaptureInterval
import Leader.L4.BStarLongGrantProjection

/-! A canonically held reader excludes every actual publication at
that old endpoint; selector equality is neither used nor sufficient.
The theorem counts inherited successful COMMIT exactly like one
generated after the reset cut. -/
namespace L4.BStarReaderExclusion
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongClaims
open BStarLongGrant BStarLongEvents BStarLongPublication BStarLongWork

theorem writer_false (old : Ports) (j : Fin 3) (ne : j≠1)
    (h : canonical old j=true) : old 1=false := by
  cases e : old 1
  · rfl
  · simp [canonical,e,ne] at h

theorem event_ne_reader (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side)
    (j : Fin 3) (ne : j≠1) (held : canonical (original (BStarLongGrant.atOld x s)) j=true) :
    ∀ e∈(longTrace g x).publications, e.endpoint≠s := by
  have w := writer_false (original (BStarLongGrant.atOld x s)) j ne held
  intro e he side
  obtain ⟨c,p,_,hs,H⟩ := (literal_event_iff g x e).mp he
  obtain ⟨_,_,_,_,d,_,_,K⟩ := H
  have S : c.source.side=s := hs.symm.trans side
  unfold BStarLongPublication.guard typedGuard at K
  have E : ((grant 1).read (BStarLongWork.atOld x c.source)).getLsbD 0=false := by
    change ((grant 1).read (lane (c.source.side==.right) x)).getLsbD 0=false
    rw [S]
    exact w
  simp only [E,Bool.false_and,Bool.and_false,Bool.false_eq_true] at K

/-- On a marked reader interval one need only prove ownership compatibility
for the selected STAGE cases: no-publication at this endpoint is literal. -/
theorem reader_safe (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side)
    (j : Fin 3) (ne : j≠1) (held : canonical (original (BStarLongGrant.atOld x s)) j=true)
    (b : Fin 3)
    (owned : ∀ c p, (c,BStarLongCommand.Offer.advance p)∈BStarBankTrace.offers g x →
      c.source.side=s → BStarBankTrace.StageLiveAt g x b c p) :
    ∀ o∈BStarBankTrace.offers g x, BStarBankTrace.SafeOffer g x s b o :=
  BStarCaptureInterval.safe_from_events g x s b owned (event_ne_reader g x s j ne held)

/-- At the reader's header, even a forged STAGE fails literal
authorization, so no descriptor witness is needed for this mark. -/
theorem header_reader_safe (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side)
    (j : Fin 3) (ne : j≠1) (held : canonical (original (BStarLongGrant.atOld x s)) j=true)
    (b : Fin 3) (head : (BStarLongCommand.geometry g s).axes.h6=true) :
    ∀ o∈BStarBankTrace.offers g x, BStarBankTrace.SafeOffer g x s b o := by
  apply reader_safe g x s j ne held b
  intro c p _ hs
  intro _ _ _ _ d _ H
  have w := writer_false (original (BStarLongGrant.atOld x s)) j ne held
  have E : ((grant 1).read (BStarLongWork.atOld x c.source)).getLsbD 0=false := by
    change ((grant 1).read (lane (c.source.side==.right) x)).getLsbD 0=false
    rw [hs]
    exact w
  have h : (BStarLongCommand.geometry g c.source.side).axes.h6=true := hs.symm ▸ head
  simp only [h,BStarLongOutgoing.actual,E,Bool.false_and,Bool.not_false,Bool.true_and] at H
  contradiction

/-- On the actual pair transition, the reader's old header protects its
physical bank on that edge. The incidence itself persists when no
effective release was selected; release cannot authorize a same-mark
publication because inputs use the old grants. -/
theorem bStar_reader_step (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (s : Side) (j : Fin 3) (ne : j≠1) (bank : Fin 3) :
    let producer := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry producer) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (BStarLongCommand.geometry g s).axes.h6=true →
    canonical (original (BStarLongGrant.atOld raw s)) j=true →
    BStarCaptureInterval.HeldStep bank (lane (BStarBankTrace.sideFlag s) x).long
        (lane (BStarBankTrace.sideFlag s) (largePair producer x)).long ∧
    (requested (BStarLongCommandData.round g raw).offered s j releaseOp=false →
      BStarLongGrantProjection.read (Pair.map LargeSite.long (largePair producer x)) s j=1) := by
  dsimp only
  intro h old
  refine ⟨BStarCaptureInterval.bStar_held_step _ _ _ _ _ _ _ _ _ hp x s bank
      (header_reader_safe _ _ s j ne old bank h),?_⟩
  exact BStarLongGrantProjection.joined_keeps_incidence _ _ _ _ _ _ _ _ _ hp x s j h old

#print axioms header_reader_safe
#print axioms bStar_reader_step
#print axioms reader_safe
end L4.BStarReaderExclusion
