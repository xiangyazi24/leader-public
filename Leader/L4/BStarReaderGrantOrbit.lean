import Leader.L4.BStarReaderExclusion

/-! Readout of the next canonical grant through an actual mark. These
lemmas seed and preserve a header reader; assigning global ownership
to the release requests is a separate history obligation. -/
namespace L4.BStarReaderGrantOrbit
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongLayout
open BStarLongGrant BStarLongWork BStarLongCommand
open BStarLongGrantProjection BStarReaderExclusion

theorem result_coherent (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (os : Offers) (s : Side) :
    conflict (grants g raw os s)=false := by
  cases h : (geometry g s).axes.h6
  · simp [conflict,grants,h]
  · let old := original (BStarLongGrant.atOld raw s)
    let release := fun j => requested os s j releaseOp
    let ask := fun j => requested os s j acquire
    have H : grants g raw os s=result old release ask := by
      funext j
      simp [grants,h,old,release,ask]
    rw [H]
    exact BStarGrantRetention.coherent_succ old release ask

theorem joined_canonical (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (s : Side) (j : Fin 3) :
    let producer := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry producer) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let newRaw : Pair (BitVec LW) := Pair.map LargeSite.long (largePair producer x)
    canonical (original (BStarLongGrant.atOld newRaw s)) j =
      grants g raw (BStarLongCommandData.round g raw).offered s j := by
  dsimp only
  let producer := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry producer) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let newRaw : Pair (BitVec LW) := Pair.map LargeSite.long (largePair producer x)
  let os := (BStarLongCommandData.round g raw).offered
  have O (i : Fin 3) : original (BStarLongGrant.atOld newRaw s) i = grants g raw os s i := by
    have P := joined_grants k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x s i
    change read newRaw s i=BitVec.ofBool (grants g raw os s i) at P
    have E := congrArg (fun z : BitVec 1 => z.getLsbD 0) P
    change (BStarLongGrantProjection.read newRaw s i).getLsbD 0=_
    rw [E]
    cases grants g raw os s i <;> rfl
  have E : original (BStarLongGrant.atOld newRaw s)=grants g raw os s := funext O
  change canonical (original (BStarLongGrant.atOld newRaw s)) j=grants g raw os s j
  rw [E]
  exact canonical_clean _ (result_coherent g raw os s) j

/-- Canonical reader, old header and no own release suffice for
closure of both the old snapshot and the canonical held readout. -/
theorem reader_header_keeps (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (s : Side) (j : Fin 3) (ne : j≠1) (bank : Fin 3) :
    let producer := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry producer) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let newRaw : Pair (BitVec LW) := Pair.map LargeSite.long (largePair producer x)
    (geometry g s).axes.h6=true →
    canonical (original (BStarLongGrant.atOld raw s)) j=true →
    requested (BStarLongCommandData.round g raw).offered s j releaseOp=false →
    BStarCaptureInterval.HeldStep bank (lane (BStarBankTrace.sideFlag s) x).long
        (lane (BStarBankTrace.sideFlag s) (largePair producer x)).long ∧
      canonical (original (BStarLongGrant.atOld newRaw s)) j=true := by
  dsimp only
  intro hh held nr
  refine ⟨(bStar_reader_step _ _ _ _ _ _ _ _ _ hp x s j ne bank hh held).1,?_⟩
  rw [joined_canonical]
  simp [grants,hh,BStarGrantRetention.keep_canonical _ _ _ j held,nr]

/-- A selected winning request at the old header seeds the next held
incidence, using the request and grant decision evaluated on old bytes. -/
theorem acquisition_seeds (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (s : Side) (j : Fin 3) :
    let producer := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry producer) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let newRaw : Pair (BitVec LW) := Pair.map LargeSite.long (largePair producer x)
    let os := (BStarLongCommandData.round g raw).offered
    (geometry g s).axes.h6=true →
    win (original (BStarLongGrant.atOld raw s)) (fun i => requested os s i releaseOp)
      (fun i => requested os s i acquire) j=true →
    canonical (original (BStarLongGrant.atOld newRaw s)) j=true := by
  dsimp only
  intro hh win
  rw [joined_canonical]
  simp [grants,hh,result,win]

end L4.BStarReaderGrantOrbit
