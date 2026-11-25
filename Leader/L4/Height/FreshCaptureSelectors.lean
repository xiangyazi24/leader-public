import Leader.L4.Height.ReleaseGrantReceipt
import Leader.L4.BStarRetainedActualSamples
import Leader.L4.BStarAcquireVisitWitness
import Leader.L4.BStarCopyLeftAcquireBank

namespace L4.Height.FreshCaptureSelectors

open AllSizeProtocol PhysicalCustody ProductionCustody ProductionCycles BStarLongWork BStarLongLayout
open BStarLongDoor BStarLongCommand BStarGeneratedOwner BStarH6WordChart BStarAcquireAnchors
open BStarAcquireLiteralChain BStarGeneratedBandScan BStarResetChartTouch BStarAcquireVisitOrder
open BStarSteeredLikelihood BStarTrace

private theorem capture_legal (w : BitVec LW)
    (legal : ∀ j : Fin 3,((capturedSelector j).read w).toNat<3) :
    selTriple (captures.read w).toNat=true := by
  have left := legal 0
  have center := legal 1
  have right := legal 2
  rw [BStarCopyLeftAcquireBank.left_capture_val] at left
  rw [BStarCopyRightAcquireBank.right_capture_val] at right
  rw [BStarAcquireSource.center_read,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow] at center
  unfold selTriple
  simp only [Bool.and_eq_true_iff,bne_iff_ne,ne_eq]
  exact ⟨⟨by omega,by omega⟩,by omega⟩

/-- All three stored selectors on every computation-band prefix after a real RREL
are legal. The actual winning visits also certify COPY LOAD issue and the center
selector consumed by the final native instruction. -/
theorem legal_on_band {s n : Nat} {x : Raw s n} {g : CustodyWitness x} (P : Production g)
    (o : Owners (oldH6 (rows s) g.base)) (a : Word n) (e : Fin n) (paid : accepted g o a e)
    (w : Word n) :
    let z := rawNext s (rawRun x a) e
    let root := (endpoint (oldH6 (rows s) g.base) g.hh o 0).1
    let y := rawRun z w
    Band y root → (∀ j : Fin 3,((capturedSelector j).read (y root).long).toNat<3) ∧
      initial 8 (y root).long=some (captures.read (y root).long).toNat := by
  let hp : 0<2 := by decide
  let z := rawNext s (rawRun x a) e
  obtain ⟨S,len,fall,C,idle,_⟩ := ReleaseGrantReceipt.released_chart P o a e paid
  let root := (S.getD 0 fall).1
  have eq : root=(endpoint (oldH6 (rows s) g.base) g.hh o 0).1 := congrArg Prod.fst C.root
  have q : g.Q z := g.closed _ e (ready_run P a).1
  obtain ⟨m,G,_,_⟩ := generated_word hp C g.Q g.fiber (fun y hy f => g.closed y f hy)
    (separation P) w .idle q idle
  dsimp only
  intro band
  rw [←eq] at band ⊢
  have origin : Origin hp root z w := by
    rcases BStarGeneratedIdleStage.scan_on_Q hp C g.Q q g.fiber g.closed (separation P) G band with old | actual
    · have low := old.1.1
      have atThree : pc z root=3 := by rw [eq]; exact paid.2.2
      change 6≤pc z root at low
      omega
    · exact actual
  obtain ⟨_,_,_,_,_,_,vs,_,_,_,wins,once,_,fields⟩ :=
    BStarRetainedActualSamples.retained_samples hp C g.Q q g.fiber g.closed (separation P) idle w origin
  have legal (j : Fin 3) : ((capturedSelector j).read (rawRun z w root).long).toNat<3 := by
    obtain ⟨v,mem,atJ,_⟩ := BStarAcquireVisitWitness.incidence_exists vs j (once j) wins
    have E := congrArg Prod.fst (fields v mem)
    rw [atJ] at E
    change ((capturedSelector j).read (rawRun z w root).long).toNat=v.selector.val at E
    exact E.symm ▸ v.selector.isLt
  have good := capture_legal _ legal
  refine ⟨legal,?_⟩
  change (if selTriple (captures.read (rawRun z w root).long).toNat then _ else none)=_
  rw [if_pos good]

#print axioms legal_on_band
end L4.Height.FreshCaptureSelectors
