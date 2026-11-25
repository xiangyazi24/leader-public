import Leader.L4.TripleResidual
import Leader.L4.RootlessFIFO

namespace L4.RestartAudit
open RankSupplier

/-- On a non-retiring stop of the fixed-supplier push with the supplier
still alive, the actual newly living target is its immediate successor.
Use the physical updated offset, not the observer's frozen numeric field. -/
theorem supplier_birth_exit {p c n : Nat} (hn : 4≤n) (v e : Fin n)
    (s : Obs p c n) (hs : Live v s) (ht : (advance v s e).stopped=true)
    (hR : RankPhysical.retirement s.config e=false)
    (hAlive : (step s.config e v).leader=true) :
    let pay := geometricPay (s.config e) (s.config (rightNeighbor e))
    let d := s.donor + ((e == liftedSite v s.donor) && pay).toNat
    let y := step s.config e
    FirstMark y v d ∧ d+1<n ∧ (y (liftedSite v (d+1))).leader=true := by
  let pay := geometricPay (s.config e) (s.config (rightNeighbor e))
  let d := s.donor + ((e == liftedSite v s.donor) && pay).toNat
  let y := step s.config e
  have hRet : (pay && (s.config (rightNeighbor e)).mark)=false := hR
  have hF : FirstMark y v d ∧ d+1<n :=
    firstMark_after_supplier_step hn s.config v e hs.2.1 hs.2.2.2.2.1
      hs.2.2.2.2.2 hs.2.2.1 hAlive hRet
  have hStop : stop s.config y v e d pay=true := by
    unfold advance at ht
    simp only [hs.1,Bool.false_eq_true,if_false] at ht
    change (if stop s.config y v e d pay then (⟨y,s.donor,true⟩ : Obs p c n)
      else ⟨y,d,false⟩).stopped = true at ht
    split at ht
    · assumption
    · contradiction
  refine ⟨hF.1,hF.2,?_⟩
  change (y v).leader=true at hAlive
  simpa [stop,hRet,hAlive] using hStop

/-- While no native death or retirement intervenes, the already
prepared first sector stays root-free through the second target's
actual terminal birth mark. This is a two-consecutive-root handoff,
not a statement about the order of currently living leaders. -/
theorem second_birth_joins_first_sector {p c n a : Nat}
    (hn : 4≤n) (u e : Fin n) (s : Obs p c n)
    (hs : Live (liftedSite u (a+1)) s)
    (hCover : COV s.config)
    (hU : (s.config u).leader=true)
    (hPrior : FirstMark s.config u a) (ha : a+1<n)
    (hStop : (advance (liftedSite u (a+1)) s e).stopped=true)
    (hEvent : TripleResidual.event s.config e=false) :
    let v := liftedSite u (a+1)
    let pay := geometricPay (s.config e) (s.config (rightNeighbor e))
    let d := s.donor + ((e == liftedSite v s.donor) && pay).toNat
    let y := step s.config e
    FirstMark y u a ∧ FirstMark y v d ∧ d+1<n ∧
      (y u).leader=true ∧ (y v).leader=true ∧ (y (liftedSite v (d+1))).leader=true := by
  let v := liftedSite u (a+1)
  have hKeepU := TripleResidual.no_event_preserves_leader hn s.config e u hCover hEvent hU
  have hKeepV := TripleResidual.no_event_preserves_leader hn s.config e v hCover hEvent hs.2.2.1
  have hR : RankPhysical.retirement s.config e=false := (Bool.or_eq_false_iff.mp hEvent).2
  have hFirst := TripleResidual.no_event_sector hn s.config e u hs.2.1 hCover hEvent
    hU hs.2.2.1 hPrior ha
  have hSecond := supplier_birth_exit hn v e s hs hStop hR hKeepV
  exact ⟨hFirst,hSecond.1,hSecond.2.1,hKeepU,hKeepV,hSecond.2.2⟩

end L4.RestartAudit
#print axioms L4.RestartAudit.supplier_birth_exit
#print axioms L4.RestartAudit.second_birth_joins_first_sector
