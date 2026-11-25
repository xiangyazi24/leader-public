import Leader.L4.WindowFourHeadCut

namespace L4.WindowFourHeadCap
open WindowFourHeadCut WindowFourHeadTrace SevenTagCharge

/-- Charge only a genuine payment by the selected J tag. Exterior
retirement and nonpayment marks are still executed and carry zero charge. -/
def jCharge {p c n : Nat} (q : Cursor p c n) (e : Fin n) : Nat :=
  if moves q.ledger e q.j then 1 else 0

def totalJ {p c n : Nat} (q : Cursor p c n) : List (Fin n) → Nat
  | [] => 0
  | e::t => jCharge q e + totalJ (tick q e) t

theorem one_step {p c n : Nat} (hn : 4≤n)
    (g : List (Fin n)) (q : Cursor p c n) (e a b k : Fin n)
    (hq : Geometry q.ledger q.j q.w q.k a b k q.index q.width)
    (ht : Covers q.ledger.config q.ledger.slots) (ha : a∈g) (hab : a≠b)
    (hkeep : WindowLocal.selectedGroupLoss g q.ledger e=none) :
    (tick q e).index+jCharge q e=q.index+wCharge q e := by
  have hjw : q.j≠q.w := by
    intro he
    have he' : some a=some b := hq.jTag.symm.trans (he ▸ hq.wTag)
    exact hab (Option.some.inj he')
  by_cases hj : moves q.ledger e q.j
  · have hw : ¬moves q.ledger e q.w := fun hw => hjw (hj.1.symm.trans hw.1)
    have hc := (tracked_paid_transfer hn q.ledger g e a ht ha
      (hj.1.symm ▸ hq.jTag) hkeep hj.2).1
    have hpos : 0<q.index := by
      by_cases hh : 0<q.index
      · exact hh
      exfalso
      have hz : q.index=0 := by omega
      have he : rightNeighbor q.j=q.w := by simpa [hz,liftedSite_zero] using hq.wLift
      rw [hj.1,he,hq.wTag] at hc
      cases hc
    change indexAfter q.ledger e q.j q.w q.index+jCharge q e=q.index+wCharge q e
    simp only [indexAfter,jCharge,wCharge,hj,hw,if_true,if_false]
    omega
  · change indexAfter q.ledger e q.j q.w q.index+jCharge q e=q.index+wCharge q e
    by_cases hw : moves q.ledger e q.w <;> simp [indexAfter,jCharge,wCharge,hj,hw]

/-- On the retained word the initial spacing plus the W payments bounds
the J payments. This telescopes the exact moving spacer before using
any probability estimate. -/
theorem payments {p c n : Nat} (hn : 4≤n) (g : List (Fin n))
    (a b k : Fin n) (ha : a∈g) (hb : b∈g) (hk : k∈g) (hab : a≠b)
    (x : Config p c n) (q : Cursor p c n) (w : List (Fin n))
    (hw : RetainedKeep g q w) (hv : Valid q.ledger x)
    (hq : Geometry q.ledger q.j q.w q.k a b k q.index q.width) :
    totalJ q w ≤ q.index+totalW q w := by
  induction hw with
  | nil => simp [totalJ,totalW]
  | @cons q e t hkeep _ _ ih =>
    have hx := one_step hn g q e a b k hq hv.covers ha hab hkeep
    have hgeom := geom_step hn q.ledger g e q.j q.w q.k a b k q.index q.width hq
      hv.markCover hv.covers ha hb hk hkeep
    have H := ih (valid_step hn q.ledger x e hv) hgeom
    simp only [totalJ,totalW]
    omega

/-- Paper §3: if the initial consecutive W and K gaps are b0 and c0,
fewer than 2b0+c0+1 J payments occur on every retained list. -/
theorem four_head_payments {p c n : Nat} {x : Config p c n} (hp : 2≤p) (hc : 12≤c)
    (hn : 4≤n) (g : List (Fin n)) (a b k : Fin n)
    (ha : a∈g) (hb : b∈g) (hk : k∈g) (hab : a≠b)
    (q : Cursor p c n) (w : List (Fin n)) (hw : RetainedKeep g q w)
    (hv : Valid q.ledger x) (hq : QuietEntrance q.ledger.config)
    (hg : Geometry q.ledger q.j q.w q.k a b k q.index q.width)
    (hJ : (q.ledger.config (rightNeighbor q.j)).leader=false)
    (b0 c0 : Nat) (hi : q.index+1=b0) (hwidth : q.width+1=b0+c0) :
    totalJ q w<2*b0+c0+1 := by
  have H := payments hn g a b k ha hb hk hab x q w hw hv hg
  have R := retained_progress_cap hp hc hn g a b k ha hb hk q w hw hv hq hg hJ
  omega

#print axioms one_step
#print axioms payments
#print axioms four_head_payments
end L4.WindowFourHeadCap
