import Leader.L4.BStarLongLanding
import Leader.L4.BStarGrantWriterHistory

namespace L4.BStarCommitRingLanding
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongEvents
open BStarLongPublication BStarLongLandingFrame BStarGrantWriterHistory BStarH6WordChart BStarLongCommand

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- The old mark admits exactly the literal selected publication at
its initiator. Its real ring output has the selected bank and
erases both authorization fields, irrespective of source lineage. -/
theorem ring_landing (x : X) (e i : Fin n)
    (P : ¬ NoPublication hp x e i) :
    i=e ∧ ∃ (b : Fin 3) (d : Descriptor) (C : CommandClaim) (q : BStarLongToken.Payload),
      let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      (longTrace g raw).publications=[⟨.left,b⟩] ∧
      (C,.advance q)∈actualOffers g raw ∧ C.source=L 1 ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (q.argument.toNat/4))=some d ∧
      q.argument.toNat%4=b.val ∧ readSel (x i).long=d.old ∧
      readPublication (step x e i).long=(BitVec.ofNat 2 b.val,0,0) ∧
      readSel (step x e i).long=b := by
  have old : ∃ s : Side, i=site e s ∧
      ∃ a∈(longTrace (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).publications,
      a.endpoint=s := by
    classical
    unfold NoPublication at P
    obtain ⟨s,N⟩ := Classical.not_forall.mp P
    have loc : i=site e s := Classical.byContradiction (fun h => N (fun eq => (h eq).elim))
    obtain ⟨a,A⟩ := Classical.not_forall.mp (fun h => N (fun _ => h))
    have M : a∈(longTrace (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).publications :=
      Classical.byContradiction (fun h => A (fun y => (h y).elim))
    exact ⟨s,loc,a,M,Classical.byContradiction (fun h => A (fun _ => h))⟩
  let pair := (x e,x (rightNeighbor e))
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  obtain ⟨s,loc,a,pub,side⟩ := old
  have left := literal_endpoint_left g raw a pub
  rw [←side,left] at loc
  change i=e at loc
  subst i
  obtain ⟨C,q,sel,endsrc,K⟩ := (literal_event_iff g raw a).mp pub
  have occ := K.1
  have contains : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨(C,.advance q),sel,rfl⟩
  have src : C.source=L 1 := by
    rw [BStarLongLiteral.center_of g C contains occ]
    rfl
  have dec := K.2.2.2.2
  obtain ⟨d,D,bank,G⟩ := dec
  rw [src] at G
  change BStarLongPublication.guard true 1 (x e).long d a.bank=true at G
  have same : readSel (x e).long=d.old := by
    simp only [BStarLongPublication.guard,typedGuard,Bool.and_eq_true,beq_iff_eq] at G
    exact G.1.1.1.2
  have length := at_most_one_literal_publication g raw
  have single : (longTrace g raw).publications=[a] := by
    generalize (longTrace g raw).publications=xs at pub length ⊢
    cases xs with
    | nil => simp at pub
    | cons h t =>
      have H : t=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at length; omega)
      subst t
      rw [List.mem_singleton] at pub
      rw [pub]
  have event : a=⟨.left,a.bank⟩ := by cases a; simp_all
  have landing := BStarLongLanding.bStar_literal_lands k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair a pub
  have fig : step x e e=(largePair B pair).1 := by simp only [AllSizeS1Geometry.step,if_true,pair]
  rw [←fig] at landing
  refine ⟨rfl,a.bank,d,C,q,?_,sel,src,D,bank,same,landing,?_⟩
  · exact single.trans (congrArg (fun t => [t]) event)
  · have S := congrArg Prod.fst landing
    unfold readSel
    change BStarLongLayout.selector.read (step x e e).long=BitVec.ofNat 2 a.bank.val at S
    rw [S,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.lt_trans a.bank.isLt (by decide))]
    simp [a.bank.isLt]

end L4.BStarCommitRingLanding
