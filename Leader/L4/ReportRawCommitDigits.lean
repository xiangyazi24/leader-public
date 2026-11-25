import Leader.L4.ReportRawCommitSnapshot

namespace L4.ReportRawCommitDigits
open AllSizeProtocol PhysicalCustody ReportByteRows ReportRawProjection ReportRawCommitSnapshot
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

private theorem digit_work_congr (p : Params) (a b : BitVec p.w) (ix : Nat)
    (H : ∀ i, i<workW p → a.getLsbD i=b.getLsbD i) :
    reportDigitPair p a ix=reportDigitPair p b ix := by
  let k := sealBase p+5+(1-ix)*bankW p
  change a.extractLsb' k (2*d p)=b.extractLsb' k (2*d p)
  apply BitVec.eq_of_getLsbD_eq
  intro j J
  simp only [BitVec.getLsbD_extractLsb',J,decide_true,Bool.true_and]
  apply H
  have L : 1-ix≤1 := by omega
  have M := Nat.mul_le_mul_right (bankW p) L
  simp only [Nat.one_mul] at M
  unfold k workW grantBase bankW at *
  omega

theorem join_commit_keeps_digits (p : Params) (hu : Bool) (u v : BitVec p.w)
    (dsc ix : Nat) (G : CommitGuard p hu u v dsc) :
    reportDigitPair p (join p (hu,true) (u,v)).2 ix=reportDigitPair p v ix := by
  exact (digit_work_congr p _ _ ix (join_right_work p (hu,true) u v)).trans
    (commit_keeps_digit_pair p hu u v dsc ix G)

theorem report1_commit_keeps_digits {s n : Nat} (x : Raw s n) (e : Fin n)
    (S : e≠rightNeighbor e) (head : (oldHeaders (rows s) (x (rightNeighbor e))).h4=true)
    (dsc ix : Nat)
    (G : CommitGuard (firstParams s) (oldHeaders (rows s) (x e)).h4
      (x e).report1 (x (rightNeighbor e)).report1 dsc) :
    reportDigitPair (firstParams s) (rawNext s x e (rightNeighbor e)).report1 ix=
      reportDigitPair (firstParams s) (x (rightNeighbor e)).report1 ix := by
  have P := congrArg _root_.Prod.snd (raw_report1_pair x e S)
  simp only [head] at P
  exact (congrArg (fun r => reportDigitPair (firstParams s) r ix) P).trans
    (join_commit_keeps_digits (firstParams s) _ (x e).report1 (x (rightNeighbor e)).report1 dsc ix G)

theorem report2_commit_keeps_digits {s n : Nat} (x : Raw s n) (e : Fin n)
    (S : e≠rightNeighbor e) (head : (oldHeaders (rows s) (x (rightNeighbor e))).h5=true)
    (dsc ix : Nat)
    (G : CommitGuard (secondParams s) (oldHeaders (rows s) (x e)).h5
      (x e).report2 (x (rightNeighbor e)).report2 dsc) :
    reportDigitPair (secondParams s) (rawNext s x e (rightNeighbor e)).report2 ix=
      reportDigitPair (secondParams s) (x (rightNeighbor e)).report2 ix := by
  have P := congrArg _root_.Prod.snd (raw_report2_pair x e S)
  simp only [head] at P
  exact (congrArg (fun r => reportDigitPair (secondParams s) r ix) P).trans
    (join_commit_keeps_digits (secondParams s) _ (x e).report2 (x (rightNeighbor e)).report2 dsc ix G)

#print axioms join_commit_keeps_digits
#print axioms report1_commit_keeps_digits
#print axioms report2_commit_keeps_digits
end L4.ReportRawCommitDigits
