import Leader.L4.PhysicalCustody
import Leader.L4.ReportByteRows

namespace L4.ReportRawProjection
open AllSizeProtocol PhysicalCustody ReportByteRows

def firstParams (s : Nat) : Params := ⟨s+1,1,s,streak s⟩
def secondParams (s : Nat) : Params := ⟨2,ell (radiusTwo s+1),radiusTwo s,streak (radiusTwo s)⟩

/-- Exact production report work includes the initiator grant
filter. Replacing reportWork by row before the geometry join would
silently alter some grant masks. -/
def join (p : Params) (h : Pair Bool) (x : Pair (BitVec p.w)) : Pair (BitVec p.w) :=
  let G := ShortGeo.report p.beta p.digits p.streak
  patchPair (G.patches (max 3 p.digits) h x (BStarShort.reportWork p h x)) x

/-- The owned high geometry and initiator grant filter cannot alter any
token/control bit at either side. The responder uses the literal row
unchanged at all low work fields. -/
theorem join_work_bits (p : Params) (h : Pair Bool) (x : Pair (BitVec p.w))
    (i : Nat) (L : i<grantBase p) :
    let y := join p h x
    let q := patchPair (row p h x) x
    y.1.getLsbD i=q.1.getLsbD i ∧ y.2.getLsbD i=q.2.getLsbD i := by
  let G := ShortGeo.report p.beta p.digits p.streak
  have F : ¬G.owned i := by
    intro H
    have K := H.1
    change reportWidth p.beta p.digits p.streak-ell (max 3 p.digits+1)-1≤i at K
    have Hwidth := layout_size p
    change reportWidth p.beta p.digits p.streak=workW p+1+ell (max 3 p.digits+1) at Hwidth
    rw [Hwidth] at K
    unfold workW at K
    omega
  have H := G.work_agrees_outside (max 3 p.digits) h x (BStarShort.reportWork p h x) i F
  exact ⟨H.1.trans (BStarShort.report_apply_outside p h x i (.inl L)),
    H.2.trans (by rfl)⟩

abbrev Prod (s : Nat) := BStarTrace.production s (radiusTwo s) (ell (radiusTwo s+1))
  (streak s) (streak (radiusTwo s)) (radWidth s) (s+11) 2 12

/-- Exact full report1 pair of the joined production protocol, including
high cache publishers and grant arbitration. -/
theorem pair_report1 (s : Nat) (u v : LargeSite (Prod s)) :
    let h := ((oldHeaders (rows s) u).h4,(oldHeaders (rows s) v).h4)
    let y := largePair (rows s) (u,v)
    (y.1.report1,y.2.report1) =
      join (firstParams s) h (u.report1,v.report1) := rfl

theorem pair_report2 (s : Nat) (u v : LargeSite (Prod s)) :
    let h := ((oldHeaders (rows s) u).h5,(oldHeaders (rows s) v).h5)
    let y := largePair (rows s) (u,v)
    (y.1.report2,y.2.report2) =
      join (secondParams s) h (u.report2,v.report2) := rfl

/-- Literal original-mark projection. Excluding self-pairs is necessary
to read both endpoints of the joined pair from the two raw sites. -/
theorem raw_report1_pair {s n : Nat} (x : Raw s n) (e : Fin n) (S : e≠rightNeighbor e) :
    let v := rightNeighbor e
    let h := ((oldHeaders (rows s) (x e)).h4,(oldHeaders (rows s) (x v)).h4)
    ((rawNext s x e e).report1,(rawNext s x e v).report1) =
      join (firstParams s) h ((x e).report1,(x v).report1) := by
  change ((AllSizeS1Geometry.step (rows s) x e e).report1,
      (AllSizeS1Geometry.step (rows s) x e (rightNeighbor e)).report1)=_
  simp only [AllSizeS1Geometry.step,if_true,if_neg (Ne.symm S)]
  exact pair_report1 s _ _

theorem raw_report2_pair {s n : Nat} (x : Raw s n) (e : Fin n) (S : e≠rightNeighbor e) :
    let v := rightNeighbor e
    let h := ((oldHeaders (rows s) (x e)).h5,(oldHeaders (rows s) (x v)).h5)
    ((rawNext s x e e).report2,(rawNext s x e v).report2) =
      join (secondParams s) h ((x e).report2,(x v).report2) := by
  change ((AllSizeS1Geometry.step (rows s) x e e).report2,
      (AllSizeS1Geometry.step (rows s) x e (rightNeighbor e)).report2)=_
  simp only [AllSizeS1Geometry.step,if_true,if_neg (Ne.symm S)]
  exact pair_report2 s _ _

theorem raw_spectator {s n : Nat} (x : Raw s n) (e i : Fin n)
    (E : i≠e) (R : i≠rightNeighbor e) : rawNext s x e i=x i := by
  change AllSizeS1Geometry.step (rows s) x e i=x i
  simp [AllSizeS1Geometry.step,E,R]

#print axioms join_work_bits
#print axioms raw_report1_pair
#print axioms raw_report2_pair
#print axioms raw_spectator

/-- Work observables measured as raw wire and PC. Decoding K1 ADMIT
after the mark still needs the actual post-mark geometry gate; a
wire equality alone must not silently replace its offset read. -/
def controlWork (p : Params) (x : BitVec p.w) : Nat × Nat :=
  (sourcePhase p x,sourceOpcode p x)

private theorem low_extract {w cap : Nat} {x y : BitVec w}
    (o d : Nat) (B : o+d≤cap)
    (H : ∀ i, i<cap → x.getLsbD i=y.getLsbD i) :
    x.extractLsb' o d=y.extractLsb' o d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  exact H _ (by omega)

private theorem token_low (p : Params) (j : Fin 3) :
    tail p+(2-j.val)*tokenW p+tokenW p≤grantBase p := by
  have M := Nat.mul_le_mul_right (tokenW p) (show 2-j.val≤2 by omega)
  unfold grantBase sealBase sourceBase
  omega

private theorem token_of_work (p : Params) (u v : BitVec p.w) (j : Fin 3)
    (H : ∀ i, i<grantBase p → u.getLsbD i=v.getLsbD i) :
    resetTokenRead p u j=resetTokenRead p v j := by
  exact low_extract _ _ (token_low p j) H

private theorem control_of_work (p : Params) (u v : BitVec p.w)
    (H : ∀ i, i<grantBase p → u.getLsbD i=v.getLsbD i) :
    controlWork p u=controlWork p v := by
  let pc := sourceBase p+19+2*d p
  have L : pc+o p+2≤grantBase p := by
    unfold pc grantBase sealBase sourceW
    omega
  have F : (u.extractLsb' (pc+o p) 2).toNat=(v.extractLsb' (pc+o p) 2).toNat :=
    congrArg BitVec.toNat (low_extract _ _ L H)
  have O : (u.extractLsb' pc (o p)).toNat=(v.extractLsb' pc (o p)).toNat :=
    congrArg BitVec.toNat (low_extract _ _ (by omega : pc+o p≤grantBase p) H)
  exact _root_.Prod.ext F O

def tokenControl (p : Params) (x : BitVec p.w) :
    (Fin 3 → BitVec (tokenW p)) × (Nat × Nat) :=
  (resetTokenRead p x,controlWork p x)

theorem join_token_control (p : Params) (h : Pair Bool) (x : Pair (BitVec p.w)) :
    Pair.map (tokenControl p) (join p h x) =
      Pair.map (tokenControl p) (patchPair (row p h x) x) := by
  apply _root_.Prod.ext
  · apply _root_.Prod.ext
    · funext j
      exact token_of_work p _ _ j (fun i L=>(join_work_bits p h x i L).1)
    · exact control_of_work p _ _ (fun i L=>(join_work_bits p h x i L).1)
  · apply _root_.Prod.ext
    · funext j
      exact token_of_work p _ _ j (fun i L=>(join_work_bits p h x i L).2)
    · exact control_of_work p _ _ (fun i L=>(join_work_bits p h x i L).2)

theorem raw_report1_token_control {s n : Nat} (x : Raw s n) (e : Fin n)
    (S : e≠rightNeighbor e) :
    let p := firstParams s
    let v := rightNeighbor e
    let h := ((oldHeaders (rows s) (x e)).h4,(oldHeaders (rows s) (x v)).h4)
    let xpair := ((x e).report1,(x v).report1)
    Pair.map (tokenControl p) ((rawNext s x e e).report1,(rawNext s x e v).report1) =
      Pair.map (tokenControl p) (patchPair (row p h xpair) xpair) := by
  exact (congrArg (Pair.map (tokenControl (firstParams s))) (raw_report1_pair x e S)).trans
    (join_token_control _ _ _)

theorem raw_report2_token_control {s n : Nat} (x : Raw s n) (e : Fin n)
    (S : e≠rightNeighbor e) :
    let p := secondParams s
    let v := rightNeighbor e
    let h := ((oldHeaders (rows s) (x e)).h5,(oldHeaders (rows s) (x v)).h5)
    let xpair := ((x e).report2,(x v).report2)
    Pair.map (tokenControl p) ((rawNext s x e e).report2,(rawNext s x e v).report2) =
      Pair.map (tokenControl p) (patchPair (row p h xpair) xpair) := by
  exact (congrArg (Pair.map (tokenControl (secondParams s))) (raw_report2_pair x e S)).trans
    (join_token_control _ _ _)

#print axioms raw_report1_token_control
#print axioms raw_report2_token_control
end L4.ReportRawProjection
