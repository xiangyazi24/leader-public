import Leader.L4.PhysicalCustody
import Leader.L4.ReportPulseDecode
import Leader.L4.ReportPulseWait

namespace L4.ReportPulseRaw
open AllSizeProtocol PhysicalCustody ReportByteRows

abbrev P1 (s : Nat) : Params := ⟨s+1,1,s,streak s⟩
abbrev P2 (s : Nat) : Params := ⟨2,ell (radiusTwo s+1),radiusTwo s,streak (radiusTwo s)⟩

private theorem geo_outside (p : Params) (i : Nat) (I : i<tail p) :
    ¬ (ShortGeo.report p.beta p.digits p.streak).owned i := by
  intro H
  have E := H.1
  change p.w-ell (max 3 p.digits+1)-1≤i at E
  rw [layout_size] at E
  unfold workW grantBase bankW sealBase sourceW sourceBase at E
  omega

private theorem local_join (p : Params) (h : Pair Bool) (u v : BitVec p.w) (i : Nat)
    (I : i<tail p) :
    let G := ShortGeo.report p.beta p.digits p.streak
    let y := patchPair (G.patches (max 3 p.digits) h (u,v) (BStarShort.reportWork p h (u,v))) (u,v)
    (y.1.getLsbD i=(pulseApply p h.1 2 u).getLsbD i) ∧
    (y.2.getLsbD i=(pulseApply p h.2 1 v).getLsbD i) := by
  dsimp only
  have P := ShortGeo.work_agrees_outside (ShortGeo.report p.beta p.digits p.streak)
    (max 3 p.digits) h (u,v) (BStarShort.reportWork p h (u,v)) i (geo_outside p i I)
  have G : i<grantBase p := by
    unfold grantBase sealBase sourceBase
    omega
  exact ⟨P.1.trans ((BStarShort.report_apply_outside p h (u,v) i (.inl G)).trans
      (row_left_pulse_bits p h.1 h.2 u v i I)),
    P.2.trans (row_right_pulse_bits p h.1 h.2 u v i I)⟩

private theorem paired1 {s n : Nat} (x : Raw s n) (e : Fin n) (i : Nat)
    (I : i<tail (P1 s)) :
    let r := rightNeighbor e
    let y := largePair (rows s) (x e,x r)
    (y.1.report1.getLsbD i=(pulseApply (P1 s)
       (oldHeaders (rows s) (x e)).h4 2 (x e).report1).getLsbD i) ∧
    (y.2.report1.getLsbD i=(pulseApply (P1 s)
       (oldHeaders (rows s) (x r)).h4 1 (x r).report1).getLsbD i) :=
  local_join (P1 s) ((oldHeaders (rows s) (x e)).h4,(oldHeaders (rows s) (x (rightNeighbor e))).h4)
    (x e).report1 (x (rightNeighbor e)).report1 i I

private theorem paired2 {s n : Nat} (x : Raw s n) (e : Fin n) (i : Nat)
    (I : i<tail (P2 s)) :
    let r := rightNeighbor e
    let y := largePair (rows s) (x e,x r)
    (y.1.report2.getLsbD i=(pulseApply (P2 s)
       (oldHeaders (rows s) (x e)).h5 2 (x e).report2).getLsbD i) ∧
    (y.2.report2.getLsbD i=(pulseApply (P2 s)
       (oldHeaders (rows s) (x r)).h5 1 (x r).report2).getLsbD i) :=
  local_join (P2 s) ((oldHeaders (rows s) (x e)).h5,(oldHeaders (rows s) (x (rightNeighbor e))).h5)
    (x e).report2 (x (rightNeighbor e)).report2 i I

/-- Actual report1 low work and paint projection, using the original physical mark. -/
theorem report1_pulse_raw {s n : Nat} (x : Raw s n) (e v : Fin n) (i : Nat)
    (I : i<tail (P1 s)) :
    ((rawNext s x e v).report1).getLsbD i =
      if v=e then (pulseApply (P1 s) (oldHeaders (rows s) (x v)).h4 2 (x v).report1).getLsbD i
      else if v=rightNeighbor e then (pulseApply (P1 s) (oldHeaders (rows s) (x v)).h4 1 (x v).report1).getLsbD i
      else (x v).report1.getLsbD i := by
  unfold rawNext AllSizeS1Geometry.step
  split
  · rename_i E
    subst v
    exact (paired1 x e i I).1
  · split
    · rename_i E
      subst v
      exact (paired1 x e i I).2
    · rfl

/-- Actual report2 low work and paint projection, using the original physical mark. -/
theorem report2_pulse_raw {s n : Nat} (x : Raw s n) (e v : Fin n) (i : Nat)
    (I : i<tail (P2 s)) :
    ((rawNext s x e v).report2).getLsbD i =
      if v=e then (pulseApply (P2 s) (oldHeaders (rows s) (x v)).h5 2 (x v).report2).getLsbD i
      else if v=rightNeighbor e then (pulseApply (P2 s) (oldHeaders (rows s) (x v)).h5 1 (x v).report2).getLsbD i
      else (x v).report2.getLsbD i := by
  unfold rawNext AllSizeS1Geometry.step
  split
  · rename_i E
    subst v
    exact (paired2 x e i I).1
  · split
    · rename_i E
      subst v
      exact (paired2 x e i I).2
    · rfl

/-- A frozen selected lower header seen by a literal report wire on every raw mark. -/
structure Wire {X : Type} {n : Nat} (raw : X → Fin n → X) (b : Fin n)
    (Q : X → Prop) (p : Params) (bytes : X → BitVec p.w) : Prop where
  stays : ∀ x e, Q x → Q (raw x e)
  bits : ∀ x e i, Q x → i<tail p →
    (bytes (raw x e)).getLsbD i =
      if b=e then (pulseApply p true 2 (bytes x)).getLsbD i
      else if b=rightNeighbor e then (pulseApply p true 1 (bytes x)).getLsbD i
      else (bytes x).getLsbD i

private theorem incoming_unique {n : Nat} (a e b : Fin n) (A : rightNeighbor a=b) :
    b=rightNeighbor e ↔ e=a := by
  constructor
  · intro E
    apply Fin.ext
    have He := e.isLt
    have Ha := a.isLt
    have F := congrArg Fin.val (A.trans E)
    change (a.val+1)%n=(e.val+1)%n at F
    by_cases U : a.val+1<n
    · rw [Nat.mod_eq_of_lt U] at F
      by_cases V : e.val+1<n
      · rw [Nat.mod_eq_of_lt V] at F
        omega
      · rw [show e.val+1=n by omega,Nat.mod_self] at F
        omega
    · rw [show a.val+1=n by omega,Nat.mod_self] at F
      by_cases V : e.val+1<n
      · rw [Nat.mod_eq_of_lt V] at F
        omega
      · omega
  · rintro rfl
    exact A.symm

/-- Count a pulse completion on the actual OLD report snapshot.
A completion can count even when its paint has the same old Z. -/
def countedPaint {X : Type} {n : Nat} (b : Fin n) (p : Params)
    (bytes : X→BitVec p.w) (x : X) (e : Fin n) : Bool :=
  if b=rightNeighbor e then paints p true 1 (bytes x) else false

private theorem no_outgoing_paint (p : Params) (x : BitVec p.w) :
    paints p true 2 x=false := by
  unfold paints
  dsimp only
  generalize (if ((x.extractLsb' (ell p.streak) 2).toNat==3) then 0
      else (x.extractLsb' (ell p.streak) 2).toNat)=r
  split <;> (first | rfl | split <;> simp_all)

open ReportPulseWait

theorem wire_mean {X : Type} {n : Nat} {raw : X → Fin n → X} {b : Fin n}
    {Q : X → Prop} {p : Params} {bytes : X → BitVec p.w}
    (F : Wire raw b Q p bytes) (a : Fin n) (A : rightNeighbor a=b) (D : a≠b)
    (P : 0<p.streak) (x : X) (G : Q x) :
    IIDExpectedHittingTimeAtMost (monitor raw (countedPaint b p bytes)) (fun y=>y.2=true)
      (x,false) (4*n*2^p.streak) := by
  apply original_tape_mean P a b D raw (countedPaint b p bytes) Q F.stays
    (fun y=>ReportPulseDecode.phase p (bytes y)) (fun y=>ReportPulseDecode.count p (bytes y)) _ x G
  intro y e h hy
  change ReportPulseDecode.state p (bytes (raw y e)) (h || countedPaint b p bytes y e) =
    ReportPulseWait.step p.streak a b e (ReportPulseDecode.state p (bytes y) h)
  have E := incoming_unique a e b A
  by_cases H : e=a
  · have K : b≠e := by exact fun L=>D (H.symm.trans L.symm)
    have J := E.mpr H
    rw [ReportPulseWait.step,if_pos H]
    have T := ReportPulseDecode.state_congr p (bytes (raw y e)) (pulseApply p true 1 (bytes y))
      (h || countedPaint b p bytes y e) (fun i I=>by simpa only [if_neg K,if_pos J] using F.bits y e i hy I)
    rw [T,countedPaint,if_pos J]
    exact ReportPulseDecode.clock_eq p P (bytes y) false h
  · have J : b≠rightNeighbor e := fun I=>H (E.mp I)
    by_cases K : e=b
    · rw [ReportPulseWait.step,if_neg H,if_pos K]
      have T := ReportPulseDecode.state_congr p (bytes (raw y e)) (pulseApply p true 2 (bytes y))
        (h || countedPaint b p bytes y e)
        (fun i I=>by simpa only [if_pos K.symm] using F.bits y e i hy I)
      rw [T,countedPaint,if_neg J,←no_outgoing_paint p (bytes y)]
      exact ReportPulseDecode.clock_eq p P (bytes y) true h
    · rw [ReportPulseWait.step,if_neg H,if_neg K]
      have T := ReportPulseDecode.state_congr p (bytes (raw y e)) (bytes y)
        (h || countedPaint b p bytes y e)
        (fun i I=>by simpa only [if_neg (Ne.symm K),if_neg J] using F.bits y e i hy I)
      rw [T,countedPaint,if_neg J,Bool.or_false]

theorem report1_mean {s n : Nat} (a b : Fin n) (A : rightNeighbor a=b) (D : a≠b)
    (Q : Raw s n → Prop) (stay : ∀ x e, Q x → Q (rawNext s x e))
    (frozen : ∀ x, Q x → (oldHeaders (rows s) (x b)).h4=true)
    (x : Raw s n) (G : Q x) :
    IIDExpectedHittingTimeAtMost (monitor (rawNext s) (countedPaint b (P1 s) (fun x=>(x b).report1)))
      (fun y=>y.2=true) (x,false) (4*n*2^streak s) := by
  apply wire_mean (p:=P1 s) (b:=b) (Q:=Q) _ a A D _ x G
  · refine ⟨stay,?_⟩
    intro y e i hy I
    have E := report1_pulse_raw y e b i I
    rw [frozen y hy] at E
    exact E
  · change 0<streak s
    unfold streak
    exact Nat.lt_of_lt_of_le (show 0 < 45 from by decide)
      (Nat.le_trans (Nat.le_add_left 45 _) (Nat.le_add_right _ _))

theorem report2_mean {s n : Nat} (a b : Fin n) (A : rightNeighbor a=b) (D : a≠b)
    (Q : Raw s n → Prop) (stay : ∀ x e, Q x → Q (rawNext s x e))
    (frozen : ∀ x, Q x → (oldHeaders (rows s) (x b)).h5=true)
    (x : Raw s n) (G : Q x) :
    IIDExpectedHittingTimeAtMost (monitor (rawNext s) (countedPaint b (P2 s) (fun x=>(x b).report2)))
      (fun y=>y.2=true) (x,false) (4*n*2^streak (radiusTwo s)) := by
  apply wire_mean (p:=P2 s) (b:=b) (Q:=Q) _ a A D _ x G
  · refine ⟨stay,?_⟩
    intro y e i hy I
    have E := report2_pulse_raw y e b i I
    rw [frozen y hy] at E
    exact E
  · change 0<streak (radiusTwo s)
    unfold streak
    exact Nat.lt_of_lt_of_le (show 0 < 45 from by decide)
      (Nat.le_trans (Nat.le_add_left 45 _) (Nat.le_add_right _ _))

#print axioms report1_pulse_raw
#print axioms report2_pulse_raw
#print axioms report1_mean
#print axioms report2_mean
end L4.ReportPulseRaw
