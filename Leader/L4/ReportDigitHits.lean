import Leader.L4.ReportChartPartition
import Leader.L4.ReportRawProjection
import Leader.L4.AdviceBandRadiusBudget
import Leader.L4.ReportCacheAllSites

namespace L4.ReportDigitHits
open AllSizeProtocol BStarH6Ordinal WidthOrdinalSpan ShortLayerGeometry ShortResetChart
open ShortResetCycle ReportChartPartition
open PhysicalCustody ReportByteRows ReportRawProjection

/-- Offset tested by the literal report row (clipping at the exact joined
geometry cap, and forcing lower-header offset zero). -/
def effectiveOffset (p : Params) (h : Bool) (x : BitVec p.w) : Nat :=
  if h then 0 else min (max 3 p.digits)
    ((x.extractLsb' (workW p+1) (ell (max 3 p.digits+1))).toNat)

theorem effectiveOffset_eq (p : Params) (h : Bool) (x : BitVec p.w) :
    effectiveOffset p h x =
      if h then 0 else min (max 3 p.digits)
        (((ShortGeo.report p.beta p.digits p.streak).off.read x).toNat) := by
  have W := layout_size p
  change reportWidth p.beta p.digits p.streak=workW p+1+ell (max 3 p.digits+1) at W
  unfold effectiveOffset
  have E : reportWidth p.beta p.digits p.streak - ell (max 3 p.digits+1)=workW p+1 := by omega
  change (if h then 0 else min _ ((x.extractLsb' (workW p+1) _).toNat))=
    (if h then 0 else min _ ((x.extractLsb' (reportWidth p.beta p.digits p.streak -
      ell (max 3 p.digits+1)) _).toNat))
  rw [E]

theorem reportK_eq (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) :
    BStarShort.reportK p h x j =
      decode p (j.val==1 && effectiveOffset p h x==2) (resetTokenRead p x j) := rfl

/-- Correct cache data evaluated in the *old* raw sheet at an arbitrary
actual sampled mark, not substituted for a post-mark decoded wire. -/
def CacheCorrect {n : Nat} (p : Params) (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (bytes : Fin n→BitVec p.w) : Prop :=
  ∀ i, (((ShortGeo.report p.beta p.digits p.streak).off.read (bytes i)).toNat) =
    min (max 3 p.digits) (ordinal h hh i)

theorem offset_from_cache {n : Nat} (p : Params) (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (bytes : Fin n→BitVec p.w) (C : CacheCorrect p h hh bytes) (i : Fin n) :
    effectiveOffset p (h i) (bytes i)=min (max 3 p.digits) (ordinal h hh i) := by
  rw [effectiveOffset_eq,C i]
  by_cases H : h i=true
  · rw [if_pos H,(ordinal_zero h hh i).mpr H,Nat.min_zero]
  · rw [if_neg H,←Nat.min_assoc,Nat.min_self]

/-- The literal report link schedule has the same port destinations as
the common three-lane chart. -/
theorem destination_agrees (h : Bool) (j : Fin 3) :
    reset0Destination h j=ShortResetRow.destination h j := by
  revert j h
  decide

theorem literal_route_step {n : Nat} {h : Fin n→Bool} (C : Chart h) (k : Nat) (K : k<C.L) :
    reset0Destination (h (rightNeighbor (nextAt C.root k))) (C.route.port k)=
      if k+1<C.L then some (C.route.port (k+1)) else none := by
  rw [destination_agrees]
  exact C.dst k K

def markAt {n : Nat} {h : Fin n→Bool} (C : Chart h) (k : Fin C.L) : Fin n :=
  nextAt C.root k.val

theorem markAt_injective {n : Nat} {h : Fin n→Bool} (C : Chart h)
    {i j : Fin C.L} (E : markAt C i=markAt C j) : i=j :=
  Fin.ext (C.route.injectiveOn _ _ i.isLt j.isLt E)

/-- Under the old cache equality, exactly one departure index tests
each literal (lane,digit) pair in the entire three-word physical tour. -/
theorem unique_live_digit {n : Nat} (p : Params) {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (bytes : Fin n→BitVec p.w) (cache : CacheCorrect p h hh bytes)
    {r : Fin n} {a b c : Nat} (R : h r=true)
    (F : Gap h r a) (G : Gap h (nextAt r a) b) (I : Gap h (nextAt (nextAt r a) b) c)
    (room : a+b+c<n) (laneId : Fin 3) (digit : Nat)
    (D : digit<p.digits) (L : p.digits≤wordSize a b c laneId) :
    let C := chart_of_three R F G I room
    let k := wordStart a b laneId+digit
    k<C.L ∧ ∀ q : Fin C.L,
      ((C.route.port q.val=laneId ∧
        effectiveOffset p (h (markAt C q)) (bytes (markAt C q))=digit) ↔ q.val=k) := by
  have X := chart_unique_digit hh R F G I room laneId digit
    (show digit<max 3 p.digits from Nat.lt_of_lt_of_le D (Nat.le_max_right _ _))
    (Nat.lt_of_lt_of_le D L)
  refine ⟨X.1,fun q=>?_⟩
  rw [offset_from_cache p h hh bytes cache]
  exact X.2 q.val q.isLt

/-- Distinct physical marks, in forward route order, implement the
left reader, center writer, and right reader tests for the same digit. -/
theorem ordered_three_hits {n : Nat} (p : Params) {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (bytes : Fin n→BitVec p.w) (cache : CacheCorrect p h hh bytes)
    {r : Fin n} {a b c : Nat} (R : h r=true)
    (F : Gap h r a) (G : Gap h (nextAt r a) b) (I : Gap h (nextAt (nextAt r a) b) c)
    (room : a+b+c<n) (d : Nat) (D : d<p.digits)
    (A : p.digits≤a) (B : p.digits≤b) (C : p.digits≤c) :
    let chart := chart_of_three R F G I room
    ∃ q₀ q₁ q₂ : Fin chart.L, q₀.val<q₁.val ∧ q₁.val<q₂.val ∧
      (∀ q : Fin chart.L,
        (effectiveOffset p (h (markAt chart q)) (bytes (markAt chart q))=d) ↔
          q=q₀ ∨ q=q₁ ∨ q=q₂) ∧
      chart.route.port q₀.val=0 ∧ chart.route.port q₁.val=1 ∧ chart.route.port q₂.val=2 := by
  let chart := chart_of_three R F G I room
  have H0 := unique_live_digit p hh bytes cache R F G I room 0 d D A
  have H1 := unique_live_digit p hh bytes cache R F G I room 1 d D B
  have H2 := unique_live_digit p hh bytes cache R F G I room 2 d D C
  let q₀ : Fin chart.L := ⟨wordStart a b 0+d,H0.1⟩
  let q₁ : Fin chart.L := ⟨wordStart a b 1+d,H1.1⟩
  let q₂ : Fin chart.L := ⟨wordStart a b 2+d,H2.1⟩
  have T0 := (H0.2 q₀).mpr rfl
  have T1 := (H1.2 q₁).mpr rfl
  have T2 := (H2.2 q₂).mpr rfl
  have pa := F.positive
  have pb := G.positive
  refine ⟨q₀,q₁,q₂,by simp [q₀,q₁,wordStart]; omega,by simp [q₁,q₂,wordStart]; omega,?_,T0.1,T1.1,T2.1⟩
  intro q
  constructor
  · intro E
    let j := chart.route.port q.val
    have J := j.isLt
    rcases (show j.val=0 ∨ j.val=1 ∨ j.val=2 by omega) with J|J|J
    · exact .inl (Fin.ext ((H0.2 q).mp ⟨Fin.ext J,E⟩))
    · exact .inr (.inl (Fin.ext ((H1.2 q).mp ⟨Fin.ext J,E⟩)))
    · exact .inr (.inr (Fin.ext ((H2.2 q).mp ⟨Fin.ext J,E⟩)))
  · rintro (rfl|rfl|rfl)
    · exact T0.2
    · exact T1.2
    · exact T2.2

#print axioms effectiveOffset_eq
#print axioms reportK_eq
#print axioms literal_route_step
#print axioms unique_live_digit
#print axioms ordered_three_hits

/-- Throughout an arbitrary actual flight each sampled departure may
have different old production bytes. The unique-hit calculation needs
the cache invariant at each old pair, not constancy of work data. -/
theorem ordered_hits_varying_old {n : Nat} (p : Params) {h : Fin n→Bool} (hh : ∃ i,h i=true)
    {r : Fin n} {a b c : Nat} (R : h r=true)
    (F : Gap h r a) (G : Gap h (nextAt r a) b) (I : Gap h (nextAt (nextAt r a) b) c)
    (room : a+b+c<n) (d : Nat) (D : d<p.digits)
    (A : p.digits≤a) (B : p.digits≤b) (C : p.digits≤c)
    (snapshots : Fin (chart_of_three R F G I room).L→Fin n→BitVec p.w)
    (HC : ∀ q, CacheCorrect p h hh (snapshots q)) :
    let chart := chart_of_three R F G I room
    ∃ q₀ q₁ q₂ : Fin chart.L, q₀.val<q₁.val ∧ q₁.val<q₂.val ∧
      (∀ q : Fin chart.L,
        (effectiveOffset p (h (markAt chart q)) (snapshots q (markAt chart q))=d) ↔
          q=q₀ ∨ q=q₁ ∨ q=q₂) ∧
      chart.route.port q₀.val=0 ∧ chart.route.port q₁.val=1 ∧ chart.route.port q₂.val=2 := by
  let chart := chart_of_three R F G I room
  let seed : Fin chart.L := ⟨0,chart.positive⟩
  obtain ⟨q₀,q₁,q₂,L₀,L₁,S,T₀,T₁,T₂⟩ :=
    ordered_three_hits p hh (snapshots seed) (HC seed) R F G I room d D A B C
  refine ⟨q₀,q₁,q₂,L₀,L₁,?_,T₀,T₁,T₂⟩
  intro q
  rw [offset_from_cache p h hh (snapshots q) (HC q)]
  have H := S q
  rw [offset_from_cache p h hh (snapshots seed) (HC seed)] at H
  exact H

theorem report1_cache_is_literal {s n : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    {Q : Raw s n→Prop} (x : Raw s n)
    (A : ReportCacheAllSites.Report1Correct h hh Q x) :
    CacheCorrect (firstParams s) h hh (fun i=>(x i).report1) :=
  fun i=>(ReportCacheAllSites.raw_fields_correct hh (by decide : 0<3) x A i).1

theorem report2_cache_is_literal {s n : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    {Q : Raw s n→Prop} (x : Raw s n)
    (A : ReportCacheAllSites.Report2Correct h hh Q x) :
    CacheCorrect (secondParams s) h hh (fun i=>(x i).report2) :=
  fun i=>(ReportCacheAllSites.raw_fields_correct hh
    (by omega : 0<max 3 (ell (radiusTwo s+1))) x A i).1

theorem report1_digit_room (s gap : Nat) (G : 16≤gap) : (firstParams s).digits≤gap := by
  change 1≤gap
  omega

theorem report2_digit_room {s gap : Nat} (S : 6≤s) (G : 16*(s+1)≤gap) :
    (secondParams s).digits≤gap := by
  have D := AdviceBandRadiusBudget.t2_le S
  change ell (radiusTwo s+1)≤gap
  omega

#print axioms ordered_hits_varying_old
#print axioms report1_cache_is_literal
#print axioms report2_cache_is_literal
#print axioms report2_digit_room
end L4.ReportDigitHits
