import Leader.L4.BStarWarmupArrival
import Leader.L4.BStarWarmupRawQuarter

namespace L4.BStarWarmupEventQuarter
open BStarWarmupQuarter BStarWarmupRawQuarter BStarWarmupKeys
open BStarWarmupReceiptChoice BStarWarmupArrival BStarStaggeredArrival BStarFirstArrival
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarAcquireAnchors BStarNativeNeedLift BStarNativePortGeometry L4.Compiler.Native
open L4.Height BStarPhysicalPairLaw BStarEpochLift Classical

variable {n : Nat} {h : Fin n→Bool}
local notation "Owner" => Header h

/-- Evolve a simultaneous logical starting slice at the opening for
exactly the requested number of levels. The index is a logical level,
not a physical raw-mark deadline. -/
abbrev evolve (neighbor : Owner→Fin 3→Owner) (update : Update Owner Snapshot (Fin 3))
    (opening : Nat) (initial : Owner→Snapshot) :=
  levels neighbor update opening initial

theorem oracle_restarts {T : Nat} (R : BStarFirstArrival.Trace Owner Snapshot (Fin 3) T)
    (update : Update Owner Snapshot (Fin 3)) (opening : Nat)
    (le : ∀ i,R.level 0 i≤opening) (q : Nat) :
    fromTrace R update (opening+q) =
      evolve R.neighbor update opening (fromTrace R update opening) q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    funext i
    rw [show opening+(q+1)=opening+q+1 from rfl,
      oracle_after R update (opening+q) i (Nat.le_trans (le i) (Nat.le_add_right _ _))]
    simp only [evolve,levels,ih]

noncomputable def joinList (reserve : BStarWarmupKeys.Key n→Option Bool) (lo op hi : Nat)
    (a : Bits (jointSize reserve lo op hi)) :
    Fin (joint reserve lo op hi).length→Bool :=
  fun j=>a (j.cast (joint_length reserve lo op hi))

/-- If two fills have the same warm part, all differences before the
opening are invisible, even to owners beginning at different lifts. -/
theorem joinList_warm {reserve : BStarWarmupKeys.Key n→Option Bool} {lo op hi : Nat}
    (a b : Bits (jointSize reserve lo op hi))
    (W : warm (K:=(keys reserve op hi).length) a = warm b) :
    ∀ j,j.val<(keys reserve lo op).length →
      joinList reserve lo op hi a j=joinList reserve lo op hi b j := by
  intro j J
  let k : Fin (keys reserve lo op).length := ⟨j.val,J⟩
  exact congrFun W k

theorem joinList_agrees {reserve : BStarWarmupKeys.Key n→Option Bool} {lo op hi : Nat}
    (obs : List (Fin n)→Fin n→Option (BStarWarmupKeys.Key n×Bool)) (history w : List (Fin n))
    (a : Bits (jointSize reserve lo op hi))
    (agree : ∀ j b,firstRaw obs (sumKey reserve lo op hi j) history w=some b → a j=b) :
    ∀ j b,firstRaw obs (indexKey reserve lo op hi j) history w=some b →
      joinList reserve lo op hi a j=b := by
  intro j b E
  apply agree
  unfold sumKey
  rw [show (j.cast (joint_length reserve lo op hi)).cast (joint_length reserve lo op hi).symm=j from Fin.ext rfl]
  exact E

/-- Below the finite cap, physical first arrivals agree with the
simultaneous logical computation started from the warm-up-only slice.
The reach hypothesis is per owner at the raw deadline; no equal final
lifts and no observation of unused cube coordinates are required. -/
theorem cap_snapshot {T : Nat} (R : BStarFirstArrival.Trace Owner Snapshot (Fin 3) T)
    (r : Nat) (reserve : BStarWarmupKeys.Key n→Option Bool) (lo opening cap : Nat)
    (a : Bits (jointSize reserve lo opening cap))
    (W : FollowsBelow R cap (cubeUpdate r reserve lo opening cap (joinList reserve lo opening cap a)))
    (le : ∀ i,R.level 0 i≤opening) (OC : opening≤cap)
    (reach : ∀ i,cap≤R.level T i)
    (view : Owner→Snapshot)
    (actual : ∀ i,∃ t,FirstAt R i cap t ∧ view i=R.curr t i) :
    view=evolve R.neighbor (cubeUpdate r reserve lo opening cap (joinList reserve lo opening cap a))
      opening
      (fromTrace R (cubeUpdate r reserve lo opening cap (joinList reserve lo opening cap
        (join (warm (K:=(keys reserve opening cap).length) a) (fun _=>false)))) opening)
      (cap-opening) := by
  let A := (keys reserve lo opening).length
  let K := (keys reserve opening cap).length
  let b : Bits (A+K) := join (warm (K:=K) a) (fun _=>false)
  let update := cubeUpdate r (h:=h) reserve lo opening cap (joinList reserve lo opening cap a)
  have warmEq := opening_oracle_eq R r reserve lo opening cap
    (joinList reserve lo opening cap a) (joinList reserve lo opening cap b)
    (joinList_warm a b (by simp [b]))
  have same := oracle_restarts R update opening le (cap-opening)
  rw [Nat.add_sub_of_le OC,warmEq] at same
  funext i
  obtain ⟨t,H,E⟩ := actual i
  obtain ⟨s,F,G⟩ := snapshot_of_finish_ge R cap update W i cap
    (Nat.le_trans (le i) OC) (Nat.le_refl _) (reach i)
  have eq : t=s := by
    rcases Nat.lt_trichotomy t s with ts|eq|st
    · exact (Nat.not_lt_of_ge (by rw [H.2.1]; exact Nat.le_refl _) (F.2.2 t ts)).elim
    · exact eq
    · exact (Nat.not_lt_of_ge (by rw [F.2.1]; exact Nat.le_refl _) (H.2.2 s st)).elim
  exact E.trans ((eq.symm ▸ G).trans (congrFun same i))

/-- At or after the opening every free tracked update uses the main
part, not the warm-up part. Reserved values, if any, are independent
of either fill. -/
theorem main_update_eq (r : Nat) (reserve : BStarWarmupKeys.Key n→Option Bool)
    (lo opening cap : Nat) (a b : Bits (jointSize reserve lo opening cap))
    (M : main (A:=(keys reserve lo opening).length) a = main b)
    (level : Nat) (L : opening≤level) (i : Owner) (own : Snapshot) (port : Fin 3→Snapshot) :
    cubeUpdate r reserve lo opening cap (joinList reserve lo opening cap a) level i own port =
      cubeUpdate r reserve lo opening cap (joinList reserve lo opening cap b) level i own port := by
  unfold cubeUpdate cubeBit complete
  cases reserve (i.val,level) with
  | some c => rfl
  | none =>
    cases E : coordinate reserve lo opening cap (i.val,level) with
    | none => rfl
    | some j =>
      have le : (keys reserve lo opening).length≤j.val := by
        apply Nat.le_of_not_gt
        intro lt
        have eq := (coordinate_iff reserve lo opening cap j (i.val,level)).mp E
        have mem : (i.val,level)∈keys reserve lo opening := by
          rw [eq]
          unfold indexKey joint
          erw [List.getElem_append_left lt]
          exact List.getElem_mem _
        exact (Nat.not_lt_of_ge L) ((mem_keys _ _ _ _).mp mem).2.1
      let k : Fin (keys reserve opening cap).length :=
        ⟨j.val-(keys reserve lo opening).length,by have J:=Nat.lt_of_lt_of_eq j.isLt (joint_length reserve lo opening cap); unfold jointSize at J; omega⟩
      have idx : k.natAdd (keys reserve lo opening).length=j.cast (joint_length reserve lo opening cap) := by
        apply Fin.ext
        change (keys reserve lo opening).length+(j.val-(keys reserve lo opening).length)=j.val
        omega
      have v := congrFun M k
      change a (k.natAdd (keys reserve lo opening).length)=b (k.natAdd (keys reserve lo opening).length) at v
      rw [idx] at v
      simp only [Option.map_some,Option.getD_some]
      rw [show joinList reserve lo opening cap a j=joinList reserve lo opening cap b j from v]

theorem main_evolve_eq (r : Nat) (reserve : BStarWarmupKeys.Key n→Option Bool)
    (lo opening cap : Nat) (a b : Bits (jointSize reserve lo opening cap))
    (M : main (A:=(keys reserve lo opening).length) a = main b)
    (neighbor : Owner→Fin 3→Owner) (seed : Owner→Snapshot) (q : Nat) :
    evolve neighbor (cubeUpdate r reserve lo opening cap (joinList reserve lo opening cap a)) opening seed q =
      evolve neighbor (cubeUpdate r reserve lo opening cap (joinList reserve lo opening cap b)) opening seed q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    funext i
    simp only [evolve,levels] at ih ⊢
    rw [ih]
    exact main_update_eq r reserve lo opening cap a b M _ (Nat.le_add_right _ _) _ _ _

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

noncomputable def openingSlice {T : Nat} (R : BStarFirstArrival.Trace Owner Snapshot (Fin 3) T)
    (r : Nat) (reserve : BStarWarmupKeys.Key n→Option Bool) (lo opening cap : Nat)
    (warmBits : Bits (keys reserve lo opening).length) : Owner→Snapshot :=
  fromTrace R (cubeUpdate r reserve lo opening cap (joinList reserve lo opening cap
    (join warmBits (fun _=>false)))) opening

/-- Count the bad first-at-cap event on words of one exact raw horizon.
The physical timing premise supplies reaching the cap on the counted
words, not exact equality of endpoint lifts. The genuine logical
probability premise is a uniform quarter bound for each opening slice;
the theorem does not infer it from finite key coverage. -/
theorem physical_bad_quarter {T₀ : Nat}
    (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history : List (Fin n)) (deadline : Nat)
    (lo opening cap : Nat) (OC : opening≤cap)
    (R₀ : BStarFirstArrival.Trace (Header (oldH6 B base)) Snapshot (Fin 3) T₀)
    (R : (w : List (Fin n)) → BStarFirstArrival.Trace (Header (oldH6 B base)) Snapshot (Fin 3) w.length)
    (view : List (Fin n)→Header (oldH6 B base)→Snapshot)
    (E : List (Fin n)→Prop)
    (badAt : (Header (oldH6 B base)→Snapshot)→Prop)
    (included : ∀ w,w.length=deadline → E w →
      (∀ i,cap≤(R w).level w.length i) ∧
      (∀ i,∃ t,FirstAt (R w) i cap t ∧ view w i=(R w).curr t i) ∧ badAt (view w))
    (startEq : ∀ w,(R w).neighbor=R₀.neighbor ∧ (R w).level 0=R₀.level 0 ∧
      (R w).curr 0=R₀.curr 0 ∧ (R w).prior 0=R₀.prior 0)
    (startLe : ∀ i,R₀.level 0 i≤opening)
    (follows : ∀ w,w.length=deadline → E w →
      let reserve := reserveMap hp base initial hh start history
      ∀ assign : Bits (jointSize reserve lo opening cap),
      (∀ j bit,firstRaw (reveal hp base hh initial (ownerAt hp base hh) start)
        (sumKey reserve lo opening cap j) history w=some bit → assign j=bit) →
      FollowsBelow (R w) cap (cubeUpdate r reserve lo opening cap (joinList reserve lo opening cap assign)))
    (bad : (Header (oldH6 B base)→Snapshot) →
      List (Bits (keys (reserveMap hp base initial hh start history) opening cap).length))
    (exactBad : ∀ seed mainBits,
      let reserve := reserveMap hp base initial hh start history
      mainBits∈bad seed ↔ badAt (evolve R₀.neighbor (cubeUpdate r reserve lo opening cap
        (joinList reserve lo opening cap (join (fun _=>false) mainBits))) opening seed (cap-opening)))
    (distinct : ∀ seed,(bad seed).Nodup)
    (quarter : ∀ seed,4*(bad seed).length≤
      2^(keys (reserveMap hp base initial hh start history) opening cap).length) :
    4*wordSum (fun w=>if E w then 1 else 0) deadline≤n^deadline := by
  let reserve := reserveMap hp base initial hh start history
  let slice := openingSlice R₀ r reserve lo opening cap
  let pred := fun seed (m : Bits (keys reserve opening cap).length) =>
    badAt (evolve R₀.neighbor (cubeUpdate r reserve lo opening cap (joinList reserve lo opening cap
      (join (fun _=>false) m))) opening seed (cap-opening))
  exact raw_warmup_quarter hp base initial hh start history deadline
    (sumCoordinate reserve lo opening cap) (sumKey reserve lo opening cap)
    (sum_fiber reserve lo opening cap) E slice pred bad exactBad distinct quarter (by
      intro w len event a agree
      have W := follows w len event a agree
      obtain ⟨reach,actual,badView⟩ := included w len event
      obtain ⟨N,L,C,P⟩ := startEq w
      have viewEq := cap_snapshot (R w) r reserve lo opening cap a W
        (fun i=>by rw [L]; exact startLe i) OC reach (view w) actual
      have sliceEq : openingSlice (R w) r reserve lo opening cap
          (warm (K:=(keys reserve opening cap).length) a)=slice (warm a) := by
        unfold openingSlice slice fromTrace
        rw [N,L,C,P]
        rfl
      change view w=evolve (R w).neighbor
        (cubeUpdate r reserve lo opening cap (joinList reserve lo opening cap a)) opening
        (openingSlice (R w) r reserve lo opening cap (warm a)) (cap-opening) at viewEq
      rw [N,sliceEq] at viewEq
      have mainEq := main_evolve_eq r reserve lo opening cap a
        (join (fun _=>false) (main (A:=(keys reserve lo opening).length) a)) (by simp)
        R₀.neighbor (slice (warm a)) (cap-opening)
      unfold pred
      exact (viewEq.trans mainEq) ▸ badView)

#print axioms cap_snapshot
#print axioms main_evolve_eq
#print axioms physical_bad_quarter
end L4.BStarWarmupEventQuarter
