import Leader.L4.PhysicalCustodyH1Censor
import Leader.Core.FiniteUniformStoppingTree

namespace L4.PhysicalCustody.H1

/-- Remaining-label potential, scaled by five. A wrong watched mark
restarts a fresh visit, while an unwatched mark spends no progress. -/
def matchingPotential (k : Nat) : Nat := 6^9 - 6^(9-k)

theorem matchingPotential_bound {k : Nat} :
    matchingPotential k ≤ matchingPotential 9 := by
  unfold matchingPotential
  have P : 0 < 6^(9-k) := Nat.pow_pos (by decide)
  simp
  omega

private theorem credit_finite : ∀ k : Fin 10, k.val>0 →
    5 + matchingPotential (k.val-1) + 5*matchingPotential 9 ≤
      6*matchingPotential k.val := by
  decide +kernel

/-- One good label and at most five wrong watched labels give at
least five units of denominator-free credit per independent raw hit. -/
theorem matchingPotential_credit (k b : Nat) (hk : 0<k) (K : k≤9) (hb : b≤5) :
    5 + matchingPotential (k-1) + b*matchingPotential 9 ≤
      (b+1)*matchingPotential k := by
  have E := credit_finite ⟨k,by omega⟩ hk
  change 5 + matchingPotential (k-1) + 5*matchingPotential 9 ≤ 6*matchingPotential k at E
  have M := matchingPotential_bound (k:=k)
  have B := Nat.mul_le_mul_left (5-b) M
  have C : b+(5-b)=5 := by omega
  have X : b*matchingPotential 9+(5-b)*matchingPotential 9=5*matchingPotential 9 := by
    rw [←Nat.add_mul,C]
  have Y : (b+1)*matchingPotential k+(5-b)*matchingPotential k=6*matchingPotential k := by
    rw [←Nat.add_mul,show (b+1)+(5-b)=6 by omega]
  omega

/-- The local Bellman inequality after the finite-label sum has been
partitioned into one requested hit, wrong watched hits and spectators. -/
theorem matchingPotential_bellman (k b spectators n : Nat)
    (hk : 0<k) (K : k≤9) (hb : b≤5) (N : n=1+b+spectators) :
    5*n + (n*matchingPotential (k-1)+b*(n*matchingPotential 9)+
      spectators*(n*matchingPotential k)) ≤ n*(n*matchingPotential k) := by
  calc
    _ = n * (5 + matchingPotential (k-1) + b*matchingPotential 9 +
      spectators*matchingPotential k) := by
      simp only [Nat.mul_add]
      ac_rfl
    _ ≤ n*((b+1)*matchingPotential k+spectators*matchingPotential k) := by
      have H := matchingPotential_credit k b hk K hb
      exact Nat.mul_le_mul_left n (Nat.add_le_add_right H _)
    _ = _ := by
      rw [←Nat.add_mul,N]
      ac_rfl

open L4.AllSizeS1Geometry

/-- An invariant region with a forward-invariant target and a
state-dependent witness on the same six watched physical labels. -/
structure MatchSpec {n : Nat} (p : Fin 5 → Fin n) where
  region : State n → Prop
  done : State n → Prop
  region_next : ∀ x e, region x → region (physicalStep x e)
  done_later : ∀ x, region x → done x → ∀ u,
    done (L4.BStarResetSchedule.run physicalStep x u)
  trial : ∀ x, region x → ∃ w : List (Fin n), w.length≤9 ∧
    (∀ e∈w,e∈watchedLabels p) ∧ ∀ u : List (Fin n), u.filter (watches p)=w →
      done (L4.BStarResetSchedule.run physicalStep x u)

/-- This ghost records only the future watched word, never edits an
actual physical mark, and carries its soundness from the current bytes. -/
structure MatchPhase {n : Nat} {p : Fin 5 → Fin n} (S : MatchSpec p) where
  state : State n
  inRegion : S.region state
  pending : List (Fin n)
  bounded : pending.length≤9
  watched : ∀ e∈pending, watches p e=true
  guarantee : ∀ u : List (Fin n), u.filter (watches p)=pending →
    S.done (L4.BStarResetSchedule.run physicalStep state u)

theorem empty_phase_safe {n : Nat} {p : Fin 5 → Fin n} {S : MatchSpec p} (q : MatchPhase S)
    (E : q.pending=[]) : S.done q.state :=
  q.guarantee [] E.symm

noncomputable def freshPhase {n : Nat} {p : Fin 5 → Fin n}
    (S : MatchSpec p) (x : State n) (auth : S.region x) : MatchPhase S :=
  let T := S.trial x auth
  let W := Classical.choose_spec T
  ⟨x,auth,Classical.choose T,W.1,fun e h => decide_eq_true (W.2.1 e h),W.2.2⟩

def idlePhase {n : Nat} {p : Fin 5 → Fin n} {S : MatchSpec p} (q : MatchPhase S) (e : Fin n)
    (idle : watches p e=false) : MatchPhase S :=
  ⟨physicalStep q.state e,S.region_next q.state e q.inRegion,
    q.pending,q.bounded,q.watched,fun u h => by
      apply q.guarantee (e::u)
      simpa only [List.filter_cons,idle,Bool.false_eq_true,if_false] using h⟩

def consumePhase {n : Nat} {p : Fin 5 → Fin n} {S : MatchSpec p} (q : MatchPhase S) (e : Fin n)
    (rest : List (Fin n)) (E : q.pending=e::rest) : MatchPhase S :=
  ⟨physicalStep q.state e,S.region_next q.state e q.inRegion,rest,
    by have B := q.bounded; rw [E,List.length_cons] at B; omega,
    fun f hf => q.watched f (E.symm ▸ List.mem_cons_of_mem _ hf),fun u h => by
      have W := q.watched e (E.symm ▸ List.mem_cons_self)
      apply q.guarantee (e::u)
      simp only [List.filter_cons,W,if_true,h,E]⟩

private theorem nodup_length_of_subset {A : Type} [BEq A] [LawfulBEq A]
    (xs ys : List A) (H : xs.Nodup) (S : ∀ x∈xs,x∈ys) : xs.length≤ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    have E := List.nodup_cons.mp H
    have mem : x∈ys := S x List.mem_cons_self
    have Q := ih (ys.erase x) E.2 (fun a ha =>
      (List.mem_erase_of_ne (fun V => E.1 (by simpa only [V] using ha))).mpr (S a (List.mem_cons_of_mem _ ha)))
    rw [List.length_erase_of_mem mem] at Q
    have P := List.length_pos_iff.mpr (List.ne_nil_of_mem mem)
    simp only [List.length_cons]
    omega

private def wrong {n : Nat} (watch : Fin n → Bool) (a e : Fin n) : Bool :=
  if e=a then false else watch e

private def spectator {n : Nat} (watch : Fin n → Bool) (a e : Fin n) : Bool :=
  if e=a then false else !watch e

private theorem bucket_sum {n : Nat} (watch : Fin n → Bool) (a : Fin n)
    (g b c : Nat) (L : List (Fin n)) :
    (L.map (fun e => if e=a then g else if watch e then b else c)).sum =
      L.count a*g + L.countP (wrong watch a)*b + L.countP (spectator watch a)*c := by
  induction L with
  | nil => simp
  | cons e L ih =>
    by_cases E : e=a
    · subst e
      simp [wrong,spectator,ih,Nat.add_mul,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
    · cases W : watch e <;>
        simp [E,W,List.count_cons_of_ne,wrong,spectator,ih,Nat.add_mul,
          Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

private theorem bucket_card {n : Nat} (watch : Fin n → Bool) (a : Fin n) :
    n = 1 + (List.finRange n).countP (wrong watch a) +
      (List.finRange n).countP (spectator watch a) := by
  have H := bucket_sum watch a 1 1 1 (List.finRange n)
  have O := (List.nodup_finRange n).count (a:=a)
  rw [if_pos (List.mem_finRange a)] at O
  have U : (List.finRange n).map (fun _ => 1) = List.ofFn (fun _ : Fin n => 1) := by
    rw [List.finRange,List.map_ofFn]
    rfl
  have V : (List.finRange n).map (fun e => if e=a then 1 else if watch e then 1 else 1) =
      (List.finRange n).map (fun _ => 1) := by
    apply List.map_congr_left
    intro e _
    simp
  rw [V,U,FiniteUniformStoppingTree.ofFn_sum_const] at H
  simpa [O] using H

private theorem wrong_count_le {n : Nat} (p : Fin 5 → Fin n) (a : Fin n)
    (W : watches p a=true) : (List.finRange n).countP (wrong (watches p) a)≤5 := by
  rw [List.countP_eq_length_filter]
  have A : a∈watchedLabels p := of_decide_eq_true W
  have H := nodup_length_of_subset ((List.finRange n).filter (wrong (watches p) a))
    ((watchedLabels p).erase a) (List.Pairwise.filter _ (List.nodup_finRange n))
    (fun e he => by
      have E := (List.mem_filter.mp he).2
      by_cases ea : e=a
      · simp [wrong,ea] at E
      · exact (List.mem_erase_of_ne ea).mpr
          (of_decide_eq_true (by simpa only [wrong,if_neg ea] using E : watches p e=true)))
  rw [List.length_erase_of_mem A,watched_labels_length] at H
  exact H

def finishedPhase {n : Nat} {p : Fin 5 → Fin n} {S : MatchSpec p} (q : MatchPhase S) (e : Fin n)
    (done : q.pending=[]) : MatchPhase S :=
  ⟨physicalStep q.state e,S.region_next q.state e q.inRegion,[],
    by simp,by simp,fun u _ => by
      exact S.done_later q.state q.inRegion (empty_phase_safe q done) (e::u)⟩

structure MatchGeometry {n : Nat} (p : Fin 5 → Fin n) : Prop where
  injective : ∀ {i j}, p i=p j → i=j
  edge : ∀ e, rightNeighbor (p (tileLeft e))=p (tileRight e)
  sep : ∀ j : Fin n,j≠rightNeighbor j
  sepTwo : ∀ j : Fin n,j≠rightNeighbor (rightNeighbor j)

noncomputable def matchStep {n : Nat} {p : Fin 5 → Fin n}
    {S : MatchSpec p} (q : MatchPhase S) (e : Fin n) : MatchPhase S :=
  match H : q.pending with
  | [] => finishedPhase q e H
  | a::rest =>
    if E : e=a then consumePhase q e rest (E.symm ▸ H)
    else if W : watches p e=false then idlePhase q e W
    else freshPhase S (physicalStep q.state e) (S.region_next q.state e q.inRegion)

theorem match_step_projects {n : Nat} {p : Fin 5 → Fin n}
    {S : MatchSpec p} (q : MatchPhase S) (e : Fin n) :
    (matchStep q e).state=physicalStep q.state e := by
  unfold matchStep
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

private theorem matchStep_cons {n : Nat} {p : Fin 5 → Fin n}
    {S : MatchSpec p} (q : MatchPhase S) (e a : Fin n) (rest : List (Fin n))
    (H : q.pending=a::rest) :
    matchStep q e =
      if E : e=a then consumePhase q e rest (E.symm ▸ H)
      else if W : watches p e=false then idlePhase q e W
      else freshPhase S (physicalStep q.state e) (S.region_next q.state e q.inRegion) := by
  unfold matchStep
  split
  · rename_i h
    rw [H] at h
    cases h
  · rename_i b tail h
    have E := List.cons.inj (H.symm.trans h)
    obtain ⟨rfl,rfl⟩ := E
    rfl

private def phaseValue {n : Nat} {p : Fin 5 → Fin n} {S : MatchSpec p} (q : MatchPhase S) : Nat :=
  n*matchingPotential q.pending.length

theorem phase_local_bellman {n : Nat} {p : Fin 5 → Fin n}
    {S : MatchSpec p} (q : MatchPhase S) (H : q.pending≠[]) :
    5*n + (List.ofFn (fun e => phaseValue (matchStep q e))).sum ≤ n*phaseValue q := by
  cases E : q.pending with
  | nil => exact (H E).elim
  | cons a rest =>
    let k := q.pending.length
    have L : k=rest.length+1 := by simp [k,E]
    have W := q.watched a (E.symm ▸ List.mem_cons_self)
    have sum := FiniteUniformStoppingTree.ofFn_sum_le
      (fun e => phaseValue (matchStep q e))
      (fun e => if e=a then n*matchingPotential (k-1)
        else if watches p e then n*matchingPotential 9 else phaseValue q)
      (by
        intro e
        rw [matchStep_cons q e a rest E]
        by_cases S : e=a
        · simp only [S,dif_pos,if_true,phaseValue,consumePhase,L,Nat.add_sub_cancel]
          exact Nat.le_refl _
        · rw [dif_neg S, if_neg S]
          by_cases R : watches p e=false
          · rw [dif_pos R]
            simp only [R,Bool.false_eq_true,if_false,phaseValue,idlePhase,Nat.le_refl]
          · have T : watches p e=true := by cases B : watches p e <;> simp_all
            rw [dif_neg R, if_pos T]
            exact Nat.mul_le_mul_left n matchingPotential_bound)
    have enum : (List.ofFn (fun e => if e=a then n*matchingPotential (k-1)
        else if watches p e then n*matchingPotential 9 else phaseValue q)) =
          (List.finRange n).map (fun e => if e=a then n*matchingPotential (k-1)
        else if watches p e then n*matchingPotential 9 else phaseValue q) := by
      rw [List.finRange,List.map_ofFn]
      rfl
    rw [enum,bucket_sum] at sum
    have O := (List.nodup_finRange n).count (a:=a)
    rw [if_pos (List.mem_finRange a)] at O
    rw [O,Nat.one_mul] at sum
    have C := matchingPotential_bellman k
      ((List.finRange n).countP (wrong (watches p) a))
      ((List.finRange n).countP (spectator (watches p) a)) n
      (by omega) q.bounded (wrong_count_le p a W) (bucket_card (watches p) a)
    exact Nat.le_trans (Nat.add_le_add_left sum _) C

private theorem phase_cost {n : Nat} {p : Fin 5 → Fin n}
    {S : MatchSpec p} (q : MatchPhase S) (t : Nat) :
    5 * iidHitCost (matchStep) (fun z => z.pending=[]) t q ≤ phaseValue q * n^t := by
  induction t generalizing q with
  | zero => simp [iidHitCost]
  | succ t ih =>
    by_cases H : q.pending=[]
    · simp [iidHitCost,H]
    · simp only [iidHitCost,if_neg H]
      have S := FiniteUniformStoppingTree.ofFn_sum_le
        (fun e => 5 * iidHitCost (matchStep) (fun z => z.pending=[]) t (matchStep q e))
        (fun e => phaseValue (matchStep q e) * n^t) (fun e => ih _)
      rw [FiniteUniformStoppingTree.ofFn_sum_mul_left] at S
      have R : (List.ofFn (fun e => phaseValue (matchStep q e) * n^t)).sum =
          n^t * (List.ofFn (fun e => phaseValue (matchStep q e))).sum := by
        rw [←FiniteUniformStoppingTree.ofFn_sum_mul_left]
        apply FiniteUniformStoppingTree.ofFn_sum_eq
        intro e
        exact Nat.mul_comm _ _
      rw [R] at S
      have B := phase_local_bellman q H
      calc
        _ = n^t*(5*n)+5*(List.ofFn (fun e => iidHitCost (matchStep) (fun z => z.pending=[])
          t (matchStep q e))).sum := by rw [Nat.mul_add,Nat.pow_succ]; ac_rfl
        _ ≤ n^t*(5*n)+n^t*(List.ofFn (fun e => phaseValue (matchStep q e))).sum :=
          Nat.add_le_add_left S _
        _ = n^t*(5*n+(List.ofFn (fun e => phaseValue (matchStep q e))).sum) := by rw [Nat.mul_add]
        _ ≤ n^t*(n*phaseValue q) := Nat.mul_le_mul_left _ B
        _ = _ := by rw [Nat.pow_succ]; ac_rfl

private theorem phase_cost_projects {n : Nat} {p : Fin 5 → Fin n}
    {S : MatchSpec p} (q : MatchPhase S) (t : Nat) :
    iidHitCost physicalStep S.done t q.state ≤
      iidHitCost (matchStep) (fun z => z.pending=[]) t q := by
  induction t generalizing q with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    by_cases B : S.done q.state
    · simp [iidHitCost,B]
    · have H : q.pending≠[] := fun E => B (empty_phase_safe q E)
      simp only [iidHitCost,if_neg B,if_neg H]
      apply Nat.add_le_add_left
      apply FiniteUniformStoppingTree.ofFn_sum_le
      intro e
      rw [←match_step_projects q e]
      exact ih _

/-- Every authenticated physical start, on an actual window satisfying
the ring geometry, clears the designated bad bond within the stated
truncated IID mean. The monitor invokes new state-dependent trial words
but does not change one raw sampled mark. -/
theorem match_expected {n : Nat} {p : Fin 5 → Fin n}
    (S : MatchSpec p) (x : State n) (H : S.region x) :
    IIDExpectedHittingTimeAtMost physicalStep S.done x (n*6^9) := by
  let q := freshPhase S x H
  intro t
  have P := phase_cost_projects q t
  have C := phase_cost q t
  have U : phaseValue q ≤ n*6^9 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have R := Nat.le_trans C (Nat.mul_le_mul_right (n^t) U)
  change iidHitCost physicalStep S.done t x ≤ _
  change iidHitCost physicalStep S.done t x ≤ _ at P
  omega

theorem physical_bad_bond_expected {n : Nat} {p : Fin 5 → Fin n}
    (G : MatchGeometry p) (x : State n) (H : Authenticated x) :
    IIDExpectedHittingTimeAtMost physicalStep (fun y => ¬ badBond y (p 1)) x (n*6^9) := by
  let S : MatchSpec p :=
    ⟨Authenticated,fun y => ¬badBond y (p 1),fun y e H => authenticated_next e G.sep G.sepTwo H,
    fun y A done w => no_bad_bond_later y (p 1) G.sep G.sepTwo A done w,
    fun y A => by
      obtain ⟨w,L,W,F⟩ := censored_bad_bond_trial p G.injective G.edge G.sep G.sepTwo y A
      exact ⟨w,L,W,fun u E => by simpa only [List.append_nil] using F u [] E⟩⟩
  exact match_expected S x H

private theorem ring_separations {n : Nat} (N : 5≤n) (i : Fin n) :
    i≠rightNeighbor i ∧ i≠rightNeighbor (rightNeighbor i) := by
  let p := cyclicWindow i
  have E : p 0=i := by
    apply Fin.ext
    change (i.val+0)%n=i.val
    simp [Nat.mod_eq_of_lt i.isLt]
  have J : p 1=rightNeighbor i := (cyclicWindow_edges N i 0).symm.trans (congrArg rightNeighbor E)
  have K : p 2=rightNeighbor (rightNeighbor i) :=
    (cyclicWindow_edges N i 1).symm.trans (congrArg rightNeighbor J)
  constructor
  · intro C
    exact (by decide : (0 : Fin 5)≠1) (cyclicWindow_injective N i (E.trans (C.trans J.symm)))
  · intro C
    exact (by decide : (0 : Fin 5)≠2) (cyclicWindow_injective N i (E.trans (C.trans K.symm)))

theorem ring_bad_bond_expected {n : Nat} (N : 5≤n) (i : Fin n) (x : State n)
    (H : Authenticated x) :
    IIDExpectedHittingTimeAtMost physicalStep (fun y => ¬badBond y i) x (n*6^9) := by
  let p := cyclicWindow (incoming i)
  have C : MatchGeometry p :=
    ⟨cyclicWindow_injective N _,cyclicWindow_edges N _,fun j => (ring_separations N j).1,
      fun j => (ring_separations N j).2⟩
  have D : p 1=i := incoming_spec i
  have T := physical_bad_bond_expected C x H
  rw [D] at T
  exact T

open L4.PhysicalCustody

private theorem raw_bad_bond_cost {s n : Nat} (x : Raw s n) (i : Fin n) (t : Nat) :
    iidHitCost (rawNext s) (fun y => ¬badBond (projection y) i) t x =
      iidHitCost physicalStep (fun y => ¬ badBond y i) t (projection x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    simp only [iidHitCost]
    split
    · rfl
    · congr 1
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      rw [ih]
      have E : projection (rawNext s x e)=physicalStep (projection x) e :=
        funext (exact_physical_projection (rows s) x e)
      rw [E]

/-- Literal production endpoint: after any two full covers, each
prescribed physical bad bond has a uniform IID hitting-time bound.
The theorem charges the post-cover clock, not the two covers themselves. -/
theorem raw_bad_bond_after_covers_expected {s n : Nat} (N : 5≤n)
    (x : Raw s n) (a b : List (Fin n)) (ha : ∀ i,i∈a) (hb : ∀ i,i∈b) (i : Fin n) :
    IIDExpectedHittingTimeAtMost (rawNext s) (fun y => ¬ badBond (projection y) i)
      (rawRun x (a++b)) (n*6^9) := by
  have H : Authenticated (projection (rawRun x (a++b))) :=
    fun j => raw_h1_covers (by omega) x a b ha hb j
  intro t
  rw [raw_bad_bond_cost]
  exact ring_bad_bond_expected N i _ H t

end L4.PhysicalCustody.H1
