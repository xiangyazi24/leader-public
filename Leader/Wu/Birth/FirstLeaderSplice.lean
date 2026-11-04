import Leader.Wu.Birth.FirstLeaderComposition

namespace BirthPhaseFirstLeaderComposition

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthSigMoveDisposalRepair
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau : Nat}


/-! ## Exact raw-word product split -/

theorem wordSum_horizon_add
    (n T U : Nat) (f : List (Fin n) -> Nat) :
    FixedSpanRenewalPayload.wordSum n (T + U) f =
      FixedSpanRenewalPayload.wordSum n T
        (fun u => FixedSpanRenewalPayload.wordSum n U
          (fun v => f (u ++ v))) := by
  induction T generalizing f with
  | zero =>
      simp [FixedSpanRenewalPayload.wordSum, allSchedules]
  | succ T ih =>
      rw [Nat.succ_add]
      change
        FixedSpanRenewalPayload.wordSum n (T + U + 1) f =
          FixedSpanRenewalPayload.wordSum n (T + 1)
            (fun u => FixedSpanRenewalPayload.wordSum n U
              (fun v => f (u ++ v)))
      rw [FixedSpanRenewalPayload.wordSum_succ,
        FixedSpanRenewalPayload.wordSum_succ]
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      simpa only [List.cons_append] using
        ih (f := fun w => f (e :: w))


private theorem wordSum_congr_length
    {n T : Nat} (f g : List (Fin n) -> Nat)
    (h : forall u : List (Fin n), u.length = T -> f u = g u) :
    FixedSpanRenewalPayload.wordSum n T f =
      FixedSpanRenewalPayload.wordSum n T g := by
  rw [<- FixedSpanRenewalPayload.rawWord_sum n T f,
    <- FixedSpanRenewalPayload.rawWord_sum n T g]
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro i
  exact h _ (FixedSpanRenewalPayload.rawWord_length n T i)


private theorem bool_eq_false_of_ne_true (b : Bool) (h : ¬ b = true) :
    b = false := by
  cases b <;> simp_all


private theorem activeCount_success
    {S : Type} {m : Nat}
    (step : S -> Fin m -> FiniteUniformStoppingTree.StopNode S)
    (T : Nat) :
    FiniteUniformStoppingTree.activeCount step
      (.success : FiniteUniformStoppingTree.StopNode S) T = 0 := by
  induction T with
  | zero => rfl
  | succ T ih =>
      change
        (List.ofFn (fun _ : Fin m =>
          FiniteUniformStoppingTree.activeCount step
            (.success : FiniteUniformStoppingTree.StopNode S) T)).sum = 0
      rw [FiniteUniformStoppingTree.ofFn_sum_eq _ _ (fun _ => ih),
        FiniteUniformStoppingTree.ofFn_sum_const]
      simp


/-! ## A generic exact avoidance interpretation of target failure -/

noncomputable def avoidNumerator
    {S : Type} {n : Nat}
    (Avoid : S -> List (Fin n) -> Prop) (x : S) (T : Nat) : Nat := by
  classical
  exact FixedSpanRenewalPayload.wordSum n T
    (fun u => if Avoid x u then 1 else 0)


private theorem avoidNumerator_horizon_add
    {S : Type} {n : Nat}
    (step : S -> Fin n -> S)
    (Avoid : S -> List (Fin n) -> Prop)
    (happend : forall x u v,
      Avoid x (u ++ v) <->
        Avoid x u /\
          Avoid (BirthPhaseGenericRenewal.rawEndpoint step x u) v)
    (x : S) [DecidablePred (Avoid x)] (T U : Nat) :
    avoidNumerator Avoid x (T + U) =
      FixedSpanRenewalPayload.wordSum n T
        (fun u =>
          if Avoid x u then
            avoidNumerator Avoid
              (BirthPhaseGenericRenewal.rawEndpoint step x u) U
          else 0) := by
  classical
  unfold avoidNumerator
  rw [wordSum_horizon_add]
  apply wordSum_congr_length
  intro u _hu
  by_cases hpre : Avoid x u
  · rw [if_pos hpre]
    apply wordSum_congr_length
    intro v _hv
    by_cases hsuf :
        Avoid (BirthPhaseGenericRenewal.rawEndpoint step x u) v
    · have hall : Avoid x (u ++ v) :=
        (happend x u v).2 ⟨hpre, hsuf⟩
      simp [hall, hsuf]
    · have hnall : ¬ Avoid x (u ++ v) := by
        intro hall
        exact hsuf ((happend x u v).1 hall).2
      simp [hnall, hsuf]
  · rw [if_neg hpre]
    calc
      _ =
          FixedSpanRenewalPayload.wordSum n U (fun _ => 0) := by
            apply wordSum_congr_length
            intro v _hv
            have hnall : ¬ Avoid x (u ++ v) := by
              intro hall
              exact hpre ((happend x u v).1 hall).1
            simp [hnall]
      _ = 0 := by
        rw [← FixedSpanRenewalPayload.rawWord_sum n U (fun _ => 0)]
        simpa only [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero]


private theorem indicator_wordSum_le_pow
    {n T : Nat} (P : List (Fin n) -> Prop) [DecidablePred P] :
    FixedSpanRenewalPayload.wordSum n T
        (fun u => if P u then 1 else 0) <= n ^ T := by
  rw [<- FixedSpanRenewalPayload.rawWord_sum n T
    (fun u => if P u then 1 else 0)]
  calc
    (List.ofFn (fun i : Fin (n ^ T) =>
        if P (FixedSpanRenewalPayload.rawWord n T i) then 1 else 0)).sum <=
        (List.ofFn (fun _ : Fin (n ^ T) => 1)).sum := by
          apply FiniteUniformStoppingTree.ofFn_sum_le
          intro i
          by_cases h : P (FixedSpanRenewalPayload.rawWord n T i) <;>
            simp [h]
    _ = n ^ T * 1 :=
      FiniteUniformStoppingTree.ofFn_sum_const (n ^ T) 1
    _ = n ^ T := by simp


private theorem avoidNumerator_extension_le
    {S : Type} {n : Nat}
    (step : S -> Fin n -> S)
    (Avoid : S -> List (Fin n) -> Prop)
    (happend : forall x u v,
      Avoid x (u ++ v) <->
        Avoid x u /\
          Avoid (BirthPhaseGenericRenewal.rawEndpoint step x u) v)
    (x : S) (T U : Nat) :
    avoidNumerator Avoid x (T + U) <=
      avoidNumerator Avoid x T * n ^ U := by
  classical
  calc
    avoidNumerator Avoid x (T + U) =
        FixedSpanRenewalPayload.wordSum n T
          (fun u =>
            if Avoid x u then
              avoidNumerator Avoid
                (BirthPhaseGenericRenewal.rawEndpoint step x u) U
            else 0) :=
      avoidNumerator_horizon_add step Avoid happend x T U
    _ =
        (List.ofFn (fun i : Fin (n ^ T) =>
          if Avoid x (FixedSpanRenewalPayload.rawWord n T i) then
            avoidNumerator Avoid
              (BirthPhaseGenericRenewal.rawEndpoint step x
                (FixedSpanRenewalPayload.rawWord n T i)) U
          else 0)).sum := by
      exact (FixedSpanRenewalPayload.rawWord_sum n T _).symm
    _ <=
        (List.ofFn (fun i : Fin (n ^ T) =>
          n ^ U *
            (if Avoid x (FixedSpanRenewalPayload.rawWord n T i)
              then 1 else 0))).sum := by
      apply FiniteUniformStoppingTree.ofFn_sum_le
      intro i
      by_cases hpre : Avoid x (FixedSpanRenewalPayload.rawWord n T i)
      · simp only [hpre, if_pos, Nat.mul_one]
        unfold avoidNumerator
        exact indicator_wordSum_le_pow
          (fun v => Avoid
            (BirthPhaseGenericRenewal.rawEndpoint step x
              (FixedSpanRenewalPayload.rawWord n T i)) v)
      · simp [hpre]
    _ = n ^ U *
        (List.ofFn (fun i : Fin (n ^ T) =>
          if Avoid x (FixedSpanRenewalPayload.rawWord n T i)
            then 1 else 0)).sum :=
      FiniteUniformStoppingTree.ofFn_sum_mul_left (n ^ U) _
    _ = n ^ U * avoidNumerator Avoid x T := by
      unfold avoidNumerator
      exact congrArg (fun z : Nat => n ^ U * z)
        (FixedSpanRenewalPayload.rawWord_sum n T
          (fun u => if Avoid x u then 1 else 0))
    _ = avoidNumerator Avoid x T * n ^ U := by
      ac_rfl


private theorem targetFailureNumerator_eq_avoidNumerator
    {S : Type} {n L : Nat}
    (step : S -> Fin n -> S)
    (Carrier Reacquire : S -> Prop)
    (target : S -> List (Fin n) -> Bool)
    (hclosed : forall x,
      BirthPhaseGenericRenewal.RenewalAllowed Carrier Reacquire x ->
      forall u, u.length = L -> target x u = false ->
        BirthPhaseGenericRenewal.RenewalAllowed Carrier Reacquire
          (BirthPhaseGenericRenewal.rawEndpoint step x u))
    (Avoid : S -> List (Fin n) -> Prop)
    (hempty : forall x, Avoid x [])
    (happend : forall x u v,
      Avoid x (u ++ v) <->
        Avoid x u /\
          Avoid (BirthPhaseGenericRenewal.rawEndpoint step x u) v)
    (htarget : forall x u, u.length = L ->
      (target x u = false <-> Avoid x u))
    (x : BirthPhaseGenericRenewal.RenewalState Carrier Reacquire)
    (blocks : Nat) :
    BirthPhaseGenericRenewal.targetFailureNumerator
        step Carrier Reacquire target hclosed x blocks =
      avoidNumerator Avoid x.1 (L * blocks) := by
  classical
  induction blocks generalizing x with
  | zero =>
      have he := hempty x.1
      change 1 = avoidNumerator Avoid x.1 0
      simp [avoidNumerator, FixedSpanRenewalPayload.wordSum,
        allSchedules, he]
  | succ blocks ih =>
      let M := BirthPhaseGenericRenewal.targetStep
        step Carrier Reacquire target hclosed
      have hleft :
          BirthPhaseGenericRenewal.targetFailureNumerator
              step Carrier Reacquire target hclosed x (blocks + 1) =
            FixedSpanRenewalPayload.wordSum n L
              (fun u =>
                if target x.1 u = true then 0
                else avoidNumerator Avoid
                  (BirthPhaseGenericRenewal.rawEndpoint step x.1 u)
                  (L * blocks)) := by
        change
          (List.ofFn (fun i : Fin (n ^ L) =>
            FiniteUniformStoppingTree.activeCount M (M x i) blocks)).sum = _
        rw [<- FixedSpanRenewalPayload.rawWord_sum n L
          (fun u =>
            if target x.1 u = true then 0
            else avoidNumerator Avoid
              (BirthPhaseGenericRenewal.rawEndpoint step x.1 u)
              (L * blocks))]
        apply FiniteUniformStoppingTree.ofFn_sum_eq
        intro i
        let u := FixedSpanRenewalPayload.rawWord n L i
        have hlen : u.length = L := by
          simpa [u] using FixedSpanRenewalPayload.rawWord_length n L i
        change
          FiniteUniformStoppingTree.activeCount M (M x i) blocks =
            (if target x.1 u = true then 0
             else avoidNumerator Avoid
               (BirthPhaseGenericRenewal.rawEndpoint step x.1 u)
               (L * blocks))
        by_cases ht : target x.1 u = true
        · have hMi : M x i = .success := by
            simp [M, BirthPhaseGenericRenewal.targetStep, u, ht]
          rw [hMi, activeCount_success, if_pos ht]
        · have htf : target x.1 u = false :=
            bool_eq_false_of_ne_true _ ht
          let y : BirthPhaseGenericRenewal.RenewalState Carrier Reacquire :=
            ⟨BirthPhaseGenericRenewal.rawEndpoint step x.1 u,
              hclosed x.1 x.2 u hlen htf⟩
          have hMi : M x i = .active y := by
            simp [M, BirthPhaseGenericRenewal.targetStep, u, ht, y]
          rw [hMi, if_neg ht]
          have hi := ih (x := y)
          simpa [M, BirthPhaseGenericRenewal.targetFailureNumerator, y] using hi
      calc
        BirthPhaseGenericRenewal.targetFailureNumerator
            step Carrier Reacquire target hclosed x (blocks + 1) =
            FixedSpanRenewalPayload.wordSum n L
              (fun u =>
                if target x.1 u = true then 0
                else avoidNumerator Avoid
                  (BirthPhaseGenericRenewal.rawEndpoint step x.1 u)
                  (L * blocks)) := hleft
        _ = FixedSpanRenewalPayload.wordSum n L
              (fun u =>
                if Avoid x.1 u then
                  avoidNumerator Avoid
                    (BirthPhaseGenericRenewal.rawEndpoint step x.1 u)
                    (L * blocks)
                else 0) := by
          apply wordSum_congr_length
          intro u hlen
          by_cases ht : target x.1 u = true
          · have hna : ¬ Avoid x.1 u := by
              intro ha
              have hf := (htarget x.1 u hlen).2 ha
              rw [ht] at hf
              cases hf
            simp [ht, hna]
          · have htf : target x.1 u = false :=
              bool_eq_false_of_ne_true _ ht
            have ha : Avoid x.1 u := (htarget x.1 u hlen).1 htf
            simp [ht, ha]
        _ = avoidNumerator Avoid x.1 (L + L * blocks) :=
          (avoidNumerator_horizon_add
            step Avoid happend x.1 L (L * blocks)).symm
        _ = avoidNumerator Avoid x.1 (L * (blocks + 1)) := by
          have hmul : L + L * blocks = L * (blocks + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            ac_rfl
          rw [hmul]

def NoCapAlong
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) : List (Fin n) -> Prop
  | [] => True
  | e :: es =>
      ¬ BirthShortDoneTerminalPassiveR4.RowCap2
        hpsi h2 kappa ring C e /\
      NoCapAlong hpsi h2 kappa ring
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) es


private theorem noCapAlong_append
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u v : List (Fin n)) :
    NoCapAlong hpsi h2 kappa ring C (u ++ v) <->
      NoCapAlong hpsi h2 kappa ring C u /\
      NoCapAlong hpsi h2 kappa ring
        (BirthPhaseGenericRenewal.rawEndpoint
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C u) v := by
  induction u generalizing C with
  | nil =>
      simp [NoCapAlong, BirthPhaseGenericRenewal.rawEndpoint]
  | cons e es ih =>
      simp only [List.cons_append, NoCapAlong]
      rw [ih]
      simp [BirthPhaseGenericRenewal.rawEndpoint, and_assoc]


private theorem firstCapWithin_cons_iff
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) (es : List (Fin n)) :
    BirthPhaseWait2BlockProgress.FirstCapWithin
        hpsi h2 kappa ring C (e :: es) <->
      BirthShortDoneTerminalPassiveR4.RowCap2
          hpsi h2 kappa ring C e \/
        BirthPhaseWait2BlockProgress.FirstCapWithin
          hpsi h2 kappa ring
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) es := by
  constructor
  · rintro ⟨pre, a, post, hword, hcap⟩
    cases pre with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at hword
        rcases hword with ⟨hea, hrest⟩
        subst a
        subst post
        exact Or.inl hcap
    | cons b pre =>
        simp only [List.cons_append, List.cons.injEq] at hword
        rcases hword with ⟨heb, hrest⟩
        subst b
        right
        refine ⟨pre, a, post, hrest, ?_⟩
        simpa using hcap
  · intro h
    rcases h with hcap | htail
    · exact ⟨[], e, es, rfl, hcap⟩
    · rcases htail with ⟨pre, a, post, hword, hcap⟩
      refine ⟨e :: pre, a, post, ?_, ?_⟩
      · simp [hword]
      · simpa using hcap


private theorem noCapAlong_iff_not_firstCapWithin
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u : List (Fin n)) :
    NoCapAlong hpsi h2 kappa ring C u <->
      ¬ BirthPhaseWait2BlockProgress.FirstCapWithin
        hpsi h2 kappa ring C u := by
  induction u generalizing C with
  | nil =>
      simp [NoCapAlong, BirthPhaseWait2BlockProgress.FirstCapWithin]
  | cons e es ih =>
      rw [firstCapWithin_cons_iff]
      simp [NoCapAlong, ih]


private theorem target_false_iff_noCapAlong
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u : List (Fin n)) :
    BirthPhaseWait2BlockProgress.target
        hpsi h2 kappa ring C u = false <->
      NoCapAlong hpsi h2 kappa ring C u := by
  classical
  by_cases hcap : BirthPhaseWait2BlockProgress.FirstCapWithin
      hpsi h2 kappa ring C u
  · have hnc : ¬ NoCapAlong hpsi h2 kappa ring C u := by
      intro hncap
      exact (noCapAlong_iff_not_firstCapWithin
        hpsi h2 kappa ring C u).1 hncap hcap
    simp [BirthPhaseWait2BlockProgress.target, hcap, hnc]
  · have hnc : NoCapAlong hpsi h2 kappa ring C u :=
      (noCapAlong_iff_not_firstCapWithin
        hpsi h2 kappa ring C u).2 hcap
    simp [BirthPhaseWait2BlockProgress.target, hcap, hnc]


/-- Literal original-word numerator for avoiding every cap row. -/
noncomputable def firstCapRawFailureNumerator
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (T : Nat) : Nat :=
  avoidNumerator (NoCapAlong hpsi h2 kappa ring) C T


/-- B5's erased-success stopped count is exactly the literal original-word
no-cap count.  Thus no successful endpoint has to be reconstructed from the
stopped tree. -/
theorem firstCapFailureNumerator_eq_raw
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hclosed4 : BirthPhaseWait2BlockProgress.HClosed
      hpsi h2 hn kappa tau ring anchor)
    (C : FC n psi kappa tau)
    (hC : BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor C) :
    firstCapFailureNumerator
        hpsi h2 hn kappa tau ring anchor hclosed4 C hC =
      firstCapRawFailureNumerator
        hpsi h2 kappa ring C (firstCapHorizon n kappa) := by
  have hraw := targetFailureNumerator_eq_avoidNumerator
    (step := BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
    (Carrier := BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor)
    (Reacquire := BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor)
    (target := BirthPhaseWait2BlockProgress.target hpsi h2 kappa ring)
    (hclosed := hclosed4)
    (Avoid := NoCapAlong hpsi h2 kappa ring)
    (hempty := fun _ => trivial)
    (happend := noCapAlong_append hpsi h2 kappa ring)
    (htarget := fun D u _ =>
      target_false_iff_noCapAlong hpsi h2 kappa ring D u)
    (x := ⟨C, Or.inl hC⟩)
    (blocks :=
      halfBudgetK n BirthPhaseWait2BlockProgress.Q *
        BirthPhaseWait2BlockProgress.R kappa)
  have hT :
      BirthPhaseWait2BlockProgress.L n *
          (halfBudgetK n BirthPhaseWait2BlockProgress.Q *
            BirthPhaseWait2BlockProgress.R kappa) =
        firstCapHorizon n kappa := by
    unfold firstCapHorizon
    ac_rfl
  calc
    firstCapFailureNumerator
        hpsi h2 hn kappa tau ring anchor hclosed4 C hC =
      BirthPhaseGenericRenewal.targetFailureNumerator
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
        (BirthPhaseWait2BlockProgress.Carrier
          hpsi h2 hn ring anchor)
        (BirthPhaseWait2BlockProgress.Reacquire
          hpsi h2 hn kappa tau ring anchor)
        (BirthPhaseWait2BlockProgress.target hpsi h2 kappa ring)
        hclosed4
        (⟨C, Or.inl hC⟩ : BirthPhaseGenericRenewal.RenewalState
          (BirthPhaseWait2BlockProgress.Carrier hpsi h2 hn ring anchor)
          (BirthPhaseWait2BlockProgress.Reacquire
            hpsi h2 hn kappa tau ring anchor))
        (halfBudgetK n BirthPhaseWait2BlockProgress.Q *
          BirthPhaseWait2BlockProgress.R kappa) := rfl
    _ = avoidNumerator (NoCapAlong hpsi h2 kappa ring) C
        (BirthPhaseWait2BlockProgress.L n *
          (halfBudgetK n BirthPhaseWait2BlockProgress.Q *
            BirthPhaseWait2BlockProgress.R kappa)) := hraw
    _ = firstCapRawFailureNumerator
        hpsi h2 kappa ring C (firstCapHorizon n kappa) := by
      rw [hT]
      rfl


private instance instDecidableRowCap2FirstLeaderSplice
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) :
    Decidable (BirthShortDoneTerminalPassiveR4.RowCap2
      hpsi h2 kappa ring C e) := by
  unfold BirthShortDoneTerminalPassiveR4.RowCap2
  dsimp only
  infer_instance

private theorem firstCapRawFailureNumerator_succ
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (T : Nat) :
    firstCapRawFailureNumerator hpsi h2 kappa ring C (T + 1) =
      (List.ofFn (fun e : Fin n =>
        if BirthShortDoneTerminalPassiveR4.RowCap2
            hpsi h2 kappa ring C e then 0
        else firstCapRawFailureNumerator hpsi h2 kappa ring
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) T)).sum := by
  classical
  unfold firstCapRawFailureNumerator avoidNumerator
  rw [FixedSpanRenewalPayload.wordSum_succ]
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro e
  by_cases hcap : BirthShortDoneTerminalPassiveR4.RowCap2
      hpsi h2 kappa ring C e
  · rw [if_pos hcap]
    calc
      FixedSpanRenewalPayload.wordSum n T
          (fun u =>
            if NoCapAlong hpsi h2 kappa ring C (e :: u)
            then 1 else 0) =
          FixedSpanRenewalPayload.wordSum n T (fun _ => 0) := by
            apply wordSum_congr_length
            intro u _hu
            simp [NoCapAlong, hcap]
      _ = 0 := by
        rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun _ => 0)]
        simpa only [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero]
  · rw [if_neg hcap]
    apply wordSum_congr_length
    intro u _hu
    simp [NoCapAlong, hcap]

private theorem noBirthAlong_append
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u v : List (Fin n)) :
    BirthShortDoneTerminalObserver.NoBirthAlong
        hpsi (by decide : 0 < 2) h2 ring C (u ++ v) <->
      BirthShortDoneTerminalObserver.NoBirthAlong
          hpsi (by decide : 0 < 2) h2 ring C u /\
        BirthShortDoneTerminalObserver.NoBirthAlong
          hpsi (by decide : 0 < 2) h2 ring
          (BirthPhaseGenericRenewal.rawEndpoint
            (BirthPhaseCapToFirstBirth.currentStep hpsi h2 ring) C u) v := by
  induction u generalizing C with
  | nil =>
      simp [BirthShortDoneTerminalObserver.NoBirthAlong,
        BirthPhaseGenericRenewal.rawEndpoint]
  | cons e es ih =>
      simp only [List.cons_append,
        BirthShortDoneTerminalObserver.NoBirthAlong]
      rw [ih]
      simp [BirthPhaseGenericRenewal.rawEndpoint,
        BirthPhaseCapToFirstBirth.currentStep, and_assoc]


private theorem firstBirthGoodBit_false_iff_noBirthAlong
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u : List (Fin n)) :
    BirthPhaseCapToFirstBirth.firstBirthGoodBit hpsi h2 ring C u = false <->
      BirthShortDoneTerminalObserver.NoBirthAlong
        hpsi (by decide : 0 < 2) h2 ring C u := by
  induction u generalizing C with
  | nil =>
      simp [BirthPhaseCapToFirstBirth.firstBirthGoodBit,
        BirthShortDoneTerminalObserver.NoBirthAlong]
  | cons e es ih =>
      cases hb : BirthShortDoneTerminalObserver.birthEvent
          hpsi (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e)) with
      | false =>
          simp [BirthPhaseCapToFirstBirth.firstBirthGoodBit,
            BirthShortDoneTerminalObserver.NoBirthAlong,
            BirthPhaseCapToFirstBirth.currentStep, hb, ih]
      | true =>
          simp [BirthPhaseCapToFirstBirth.firstBirthGoodBit,
            BirthShortDoneTerminalObserver.NoBirthAlong, hb]


private theorem avoidNumerator_noBirth_eq
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (T : Nat) :
    avoidNumerator
        (fun D u => BirthShortDoneTerminalObserver.NoBirthAlong
          hpsi (by decide : 0 < 2) h2 ring D u) C T =
      firstLeaderNoBirthNumerator hpsi h2 ring C T := by
  unfold avoidNumerator firstLeaderNoBirthNumerator
  apply wordSum_congr_length
  intro u _hu
  unfold BirthShortDoneTerminalNoHitCount.noBirthBit
  rfl


/-- B6's target-only stopped tree counts precisely the original words with no
birth on the charged suffix. -/
theorem firstBirthFailureNumerator_eq_noBirth
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (hclosed6 : BirthPhaseCapToFirstBirth.hclosed6
      (n := n) (kappa := kappa) (tau := tau) hpsi h2 ring)
    (D : FC n psi kappa tau)
    (hD : BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring D) :
    firstBirthFailureNumerator hpsi h2 ring hclosed6 D hD =
      firstLeaderNoBirthNumerator hpsi h2 ring D
        (firstBirthHorizon n psi kappa tau) := by
  have hraw := targetFailureNumerator_eq_avoidNumerator
    (step := BirthPhaseCapToFirstBirth.currentStep hpsi h2 ring)
    (Carrier := BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring)
    (Reacquire := BirthPhaseCapToFirstBirth.B6ReacquireCarrier hpsi h2 ring)
    (target := BirthPhaseCapToFirstBirth.firstBirthGoodBit hpsi h2 ring)
    (hclosed := hclosed6)
    (Avoid := fun E u => BirthShortDoneTerminalObserver.NoBirthAlong
      hpsi (by decide : 0 < 2) h2 ring E u)
    (hempty := fun _ => trivial)
    (happend := noBirthAlong_append hpsi h2 ring)
    (htarget := fun E u _ =>
      firstBirthGoodBit_false_iff_noBirthAlong hpsi h2 ring E u)
    (x := ⟨D, Or.inl hD⟩)
    (blocks :=
      halfBudgetK n (BirthPhaseCapToFirstBirth.Q6 n psi kappa tau) *
        BirthPhaseCapToFirstBirth.R6)
  have hT :
      BirthPhaseCapToFirstBirth.L6 n psi kappa tau *
          (halfBudgetK n (BirthPhaseCapToFirstBirth.Q6 n psi kappa tau) *
            BirthPhaseCapToFirstBirth.R6) =
        firstBirthHorizon n psi kappa tau := by
    unfold firstBirthHorizon
    unfold BirthPhaseCapToFirstBirth.massConstant
      BirthPhaseCapToFirstBirth.chargedHorizon
    ac_rfl
  calc
    firstBirthFailureNumerator hpsi h2 ring hclosed6 D hD =
      BirthPhaseGenericRenewal.targetFailureNumerator
        (BirthPhaseCapToFirstBirth.currentStep hpsi h2 ring)
        (BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring)
        (BirthPhaseCapToFirstBirth.B6ReacquireCarrier hpsi h2 ring)
        (BirthPhaseCapToFirstBirth.firstBirthGoodBit hpsi h2 ring)
        hclosed6
        (⟨D, Or.inl hD⟩ : BirthPhaseGenericRenewal.RenewalState
          (BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring)
          (BirthPhaseCapToFirstBirth.B6ReacquireCarrier hpsi h2 ring))
        (halfBudgetK n (BirthPhaseCapToFirstBirth.Q6 n psi kappa tau) *
          BirthPhaseCapToFirstBirth.R6) := rfl
    _ = avoidNumerator
        (fun E u => BirthShortDoneTerminalObserver.NoBirthAlong
          hpsi (by decide : 0 < 2) h2 ring E u) D
        (BirthPhaseCapToFirstBirth.L6 n psi kappa tau *
          (halfBudgetK n (BirthPhaseCapToFirstBirth.Q6 n psi kappa tau) *
            BirthPhaseCapToFirstBirth.R6)) := hraw
    _ = avoidNumerator
        (fun E u => BirthShortDoneTerminalObserver.NoBirthAlong
          hpsi (by decide : 0 < 2) h2 ring E u) D
        (firstBirthHorizon n psi kappa tau) := by rw [hT]
    _ = firstLeaderNoBirthNumerator hpsi h2 ring D
        (firstBirthHorizon n psi kappa tau) :=
      avoidNumerator_noBirth_eq hpsi h2 ring D _


private theorem firstLeaderNoBirthNumerator_le_pow
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (T : Nat) :
    firstLeaderNoBirthNumerator hpsi h2 ring C T <= n ^ T := by
  classical
  unfold firstLeaderNoBirthNumerator
  unfold BirthShortDoneTerminalNoHitCount.noBirthBit
  exact indicator_wordSum_le_pow
    (fun u => BirthShortDoneTerminalObserver.NoBirthAlong
      hpsi (by decide : 0 < 2) h2 ring C u)


private theorem firstLeaderNoBirthNumerator_extension_le
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (T U : Nat) :
    firstLeaderNoBirthNumerator hpsi h2 ring C (T + U) <=
      firstLeaderNoBirthNumerator hpsi h2 ring C T * n ^ U := by
  calc
    firstLeaderNoBirthNumerator hpsi h2 ring C (T + U) =
      avoidNumerator
        (fun D u => BirthShortDoneTerminalObserver.NoBirthAlong
          hpsi (by decide : 0 < 2) h2 ring D u) C (T + U) :=
      (avoidNumerator_noBirth_eq hpsi h2 ring C (T + U)).symm
    _ <= avoidNumerator
        (fun D u => BirthShortDoneTerminalObserver.NoBirthAlong
          hpsi (by decide : 0 < 2) h2 ring D u) C T * n ^ U :=
      avoidNumerator_extension_le
        (BirthPhaseCapToFirstBirth.currentStep hpsi h2 ring)
        (fun D u => BirthShortDoneTerminalObserver.NoBirthAlong
          hpsi (by decide : 0 < 2) h2 ring D u)
        (noBirthAlong_append hpsi h2 ring) C T U
    _ = firstLeaderNoBirthNumerator hpsi h2 ring C T * n ^ U := by
      rw [avoidNumerator_noBirth_eq]


private theorem firstLeaderNoBirthNumerator_succ
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (T : Nat) :
    firstLeaderNoBirthNumerator hpsi h2 ring C (T + 1) =
      (List.ofFn (fun e : Fin n =>
        if BirthShortDoneTerminalObserver.birthEvent
            hpsi (by decide : 0 < 2) h2
            (C e) (C (ring.rightNeighbor e)) = false then
          firstLeaderNoBirthNumerator hpsi h2 ring
            (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) T
        else 0)).sum := by
  classical
  unfold firstLeaderNoBirthNumerator
  rw [FixedSpanRenewalPayload.wordSum_succ]
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro e
  by_cases hb : BirthShortDoneTerminalObserver.birthEvent
      hpsi (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e)) = false
  · rw [if_pos hb]
    apply wordSum_congr_length
    intro u _hu
    unfold BirthShortDoneTerminalNoHitCount.noBirthBit
    simp only [BirthShortDoneTerminalObserver.NoBirthAlong,
      hb, true_and]
    have hstep :
        BirthShortDoneTerminalConsumer.step
            hpsi (by decide : 0 < 2) h2 ring C e =
          BirthPhaseWait2BlockProgress.currentStep2
            hpsi h2 ring C e := by
      rfl
    rw [hstep]
  · rw [if_neg hb]
    calc
      FixedSpanRenewalPayload.wordSum n T
          (fun u =>
            BirthShortDoneTerminalNoHitCount.noBirthBit
              hpsi (by decide : 0 < 2) h2 ring C (e :: u)) =
          FixedSpanRenewalPayload.wordSum n T (fun _ => 0) := by
            apply wordSum_congr_length
            intro u _hu
            unfold BirthShortDoneTerminalNoHitCount.noBirthBit
            simp [BirthShortDoneTerminalObserver.NoBirthAlong, hb]
      _ = 0 := by
        rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun _ => 0)]
        simpa only [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero]

private theorem originalWordSplice_raw
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau)
    (h0 : BirthShortDoneTerminalFirstHit.Leaderless C)
    (hWriter : HWriterAtCap hpsi h2 kappa tau ring)
    (hCapToB6 : HCapToB6 hpsi h2 kappa tau ring)
    (T6 : Nat)
    (h6 : forall (D : FC n psi kappa tau),
      BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring D ->
      2 * n * firstLeaderNoBirthNumerator hpsi h2 ring D T6 <= n ^ T6)
    (T : Nat) :
    2 * n * firstLeaderNoBirthNumerator hpsi h2 ring C (T + T6) <=
      (2 * n * firstCapRawFailureNumerator
        hpsi h2 kappa ring C T) * n ^ T6 +
      n ^ T * n ^ T6 := by
  induction T generalizing C with
  | zero =>
      have hN := firstLeaderNoBirthNumerator_le_pow
        hpsi h2 ring C T6
      have hscaled := Nat.mul_le_mul_left (2 * n) hN
      have hF0 :
          firstCapRawFailureNumerator hpsi h2 kappa ring C 0 = 1 := by
        simp [firstCapRawFailureNumerator, avoidNumerator, NoCapAlong,
          FixedSpanRenewalPayload.wordSum, allSchedules]
      calc
        2 * n * firstLeaderNoBirthNumerator hpsi h2 ring C (0 + T6) =
            2 * n * firstLeaderNoBirthNumerator hpsi h2 ring C T6 := by
              simp
        _ <= 2 * n * n ^ T6 := hscaled
        _ <=
            (2 * n * firstCapRawFailureNumerator
              hpsi h2 kappa ring C 0) * n ^ T6 +
              n ^ 0 * n ^ T6 := by
          rw [hF0]
          simp
  | succ T ih =>
      have hpoint : forall e : Fin n,
          2 * n *
              (if BirthShortDoneTerminalObserver.birthEvent
                    hpsi (by decide : 0 < 2) h2
                    (C e) (C (ring.rightNeighbor e)) = false then
                firstLeaderNoBirthNumerator hpsi h2 ring
                  (BirthPhaseWait2BlockProgress.currentStep2
                    hpsi h2 ring C e) (T + T6)
               else 0) <=
            (2 * n * n ^ T6) *
                (if BirthShortDoneTerminalPassiveR4.RowCap2
                      hpsi h2 kappa ring C e then 0
                 else firstCapRawFailureNumerator hpsi h2 kappa ring
                   (BirthPhaseWait2BlockProgress.currentStep2
                     hpsi h2 ring C e) T) +
              n ^ T * n ^ T6 := by
        intro e
        by_cases hb : BirthShortDoneTerminalObserver.birthEvent
            hpsi (by decide : 0 < 2) h2
            (C e) (C (ring.rightNeighbor e)) = false
        · by_cases hcap : BirthShortDoneTerminalPassiveR4.RowCap2
              hpsi h2 kappa ring C e
          · have hwriter := hWriter C e h0 hcap hb
            have hcarrier := hCapToB6 C e h0 hcap hb hwriter
            let D : FC n psi kappa tau :=
              BirthPhaseCapToFirstBirth.currentStep hpsi h2 ring C e
            have hbase :
                2 * n * firstLeaderNoBirthNumerator
                    hpsi h2 ring D T6 <= n ^ T6 := by
              exact h6 D hcarrier
            have hext := firstLeaderNoBirthNumerator_extension_le
              hpsi h2 ring D T6 T
            have hextScaled := Nat.mul_le_mul_left (2 * n) hext
            have hbaseScaled := Nat.mul_le_mul_right (n ^ T) hbase
            have hcapBound :
                2 * n * firstLeaderNoBirthNumerator
                    hpsi h2 ring D (T + T6) <=
                  n ^ T * n ^ T6 := by
              calc
                2 * n * firstLeaderNoBirthNumerator
                    hpsi h2 ring D (T + T6) =
                    2 * n * firstLeaderNoBirthNumerator
                      hpsi h2 ring D (T6 + T) := by
                        rw [Nat.add_comm T T6]
                _ <= 2 * n *
                    (firstLeaderNoBirthNumerator hpsi h2 ring D T6 *
                      n ^ T) := hextScaled
                _ =
                    (2 * n * firstLeaderNoBirthNumerator
                      hpsi h2 ring D T6) * n ^ T := by
                      ac_rfl
                _ <= n ^ T6 * n ^ T := hbaseScaled
                _ = n ^ T * n ^ T6 := by ac_rfl
            simpa [hb, hcap, D,
              BirthPhaseWait2BlockProgress.currentStep2,
              BirthPhaseCapToFirstBirth.currentStep] using hcapBound
          · have hnext : BirthShortDoneTerminalFirstHit.Leaderless
                (BirthPhaseWait2BlockProgress.currentStep2
                  hpsi h2 ring C e) := by
              simpa [BirthPhaseWait2BlockProgress.currentStep2] using
                (BirthShortDoneTerminalFirstHit.step_leaderless_of_no_birth
                  hpsi (by decide : 0 < 2) h2 ring C e h0 hb)
            have hi := ih
              (C := BirthPhaseWait2BlockProgress.currentStep2
                hpsi h2 ring C e) hnext
            have hi' :
                2 * n * firstLeaderNoBirthNumerator hpsi h2 ring
                    (BirthPhaseWait2BlockProgress.currentStep2
                      hpsi h2 ring C e) (T + T6) <=
                  (2 * n * n ^ T6) *
                      firstCapRawFailureNumerator hpsi h2 kappa ring
                        (BirthPhaseWait2BlockProgress.currentStep2
                          hpsi h2 ring C e) T +
                    n ^ T * n ^ T6 := by
              calc
                2 * n * firstLeaderNoBirthNumerator hpsi h2 ring
                    (BirthPhaseWait2BlockProgress.currentStep2
                      hpsi h2 ring C e) (T + T6) <=
                    (2 * n * firstCapRawFailureNumerator
                      hpsi h2 kappa ring
                      (BirthPhaseWait2BlockProgress.currentStep2
                        hpsi h2 ring C e) T) * n ^ T6 +
                      n ^ T * n ^ T6 := hi
                _ =
                    (2 * n * n ^ T6) *
                      firstCapRawFailureNumerator hpsi h2 kappa ring
                        (BirthPhaseWait2BlockProgress.currentStep2
                          hpsi h2 ring C e) T +
                      n ^ T * n ^ T6 := by
                        ac_rfl
            simpa [hb, hcap] using hi'
        · simp [hb]
      have hsum := FiniteUniformStoppingTree.ofFn_sum_le
        (fun e : Fin n =>
          2 * n *
            (if BirthShortDoneTerminalObserver.birthEvent
                  hpsi (by decide : 0 < 2) h2
                  (C e) (C (ring.rightNeighbor e)) = false then
              firstLeaderNoBirthNumerator hpsi h2 ring
                (BirthPhaseWait2BlockProgress.currentStep2
                  hpsi h2 ring C e) (T + T6)
             else 0))
        (fun e : Fin n =>
          (2 * n * n ^ T6) *
              (if BirthShortDoneTerminalPassiveR4.RowCap2
                    hpsi h2 kappa ring C e then 0
               else firstCapRawFailureNumerator hpsi h2 kappa ring
                 (BirthPhaseWait2BlockProgress.currentStep2
                   hpsi h2 ring C e) T) +
            n ^ T * n ^ T6)
        hpoint
      rw [FiniteUniformStoppingTree.ofFn_sum_mul_left,
        FiniteUniformStoppingTree.ofFn_sum_add,
        FiniteUniformStoppingTree.ofFn_sum_mul_left,
        FiniteUniformStoppingTree.ofFn_sum_const] at hsum
      have hNrec := firstLeaderNoBirthNumerator_succ
        hpsi h2 ring C (T + T6)
      have hFrec := firstCapRawFailureNumerator_succ
        hpsi h2 kappa ring C T
      rw [<- hNrec, <- hFrec] at hsum
      calc
        2 * n * firstLeaderNoBirthNumerator hpsi h2 ring C
            (Nat.succ T + T6) =
            2 * n * firstLeaderNoBirthNumerator hpsi h2 ring C
              (T + T6 + 1) := by
                rw [Nat.succ_add]
        _ <=
            (2 * n * n ^ T6) *
                firstCapRawFailureNumerator hpsi h2 kappa ring C (T + 1) +
              n * (n ^ T * n ^ T6) := hsum
        _ =
            (2 * n * firstCapRawFailureNumerator
              hpsi h2 kappa ring C (T + 1)) * n ^ T6 +
              n ^ (T + 1) * n ^ T6 := by
          rw [Nat.pow_succ]
          ac_rfl


/-- The missing B7 same-original-word seam.  No endpoint is recovered from a
B5 `.success`; the proof stays on the literal raw scheduler word and cuts it at
its first physical cap row. -/
theorem HOriginalWordSplice_proved
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hclosed4 : BirthPhaseWait2BlockProgress.HClosed
      hpsi h2 hn kappa tau ring anchor)
    (C : FC n psi kappa tau)
    (hC : BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor C)
    (hclosed6 : BirthPhaseCapToFirstBirth.hclosed6
      (n := n) (kappa := kappa) (tau := tau) hpsi h2 ring) :
    HOriginalWordSplice hpsi h2 hn kappa tau ring anchor
      hclosed4 C hC hclosed6 := by
  intro h0 hWriter hCapToB6 h6
  have h6raw : forall (D : FC n psi kappa tau),
      BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring D ->
      2 * n * firstLeaderNoBirthNumerator hpsi h2 ring D
          (firstBirthHorizon n psi kappa tau) <=
        n ^ firstBirthHorizon n psi kappa tau := by
    intro D hD
    have hb := h6 D hD
    rw [firstBirthFailureNumerator_eq_noBirth
      hpsi h2 ring hclosed6 D hD] at hb
    exact hb
  have hs := originalWordSplice_raw
    hpsi h2 kappa tau ring C h0 hWriter hCapToB6
    (firstBirthHorizon n psi kappa tau) h6raw
    (firstCapHorizon n kappa)
  have h5 := firstCapFailureNumerator_eq_raw
    hpsi h2 hn kappa tau ring anchor hclosed4 C hC
  rw [<- h5] at hs
  simpa [firstLeaderHorizon] using hs


#print axioms BirthPhaseFirstLeaderComposition.wordSum_horizon_add
#print axioms BirthPhaseFirstLeaderComposition.firstCapFailureNumerator_eq_raw
#print axioms BirthPhaseFirstLeaderComposition.firstBirthFailureNumerator_eq_noBirth
#print axioms BirthPhaseFirstLeaderComposition.HOriginalWordSplice_proved

end BirthPhaseFirstLeaderComposition
