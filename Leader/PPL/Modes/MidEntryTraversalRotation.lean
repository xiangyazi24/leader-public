import Leader.PPL.Modes.MidEntryTraversalPaperEvents
import Init.Data.List.Pairwise
import Init.Data.List.Perm

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/-! ## Rotation of the fixed clockwise sweep -/

private theorem q19778_cyclicOffset_shiftRight_of_lt
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) (hd : d < n) :
    PPL.cyclicOffset ring i (PPL.shiftRight ring i d) = d := by
  unfold PPL.cyclicOffset PPL.shiftRight
  change
    (((i.val + d) % n + n - i.val) % n) = d
  have hi : i.val < n := i.isLt
  by_cases hs : i.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have heq :
        i.val + d + n - i.val = n + d := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt hd]
  · have hge : n <= i.val + d := by
      omega
    have hlt : i.val + d - n < n := by
      omega
    rw [Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt hlt]
    have heq :
        i.val + d - n + n - i.val = d := by
      omega
    rw [heq, Nat.mod_eq_of_lt hd]

private theorem q19778_shiftRight_cyclicOffset
    {n : Nat} (ring : DirectedRing n)
    (a b : Fin n) :
    PPL.shiftRight ring a
        (PPL.cyclicOffset ring a b) = b := by
  apply Fin.ext
  change
    (a.val +
        ((b.val + n - a.val) % n)) % n =
      b.val
  by_cases hab : a.val <= b.val
  · have heq :
        b.val + n - a.val =
          n + (b.val - a.val) := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt
        (by omega : b.val - a.val < n)]
    have hsum :
        a.val + (b.val - a.val) = b.val := by
      omega
    rw [hsum, Nat.mod_eq_of_lt b.isLt]
  · have hlt :
        b.val + n - a.val < n := by
      omega
    rw [Nat.mod_eq_of_lt hlt]
    have hsum :
        a.val + (b.val + n - a.val) =
          b.val + n := by
      omega
    rw [hsum, Nat.add_mod_right,
      Nat.mod_eq_of_lt b.isLt]

/-- Minimal core-Lean replacement for Mathlib's `Q19778Perm n`. -/
structure Q19778Perm (n : Nat) where
  toFun : Fin n -> Fin n
  invFun : Fin n -> Fin n
  left_inv : ∀ i, invFun (toFun i) = i
  right_inv : ∀ e, toFun (invFun e) = e

instance {n : Nat} : CoeFun (Q19778Perm n) (fun _ => Fin n -> Fin n) :=
  ⟨Q19778Perm.toFun⟩

def Q19778Perm.symm {n : Nat} (σ : Q19778Perm n) : Q19778Perm n :=
  ⟨σ.invFun, σ.toFun, σ.right_inv, σ.left_inv⟩

@[simp] theorem Q19778Perm.symm_apply_apply {n : Nat} (σ : Q19778Perm n) (i : Fin n) :
    σ.symm (σ i) = i := σ.left_inv i

@[simp] theorem Q19778Perm.apply_symm_apply {n : Nat} (σ : Q19778Perm n) (e : Fin n) :
    σ (σ.symm e) = e := σ.right_inv e

theorem Q19778Perm.injective {n : Nat} (σ : Q19778Perm n) :
    Function.Injective (fun i => σ i) := by
  intro a b h
  have := congrArg σ.symm h
  simpa using this

private def q19778RotationEquiv
    {n : Nat} (ring : DirectedRing n)
    (start : Fin n) : Q19778Perm n where
  toFun i := PPL.shiftRight ring start i.val
  invFun e :=
    ⟨PPL.cyclicOffset ring start e,
      by
        unfold PPL.cyclicOffset
        exact Nat.mod_lt _ ring.hn⟩
  left_inv i := by
    apply Fin.ext
    exact
      q19778_cyclicOffset_shiftRight_of_lt
        ring start i.val i.isLt
  right_inv e :=
    q19778_shiftRight_cyclicOffset
      ring start e

private theorem q19778_sublist_map
    {A B : Type} (f : A -> B)
    {xs ys : List A}
    (h : xs.Sublist ys) :
    (xs.map f).Sublist (ys.map f) := by
  induction h with
  | slnil =>
      exact List.Sublist.slnil
  | cons a h ih =>
      exact List.Sublist.cons (f a) ih
  | cons_cons a h ih =>
      exact List.Sublist.cons_cons (f a) ih

private theorem q19778_clockwise_map_rotation
    {n : Nat} (ring : DirectedRing n)
    (start : Fin n) :
    (lemma5ClockwiseSweepWord n).map
        (q19778RotationEquiv ring start) =
      PPL.seqR ring start n := by
  unfold lemma5ClockwiseSweepWord PPL.seqR
  rw [List.map_ofFn]
  rfl

private theorem q19778_rotated_sublist_iff
    {n : Nat} (ring : DirectedRing n)
    (start : Fin n) (schedule : DetSchedule n) :
    (PPL.seqR ring start n).Sublist schedule ↔
      (lemma5ClockwiseSweepWord n).Sublist
        (schedule.map
          (q19778RotationEquiv ring start).symm) := by
  let σ := q19778RotationEquiv ring start
  constructor
  · intro h
    have hm :=
      q19778_sublist_map σ.symm h
    have hword :
        (PPL.seqR ring start n).map σ.symm =
          lemma5ClockwiseSweepWord n := by
      rw [← q19778_clockwise_map_rotation
        ring start]
      simp [σ, List.map_map, Function.comp_def]
    rw [hword] at hm
    exact hm
  · intro h
    have hm :=
      q19778_sublist_map σ h
    rw [q19778_clockwise_map_rotation
      ring start] at hm
    simpa [σ, List.map_map, Function.comp_def]
      using hm

private theorem q19778_nodup_ofFn_of_injective
    {A : Type} {n : Nat} (f : Fin n -> A)
    (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hm
        rw [List.mem_ofFn] at hm
        obtain ⟨i, hi⟩ := hm
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

private theorem q19778_ofFn_equiv_perm
    {n : Nat} (σ : Q19778Perm n) :
    (List.ofFn (fun i : Fin n => σ i)).Perm
      (List.ofFn (fun i : Fin n => i)) := by
  have hl :
      (List.ofFn (fun i : Fin n => σ i)).Nodup :=
    q19778_nodup_ofFn_of_injective
      (fun i : Fin n => σ i) σ.injective
  have hr :
      (List.ofFn (fun i : Fin n => i)).Nodup :=
    q19778_nodup_ofFn_of_injective
      (fun i : Fin n => i)
      (by
        intro i j h
        exact h)
  apply (List.perm_ext_iff_of_nodup hl hr).2
  intro x
  simp only [List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨σ i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨σ.symm i, by simp⟩

private theorem q19778_ofFn_sum_comp_equiv
    {n : Nat} (σ : Q19778Perm n)
    (g : Fin n -> Nat) :
    (List.ofFn (fun i => g (σ i))).sum =
      (List.ofFn g).sum := by
  have hp :=
    (q19778_ofFn_equiv_perm σ).map g
  have hs := List.Perm.sum_nat hp
  simpa [List.map_ofFn, Function.comp_def]
    using hs

private theorem q19778_sum_map_flatMap
    {A B : Type} (xs : List A)
    (children : A -> List B)
    (value : B -> Nat) :
    ((xs.flatMap children).map value).sum =
      (xs.map
        (fun x =>
          ((children x).map value).sum)).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, List.sum_append]

private theorem q19778_allSchedules_sum_relabel
    {n : Nat} (σ : Q19778Perm n)
    (H : Nat) (f : DetSchedule n -> Nat) :
    ((allSchedules n H).map
      (fun word => f (word.map σ))).sum =
      ((allSchedules n H).map f).sum := by
  induction H generalizing f with
  | zero =>
      simp [allSchedules]
  | succ H ih =>
      rw [allSchedules,
        q19778_sum_map_flatMap,
        q19778_sum_map_flatMap]
      change
        ((allSchedules n H).map
          (fun pre =>
            ((List.ofFn
              (fun e : Fin n =>
                pre ++ [e])).map
              (fun word =>
                f (word.map σ))).sum)).sum =
        ((allSchedules n H).map
          (fun pre =>
            ((List.ofFn
              (fun e : Fin n =>
                pre ++ [e])).map f).sum)).sum
      let g : DetSchedule n -> Nat :=
        fun pre =>
          ((List.ofFn
            (fun e : Fin n =>
              pre ++ [e])).map f).sum
      have hinner :
          ∀ pre : DetSchedule n,
            ((List.ofFn
              (fun e : Fin n =>
                pre ++ [e])).map
              (fun word =>
                f (word.map σ))).sum =
              g (pre.map σ) := by
        intro pre
        have hp :=
          q19778_ofFn_sum_comp_equiv
            σ
            (fun e : Fin n =>
              f (pre.map σ ++ [e]))
        simpa [g, List.map_ofFn,
          List.map_append, Function.comp_def]
          using hp
      calc
        ((allSchedules n H).map
          (fun pre =>
            ((List.ofFn
              (fun e : Fin n =>
                pre ++ [e])).map
              (fun word =>
                f (word.map σ))).sum)).sum =
          ((allSchedules n H).map
            (fun pre =>
              g (pre.map σ))).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro pre _hpre
            exact hinner pre
        _ =
          ((allSchedules n H).map g).sum :=
            ih g
        _ =
          ((allSchedules n H).map
            (fun pre =>
              ((List.ofFn
                (fun e : Fin n =>
                  pre ++ [e])).map f).sum)).sum := by
            rfl

private theorem q19778_countP_eq_sum_indicator
    {A : Type} (xs : List A)
    (p : A -> Bool) :
    xs.countP p =
      (xs.map
        (fun x =>
          if p x then 1 else 0)).sum := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.countP_cons,
        List.map_cons, List.sum_cons]
      cases hp : p x <;>
        (simp [ih]; try omega)

private theorem q19778_allSchedules_countP_relabel
    {n : Nat} (σ : Q19778Perm n)
    (H : Nat) (p : DetSchedule n -> Bool) :
    (allSchedules n H).countP
        (fun word => p (word.map σ)) =
      (allSchedules n H).countP p := by
  rw [q19778_countP_eq_sum_indicator,
    q19778_countP_eq_sum_indicator]
  exact
    q19778_allSchedules_sum_relabel
      σ H
      (fun word =>
        if p word then 1 else 0)

/--
Exact scheduler-count rotation.  The alphabet equivalence sends canonical
letter i to the edge i places clockwise from start, and therefore sends the
canonical sweep word to PPL.seqR ring start n.
-/
theorem lemma5iRotatedSweepMissCount_eq_fixedWordMissCount
    {n : Nat} (ring : DirectedRing n)
    (start : Fin n) (H : Nat) :
    (allSchedules n H).countP
        (q19765RotatedMiss ring start) =
      fixedWordMissCount
        (lemma5ClockwiseSweepWord n) H := by
  let σ := q19778RotationEquiv ring start
  let p : DetSchedule n -> Bool :=
    fun schedule =>
      decide
        (Not
          ((lemma5ClockwiseSweepWord n).Sublist
            schedule))
  have hpred :
      q19765RotatedMiss ring start =
        (fun schedule =>
          p (schedule.map σ.symm)) := by
    funext schedule
    apply Bool.eq_iff_iff.mpr
    simp only [q19765RotatedMiss, p,
      decide_eq_true_eq]
    exact
      not_congr
        (q19778_rotated_sublist_iff
          ring start schedule)
  rw [hpred]
  change
    (allSchedules n H).countP
        (fun schedule =>
          p (schedule.map σ.symm)) =
      (allSchedules n H).countP p
  exact
    q19778_allSchedules_countP_relabel
      σ.symm H p

/-! ## Corrected BC projection: hnpow is part of the interface -/

def Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBCCorrected :
    Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (D : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    maxResetSignalB D = true ->
    ∃ host : List (Fin n) -> Fin n,
      ∃ stop : List (Fin n) -> Bool,
        ∃ h : Nat,
          h <= psi ∧
          (allSchedules n
              (lemma5SweepHorizon n)).countP
            (fun suffix =>
              !allClockResetsSeenB ring D
                (suffix.take
                  (lemma5PaperSweepHorizon n))) <=
            n ^ (2 * n * n) *
              (fixedWordMissCount
                  (lemma5ClockwiseSweepWord n)
                  (lemma5PaperSweepHorizon n) +
                lemma5iTraversalEncounterFailureCountBC
                  ring host stop +
                lemma5iTraversalTTLFailureCountBC
                  psi h ring host stop)

private theorem q19778CountP_mono_on
    {A : Type}
    (xs : List A)
    (p q : A -> Bool)
    (hpq :
      ∀ x,
        x ∈ xs ->
        p x = true ->
        q x = true) :
    xs.countP p <= xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons,
        List.countP_cons]
      have htail :
          xs.countP p <= xs.countP q :=
        ih
          (fun y hy hpy =>
            hpq y (by simp [hy]) hpy)
      cases hp : p x with
      | false =>
          cases hq : q x <;>
            simp [hp, hq] <;>
            omega
      | true =>
          have hqx : q x = true :=
            hpq x (by simp) hp
          simp [hp, hqx]
          omega

private theorem q19778CountP_or_le_add
    {A : Type}
    (xs : List A)
    (p q : A -> Bool) :
    xs.countP
        (fun x => p x || q x) <=
      xs.countP p + xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons,
        List.countP_cons,
        List.countP_cons]
      cases hp : p x <;>
        cases hq : q x <;>
        simp [hp, hq] at * <;>
        omega

private theorem q19778AllSchedules_add
    (n a b : Nat) :
    allSchedules n (a + b) =
      (allSchedules n a).flatMap
        (fun pre =>
          (allSchedules n b).map
            (fun suf => pre ++ suf)) := by
  induction b with
  | zero =>
      simp [allSchedules]
  | succ b ih =>
      rw [Nat.add_succ, allSchedules, ih]
      simp only [allSchedules,
        List.flatMap_assoc,
        List.map_flatMap,
        List.flatMap_map]
      congr
      funext pre
      congr
      funext suf
      rw [List.map_ofFn]
      congr 1
      funext e
      simp [List.append_assoc]

private theorem q19778SumIfCount
    {A : Type}
    (xs : List A)
    (p : A -> Bool)
    (c : Nat) :
    (xs.map
      (fun x =>
        if p x then c else 0)).sum =
      xs.countP p * c := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons,
        List.sum_cons,
        List.countP_cons]
      cases hp : p x <;>
        simp [hp, ih, Nat.succ_mul,
          Nat.add_comm]

private theorem q19778CountP_take_pad
    {n H P : Nat}
    (p : DetSchedule n -> Bool) :
    (allSchedules n (H + P)).countP
        (fun word => p (word.take H)) =
      (allSchedules n H).countP p *
        n ^ P := by
  rw [q19778AllSchedules_add,
    List.countP_flatMap]
  simp only [Function.comp_def]
  have hmap :
      ((allSchedules n H).map
        (fun pre =>
          ((allSchedules n P).map
            (fun pad => pre ++ pad)).countP
              (fun word =>
                p (word.take H)))) =
      (allSchedules n H).map
        (fun pre =>
          if p pre then n ^ P else 0) := by
    apply List.map_congr_left
    intro pre hpre
    rw [List.countP_map]
    simp only [Function.comp_def]
    have hlen :=
      allSchedules_schedule_length
        n H pre hpre
    have hfun :
        (fun pad : DetSchedule n =>
          p ((pre ++ pad).take H)) =
        (fun _ : DetSchedule n =>
          p pre) := by
      funext pad
      rw [← hlen, List.take_append_length]
    rw [hfun]
    cases hp : p pre <;>
      simp [hp, allSchedules_length]
  rw [hmap]
  exact
    q19778SumIfCount
      (allSchedules n H)
      p (n ^ P)

/--
The requested old projection cannot be recovered globally because its
statement omits hnpow.  This is the exact corrected replacement.
-/
theorem
    lemma5iRetimedTraversalCurrentMaxSuffixProjectionBC_of_corrected
    (hABC :
      Lemma5iRetimedTraversalABCSweepResidualCorrected) :
    Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBCCorrected := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring D hlineage hmax

  let start :=
    q19765MaxSignalSite ring D
  let host :=
    q19765TraversalHost ring D
  let stop :=
    q19765TraversalStopB ring D
  let h :=
    (D start).hits.val

  have hraw :=
    hABC hn3 hpsi hkappa hnpow
      ring D hlineage hmax
  change
    (D start).signalR.val = kappa ∧
      h <= psi ∧
      ∀ sweep : DetSchedule n,
        sweep ∈
            allSchedules n
              (lemma5PaperSweepHorizon n) ->
        !allClockResetsSeenB ring D sweep =
            true ->
        ((q19765RotatedMiss
              ring start sweep ||
            q19765EncounterBad
              ring host stop sweep) ||
          q19765TTLBad
            psi h ring host stop sweep) =
            true
    at hraw

  refine
    ⟨host, stop, h, hraw.2.1, ?_⟩

  let P : Nat :=
    lemma5PaperSweepHorizon n
  let Z : Nat :=
    2 * n * n
  let S : Nat :=
    lemma5SweepHorizon n

  let badP : DetSchedule n -> Bool :=
    fun sweep =>
      !allClockResetsSeenB ring D sweep
  let qA : DetSchedule n -> Bool :=
    q19765RotatedMiss ring start
  let qB : DetSchedule n -> Bool :=
    q19765EncounterBad ring host stop
  let qC : DetSchedule n -> Bool :=
    q19765TTLBad psi h ring host stop
  let qAB : DetSchedule n -> Bool :=
    fun sweep =>
      qA sweep || qB sweep

  have hmono :
      (allSchedules n P).countP badP <=
        (allSchedules n P).countP
          (fun sweep =>
            qAB sweep || qC sweep) := by
    apply
      q19778CountP_mono_on
        (allSchedules n P)
        badP
        (fun sweep =>
          qAB sweep || qC sweep)
    intro sweep hsweep hbad
    dsimp [badP, qAB, qA, qB, qC]
    exact
      hraw.2.2 sweep
        (by simpa [P] using hsweep)
        (by simpa [badP] using hbad)

  have hab :=
    q19778CountP_or_le_add
      (allSchedules n P) qA qB
  have habc :=
    q19778CountP_or_le_add
      (allSchedules n P) qAB qC

  have hAeq :
      (allSchedules n P).countP qA =
        fixedWordMissCount
          (lemma5ClockwiseSweepWord n) P := by
    simpa [qA] using
      lemma5iRotatedSweepMissCount_eq_fixedWordMissCount
        ring start P

  have hBeq :
      (allSchedules n P).countP qB =
        lemma5iTraversalEncounterFailureCountBC
          ring host stop := by
    rfl

  have hCeq :
      (allSchedules n P).countP qC =
        lemma5iTraversalTTLFailureCountBC
          psi h ring host stop := by
    rfl

  have hpaper :
      (allSchedules n P).countP badP <=
        fixedWordMissCount
            (lemma5ClockwiseSweepWord n) P +
          lemma5iTraversalEncounterFailureCountBC
            ring host stop +
          lemma5iTraversalTTLFailureCountBC
            psi h ring host stop := by
    calc
      (allSchedules n P).countP badP <=
          (allSchedules n P).countP
            (fun sweep =>
              qAB sweep || qC sweep) :=
        hmono
      _ <=
          (allSchedules n P).countP qAB +
            (allSchedules n P).countP qC :=
        habc
      _ <=
          ((allSchedules n P).countP qA +
            (allSchedules n P).countP qB) +
              (allSchedules n P).countP qC :=
        Nat.add_le_add_right hab _
      _ =
          fixedWordMissCount
              (lemma5ClockwiseSweepWord n) P +
            lemma5iTraversalEncounterFailureCountBC
              ring host stop +
            lemma5iTraversalTTLFailureCountBC
              psi h ring host stop := by
        rw [hAeq, hBeq, hCeq]

  have hpad0 :=
    q19778CountP_take_pad
      (n := n) (H := P) (P := Z) badP

  have hPS : P + Z = S := by
    dsimp [P, Z, S]
    exact lemma5iRetimedLastArmPadding n

  have hpad :
      (allSchedules n S).countP
          (fun suffix =>
            badP (suffix.take P)) =
        (allSchedules n P).countP badP *
          n ^ Z := by
    rw [← hPS]
    exact hpad0

  have hfinal :
      (allSchedules n S).countP
          (fun suffix =>
            badP (suffix.take P)) <=
        n ^ Z *
          (fixedWordMissCount
              (lemma5ClockwiseSweepWord n) P +
            lemma5iTraversalEncounterFailureCountBC
              ring host stop +
            lemma5iTraversalTTLFailureCountBC
              psi h ring host stop) := by
    rw [hpad]
    calc
      (allSchedules n P).countP badP *
          n ^ Z <=
        (fixedWordMissCount
              (lemma5ClockwiseSweepWord n) P +
            lemma5iTraversalEncounterFailureCountBC
              ring host stop +
            lemma5iTraversalTTLFailureCountBC
              psi h ring host stop) *
          n ^ Z :=
        Nat.mul_le_mul_right
          (n ^ Z) hpaper
      _ =
        n ^ Z *
          (fixedWordMissCount
              (lemma5ClockwiseSweepWord n) P +
            lemma5iTraversalEncounterFailureCountBC
              ring host stop +
            lemma5iTraversalTTLFailureCountBC
              psi h ring host stop) := by
        ac_rfl

  simpa [P, Z, S, badP] using hfinal

/-! ## Apply the existing A+B+C budget with the corrected projection -/

theorem
    lemma5iRetimedTraversalCurrentMaxSuffixBC_budget_corrected
    (hprojection :
      Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBCCorrected) :
    ∀ {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (D : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    maxResetSignalB D = true ->
    n *
        (allSchedules n
          (lemma5SweepHorizon n)).countP
          (fun suffix =>
            !allClockResetsSeenB ring D
              (suffix.take
                (lemma5PaperSweepHorizon n))) <=
      n ^ lemma5SweepHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring D hlineage
  intro hmarked hpredict hoffset hlottery
  intro hmax

  obtain
      ⟨host, stop, h, hh, hraw⟩ :=
    hprojection
      hn3 hpsi hkappa hnpow
      ring D hlineage hmax

  let P : Nat :=
    lemma5PaperSweepHorizon n
  let Z : Nat :=
    2 * n * n
  let S : Nat :=
    lemma5SweepHorizon n

  let A : Nat :=
    fixedWordMissCount
      (lemma5ClockwiseSweepWord n) P
  let B : Nat :=
    lemma5iTraversalEncounterFailureCountBC
      ring host stop
  let C : Nat :=
    lemma5iTraversalTTLFailureCountBC
      psi h ring host stop

  have hproj :
      (allSchedules n S).countP
          (fun suffix =>
            !allClockResetsSeenB ring D
              (suffix.take P)) <=
        n ^ Z * (A + B + C) := by
    simpa [P, Z, S, A, B, C]
      using hraw

  have hpaper :
      n * (A + B + C) <=
        n ^ P := by
    simpa [A, B, C, P] using
      lemma5iTraversalABC_paperBudgetBC
        hn3 hpsi hnpow
        ring host stop h hh
        hmarked hpredict
        hoffset hlottery

  have hPS :
      P + Z = S := by
    dsimp [P, Z, S]
    exact lemma5iRetimedLastArmPadding n

  have hfinal :
      n *
          (allSchedules n S).countP
            (fun suffix =>
              !allClockResetsSeenB ring D
                (suffix.take P)) <=
        n ^ S := by
    calc
      n *
          (allSchedules n S).countP
            (fun suffix =>
              !allClockResetsSeenB ring D
                (suffix.take P)) <=
        n * (n ^ Z * (A + B + C)) :=
        Nat.mul_le_mul_left n hproj
      _ =
        n ^ Z * (n * (A + B + C)) := by
        ac_rfl
      _ <=
        n ^ Z * n ^ P :=
        Nat.mul_le_mul_left
          (n ^ Z) hpaper
      _ =
        n ^ (Z + P) := by
        rw [Nat.pow_add]
      _ =
        n ^ S := by
        congr 1
        omega

  simpa [P, S] using hfinal

/-! ## First-terminal bind with hnpow threaded through -/

private def q19778RetimedTraversalBadAux
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    Config n psi kappa ->
      Nat -> DetSchedule n -> Bool
  | C, 0, word =>
      if maxResetSignalB C then
        !allClockResetsSeenB ring C
          (word.take
            (lemma5PaperSweepHorizon n))
      else
        false
  | C, fuel + 1, [] =>
      if maxResetSignalB C then
        !allClockResetsSeenB ring C []
      else
        false
  | C, fuel + 1, e :: rest =>
      if maxResetSignalB C then
        !allClockResetsSeenB ring C
          ((e :: rest).take
            (lemma5PaperSweepHorizon n))
      else
        q19778RetimedTraversalBadAux
          ring
          (pplStep ring C e)
          fuel rest

private theorem q19778TraversalBadB_fun_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    lemma5iRetimedTraversalBadB ring C =
      q19778RetimedTraversalBadAux
        ring C (lemma5ArmHorizon n) := by
  funext word
  unfold lemma5iRetimedTraversalBadB
  generalize lemma5ArmHorizon n = fuel
  induction fuel generalizing C word with
  | zero =>
      unfoldRetimedTraversalAux
      unfold q19778RetimedTraversalBadAux
      rfl
  | succ fuel ih =>
      cases word with
      | nil =>
          unfoldRetimedTraversalAux
          unfold q19778RetimedTraversalBadAux
          rfl
      | cons e rest =>
          unfoldRetimedTraversalAux
          unfold q19778RetimedTraversalBadAux
          by_cases hm :
              maxResetSignalB C = true
          · simp only
              [hm, if_true, ite_true]
          · simp only
              [hm, if_false, ite_false,
                Bool.false_eq_true]
            exact ih _ _

private theorem q19778TraversalAux_eq_currentMax
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (fuel : Nat)
    (word : DetSchedule n)
    (hm : maxResetSignalB C = true) :
    q19778RetimedTraversalBadAux
        ring C fuel word =
      !allClockResetsSeenB ring C
        (word.take
          (lemma5PaperSweepHorizon n)) := by
  cases fuel with
  | zero =>
      simp [q19778RetimedTraversalBadAux, hm]
  | succ fuel =>
      cases word <;>
        simp [q19778RetimedTraversalBadAux, hm]

private theorem q19778SumMapLe
    {A : Type}
    (xs : List A)
    (f g : A -> Nat)
    (hfg :
      ∀ x,
        x ∈ xs ->
        f x <= g x) :
    (xs.map f).sum <=
      (xs.map g).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons]
      exact
        Nat.add_le_add
          (hfg x (by simp))
          (ih
            (fun y hy =>
              hfg y (by simp [hy])))

private theorem q19778SumMapConst
    {A : Type}
    (xs : List A)
    (c : Nat) :
    (xs.map (fun _ => c)).sum =
      xs.length * c := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.succ_mul, Nat.add_comm]

private theorem q19778SumMapMulLeft
    {A : Type}
    (xs : List A)
    (f : A -> Nat)
    (c : Nat) :
    c * (xs.map f).sum =
      (xs.map
        (fun x => c * f x)).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.mul_add]

private theorem q19778CountP_prefixInvariant
    {n H P : Nat}
    (p : DetSchedule n -> Bool)
    (hinv :
      ∀ sweep : DetSchedule n,
        sweep.length = H ->
        ∀ pad : DetSchedule n,
          p (sweep ++ pad) = p sweep) :
    (allSchedules n (H + P)).countP p =
      (allSchedules n H).countP p *
        n ^ P := by
  rw [q19778AllSchedules_add,
    List.countP_flatMap]
  simp only [Function.comp_def]
  have hmap :
      ((allSchedules n H).map
        (fun sweep =>
          ((allSchedules n P).map
            (fun pad => sweep ++ pad)).countP p)) =
      (allSchedules n H).map
        (fun sweep =>
          if p sweep then n ^ P else 0) := by
    apply List.map_congr_left
    intro sweep hsweep
    rw [List.countP_map]
    simp only [Function.comp_def]
    have hlen :=
      allSchedules_schedule_length
        n H sweep hsweep
    have hfun :
        (fun pad : DetSchedule n =>
          p (sweep ++ pad)) =
        (fun _ : DetSchedule n =>
          p sweep) := by
      funext pad
      exact hinv sweep hlen pad
    rw [hfun]
    cases hp : p sweep <;>
      simp [hp, allSchedules_length]
  rw [hmap]
  exact
    q19778SumIfCount
      (allSchedules n H)
      p (n ^ P)

private theorem q19778Paper_le_sweep
    (n : Nat) :
    lemma5PaperSweepHorizon n <=
      lemma5SweepHorizon n := by
  have h :=
    lemma5iRetimedLastArmPadding n
  omega

private theorem q19778TraversalCurrent_padding
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (sweep pad : DetSchedule n)
    (hlen :
      sweep.length =
        lemma5SweepHorizon n) :
    (!allClockResetsSeenB ring D
        ((sweep ++ pad).take
          (lemma5PaperSweepHorizon n))) =
      (!allClockResetsSeenB ring D
        (sweep.take
          (lemma5PaperSweepHorizon n))) := by
  have hle :
      lemma5PaperSweepHorizon n <=
        sweep.length := by
    rw [hlen]
    exact q19778Paper_le_sweep n
  rw [List.take_append_of_le_length hle]

private theorem q19778TraversalAuxCount
    (hprojection :
      Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBCCorrected) :
    ∀ {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (hlineage :
        SignalLineageOwnership
          (psi := psi) (kappa := kappa) ring)
      (hmarked : ModeStoppedTreeTransfer)
      (hpredict : PredictableHostTails)
      (hoffset : WLGHeadOffsetBounds)
      (hlottery : LotteryCountBounds)
      (fuel : Nat)
      (C : Config n psi kappa),
    n *
        (allSchedules n
          (lemma5SweepHorizon n + fuel)).countP
          (q19778RetimedTraversalBadAux
            ring C fuel) <=
      n ^ fuel *
        n ^ lemma5SweepHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring hlineage
  intro hmarked hpredict hoffset hlottery
  intro fuel
  induction fuel with
  | zero =>
      intro C
      cases hm :
          maxResetSignalB C with
      | false =>
          simp [q19778RetimedTraversalBadAux, hm]
      | true =>
          have hfun :
              q19778RetimedTraversalBadAux
                  ring C 0 =
                (fun word =>
                  !allClockResetsSeenB ring C
                    (word.take
                      (lemma5PaperSweepHorizon n))) := by
            funext word
            exact
              q19778TraversalAux_eq_currentMax
                ring C 0 word hm
          rw [hfun, Nat.add_zero,
            Nat.pow_zero, Nat.one_mul]
          exact
            lemma5iRetimedTraversalCurrentMaxSuffixBC_budget_corrected
              hprojection
              hn3 hpsi hkappa hnpow
              ring C hlineage
              hmarked hpredict hoffset hlottery
              hm
  | succ fuel ih =>
      intro C
      cases hm :
          maxResetSignalB C with
      | true =>
          let p : DetSchedule n -> Bool :=
            fun word =>
              !allClockResetsSeenB ring C
                (word.take
                  (lemma5PaperSweepHorizon n))
          have hfun :
              q19778RetimedTraversalBadAux
                  ring C (fuel + 1) =
                p := by
            funext word
            dsimp [p]
            exact
              q19778TraversalAux_eq_currentMax
                ring C (fuel + 1)
                word hm
          rw [hfun]
          have hpad :=
            q19778CountP_prefixInvariant
              (n := n)
              (H := lemma5SweepHorizon n)
              (P := fuel + 1)
              p
              (by
                intro sweep hsweep pad
                dsimp [p]
                exact
                  q19778TraversalCurrent_padding
                    ring C sweep pad hsweep)
          rw [hpad]
          have hcur :=
            lemma5iRetimedTraversalCurrentMaxSuffixBC_budget_corrected
              hprojection
              hn3 hpsi hkappa hnpow
              ring C hlineage
              hmarked hpredict hoffset hlottery
              hm
          change
            n *
                ((allSchedules n
                    (lemma5SweepHorizon n)).countP p *
                  n ^ (fuel + 1)) <=
              n ^ (fuel + 1) *
                n ^ lemma5SweepHorizon n
          calc
            n *
                ((allSchedules n
                    (lemma5SweepHorizon n)).countP p *
                  n ^ (fuel + 1)) =
              n ^ (fuel + 1) *
                (n *
                  (allSchedules n
                    (lemma5SweepHorizon n)).countP p) := by
              ac_rfl
            _ <=
              n ^ (fuel + 1) *
                n ^ lemma5SweepHorizon n :=
              Nat.mul_le_mul_left
                (n ^ (fuel + 1))
                (by
                  simpa [p] using hcur)
      | false =>
          let B : Nat :=
            n ^ fuel *
              n ^ lemma5SweepHorizon n
          let childCount :
              DetSchedule n -> Nat :=
            fun pre =>
              ((allSchedules n
                  (lemma5SweepHorizon n + fuel)).map
                (fun suf => pre ++ suf)).countP
                (q19778RetimedTraversalBadAux
                  ring C (fuel + 1))

          have hpoint :
              ∀ pre : DetSchedule n,
                pre ∈ allSchedules n 1 ->
                n * childCount pre <= B := by
            intro pre hpre
            have hlen :=
              allSchedules_schedule_length
                n 1 pre hpre
            cases pre with
            | nil =>
                simp at hlen
            | cons e rest =>
                cases rest with
                | nil =>
                    dsimp [childCount]
                    rw [List.countP_map]
                    simpa [Function.comp_def,
                      q19778RetimedTraversalBadAux,
                      hm, B]
                      using
                        ih (pplStep ring C e)
                | cons e2 rest2 =>
                    simp at hlen

          have hdecomp :
              (allSchedules n
                  (lemma5SweepHorizon n +
                    (fuel + 1))).countP
                  (q19778RetimedTraversalBadAux
                    ring C (fuel + 1)) =
                ((allSchedules n 1).map
                  childCount).sum := by
            rw [show
                lemma5SweepHorizon n +
                    (fuel + 1) =
                  1 +
                    (lemma5SweepHorizon n +
                      fuel) by omega,
              q19778AllSchedules_add,
              List.countP_flatMap]
            rfl

          calc
            n *
                (allSchedules n
                  (lemma5SweepHorizon n +
                    (fuel + 1))).countP
                  (q19778RetimedTraversalBadAux
                    ring C (fuel + 1)) =
              n *
                ((allSchedules n 1).map
                  childCount).sum := by
              rw [hdecomp]
            _ =
              ((allSchedules n 1).map
                (fun pre =>
                  n * childCount pre)).sum :=
              q19778SumMapMulLeft
                (allSchedules n 1)
                childCount n
            _ <=
              ((allSchedules n 1).map
                (fun _ => B)).sum :=
              q19778SumMapLe
                (allSchedules n 1)
                (fun pre =>
                  n * childCount pre)
                (fun _ => B)
                hpoint
            _ =
              (allSchedules n 1).length * B :=
              q19778SumMapConst
                (allSchedules n 1) B
            _ = n * B := by
              rw [allSchedules_length]
              simp
            _ =
              n ^ (fuel + 1) *
                n ^ lemma5SweepHorizon n := by
              dsimp [B]
              rw [Nat.pow_succ]
              ac_rfl

private theorem q19778Horizon_comm
    (n : Nat) :
    lemma5iHorizon n =
      lemma5SweepHorizon n +
        lemma5ArmHorizon n := by
  unfold lemma5iHorizon
  omega

private theorem
    lemma5iRetimedTraversalCount_of_currentMaxBC_corrected_strong
    (hprojection :
      Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBCCorrected) :
    ∀ {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    n *
        lemma5iRetimedTraversalFailureCount
          ring C <=
      n ^ lemma5iHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C hlineage
  intro hmarked hpredict hoffset hlottery

  have haux :=
    q19778TraversalAuxCount
      hprojection
      hn3 hpsi hkappa hnpow
      ring hlineage
      hmarked hpredict hoffset hlottery
      (lemma5ArmHorizon n) C

  unfold lemma5iRetimedTraversalFailureCount
  rw [q19778Horizon_comm]
  rw [q19778TraversalBadB_fun_eq]

  calc
    n *
        (allSchedules n
          (lemma5SweepHorizon n +
            lemma5ArmHorizon n)).countP
          (q19778RetimedTraversalBadAux
            ring C
            (lemma5ArmHorizon n)) <=
      n ^ lemma5ArmHorizon n *
        n ^ lemma5SweepHorizon n :=
      haux
    _ =
      n ^
        (lemma5ArmHorizon n +
          lemma5SweepHorizon n) := by
      rw [Nat.pow_add]
    _ =
      n ^
        (lemma5SweepHorizon n +
          lemma5ArmHorizon n) := by
      rw [Nat.add_comm]

/--
Direct corrected-residual replacement for the conclusion of
lemma5iSweepMidCountRetimed_traversal_of_currentMaxBC.
-/
theorem
    lemma5iSweepMidCountRetimed_traversal_of_currentMaxBC_of_corrected
    (hABC :
      Lemma5iRetimedTraversalABCSweepResidualCorrected) :
    ∀ {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    neverLeaderless ring C ->
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    StoppedClockSuffixBoundsCorrected ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    n *
        lemma5iRetimedTraversalFailureCount
          ring C <=
      2 * n ^ lemma5iHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C
  intro _hcnz hlineage _hclock
  intro hmarked hpredict hoffset hlottery

  have hprojection :
      Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBCCorrected :=
    lemma5iRetimedTraversalCurrentMaxSuffixProjectionBC_of_corrected
      hABC

  have hstrong :=
    lemma5iRetimedTraversalCount_of_currentMaxBC_corrected_strong
      hprojection
      hn3 hpsi hkappa hnpow
      ring C hlineage
      hmarked hpredict hoffset hlottery

  exact
    Nat.le_trans hstrong
      (by omega)

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iRotatedSweepMissCount_eq_fixedWordMissCount
#print axioms PPL.Modes.Lemma5.lemma5iRetimedTraversalCurrentMaxSuffixProjectionBC_of_corrected
#print axioms PPL.Modes.Lemma5.lemma5iRetimedTraversalCurrentMaxSuffixBC_budget_corrected
#print axioms PPL.Modes.Lemma5.lemma5iSweepMidCountRetimed_traversal_of_currentMaxBC_of_corrected
