import Leader.Wu.Birth.WaitClockMassResetEntry

/-!
# Reset-sweep entry under arbitrary safe raw interleavings

A root-incoming-free raw word containing the ascending entry word as an ordered
subsequence reaches the existing `BirthWaitClockMass.Line` domain.  No claim is
made about internal carries before or after entry, except for the root and
terminal carry fields required by `Line`.  No scheduler probability or timing
claim is made here.
-/

namespace BirthWaitClockMass.ResetInterleaving

open PPLL PPLLRepair
open BirthWaitClockMass.Line
open BirthWaitClockMass.RawRing
open BirthWaitClockMass.ResetEntry

set_option autoImplicit false
set_option Elab.async false

private structure PrefixDomain {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (D : Fin n → AgentState w) (k : Nat) : Prop where
  label : ∀ i : Fin w, (D (site hfit i)).label = i
  reset : ∀ i : Fin w, i.val < k → (D (site hfit i)).reset = false
  root_carry : 0 < k →
    (D (site hfit (Line.first hw))).carry = false

private theorem mem_split {α : Type} {a : α} {xs : List α} (h : a ∈ xs) :
    ∃ pre post, xs = pre ++ a :: post := by
  induction xs with
  | nil => simp at h
  | cons b bs ih =>
      rcases List.mem_cons.mp h with hba | hb
      · subst b
        exact ⟨[], bs, rfl⟩
      · rcases ih hb with ⟨pre, post, heq⟩
        subst bs
        exact ⟨b :: pre, post, by simp⟩

private theorem safe_step_label {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (C : Fin n → AgentState w)
    (e : Fin n) (he : e ≠ rootIncoming hfit) (x : Fin n) :
    (rawStep hfit hw cap C e x).label = (C x).label := by
  have hf := wait_label_frame (by omega : 0 < w) cap
    (C e) (C ((ring hfit).rightNeighbor e))
  by_cases hi : x = e
  · subst x
    rw [rawStep_initiator]
    exact hf.1
  · by_cases hr : x = (ring hfit).rightNeighbor e
    · subst x
      rw [rawStep_responder hfit hw cap C e he]
      exact hf.2
    · unfold rawStep
      rw [updatePair_other C e ((ring hfit).rightNeighbor e) x _ hi hr]

private theorem safe_step_root_carry {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (C : Fin n → AgentState w)
    (e : Fin n) (he : e ≠ rootIncoming hfit)
    (hc : (C (site hfit (Line.first hw))).carry = false) :
    (rawStep hfit hw cap C e (site hfit (Line.first hw))).carry = false := by
  by_cases hi : e = site hfit (Line.first hw)
  · subst e
    exact (raw_site_initiator_clear hw hfit cap C (Line.first hw)).2
  · have hr : (ring hfit).rightNeighbor e ≠ site hfit (Line.first hw) := by
      intro h
      have hv := congrArg Fin.val h
      rw [right_of_safe hfit e he] at hv
      change e.val + 1 = 0 at hv
      omega
    unfold rawStep
    rw [updatePair_other C e ((ring hfit).rightNeighbor e)
      (site hfit (Line.first hw)) _ (Ne.symm hi) (Ne.symm hr)]
    exact hc

private theorem safe_step_prefix_reset {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (C : Fin n → AgentState w)
    (k : Nat) (P : PrefixDomain hw hfit C k)
    (e : Fin n) (he : e ≠ rootIncoming hfit)
    (i : Fin w) (hi : i.val < k) :
    (rawStep hfit hw cap C e (site hfit i)).reset = false := by
  by_cases hinit : e = site hfit i
  · subst e
    exact (raw_site_initiator_clear hw hfit cap C i).1
  · by_cases hresp : (ring hfit).rightNeighbor e = site hfit i
    · have hv := congrArg Fin.val hresp
      rw [right_of_safe hfit e he] at hv
      change e.val + 1 = i.val at hv
      have hew : e.val < w := by
        have hiw := i.isLt
        omega
      let j : Fin w := ⟨e.val, hew⟩
      have hej : e = site hfit j := by
        apply Fin.ext
        rfl
      have hjk : j.val < k := by
        dsimp [j]
        omega
      have hlz : (C e).reset = false := by
        rw [hej]
        exact P.reset j hjk
      have hrz : (C (site hfit i)).reset = false := P.reset i hi
      have hr0 : (C (site hfit i)).label ≠ ⟨0, by omega⟩ := by
        rw [P.label i]
        intro hzero
        have hz := congrArg Fin.val hzero
        change i.val = 0 at hz
        omega
      have hlc : (C e).label = ⟨0, by omega⟩ → (C e).carry = false := by
        intro hzero
        have hzj :
            (C (site hfit j)).label = ⟨0, by omega⟩ := by
          exact
            (congrArg (fun x : Fin n => (C x).label) hej).symm.trans hzero
        have hj0 : j = Line.first hw := by
          apply Fin.ext
          have hz := congrArg Fin.val ((P.label j).symm.trans hzj)
          simpa only [Line.first] using hz
        have he0 : e = site hfit (Line.first hw) := by
          exact hej.trans
            (congrArg (fun q : Fin w => site hfit q) hj0)
        exact
          (congrArg (fun x : Fin n => (C x).carry) he0).trans
            (P.root_carry (by omega))
      have hrow := BirthWaitClockMass.internal_register_row
        (by omega : 0 < w) cap (C e) (C (site hfit i))
        hr0 hlz hrz hlc
      have hz := congrArg
        (fun p : BirthWaitClockMass.Registers × BirthWaitClockMass.Registers =>
          p.2.reset) hrow
      have hz' :
          (waitSaturated (by omega : 0 < w) cap
            (C e) (C (site hfit i))).2.reset = false := by
        simpa only [BirthWaitClockMass.registerPair,
          BirthWaitClockMass.registers] using hz
      calc
        (rawStep hfit hw cap C e (site hfit i)).reset =
            (rawStep hfit hw cap C e
              ((ring hfit).rightNeighbor e)).reset := by
          rw [hresp]
        _ = (waitSaturated (by omega : 0 < w) cap
              (C e) (C ((ring hfit).rightNeighbor e))).2.reset := by
          rw [rawStep_responder hfit hw cap C e he]
        _ = (waitSaturated (by omega : 0 < w) cap
              (C e) (C (site hfit i))).2.reset := by
          rw [hresp]
        _ = false := hz'
    · unfold rawStep
      rw [updatePair_other C e ((ring hfit).rightNeighbor e)
        (site hfit i) _ (Ne.symm hinit) (Ne.symm hresp)]
      exact P.reset i hi

private theorem prefixDomain_safeStep {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (C : Fin n → AgentState w)
    (k : Nat) (P : PrefixDomain hw hfit C k)
    (e : Fin n) (he : e ≠ rootIncoming hfit) :
    PrefixDomain hw hfit (rawStep hfit hw cap C e) k := by
  refine {
    label := ?_
    reset := ?_
    root_carry := ?_ }
  · intro i
    calc
      (rawStep hfit hw cap C e (site hfit i)).label =
          (C (site hfit i)).label := safe_step_label hw hfit cap C e he _
      _ = i := P.label i
  · intro i hi
    exact safe_step_prefix_reset hw hfit cap C k P e he i hi
  · intro hk
    exact safe_step_root_carry hw hfit cap C e he (P.root_carry hk)

private theorem prefixDomain_safeRun {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (C : Fin n → AgentState w)
    (k : Nat) (P : PrefixDomain hw hfit C k)
    (es : List (Fin n)) (hkill : rootIncoming hfit ∉ es) :
    PrefixDomain hw hfit (rawRun hfit hw cap C es) k := by
  induction es generalizing C with
  | nil => exact P
  | cons e es ih =>
      have he : e ≠ rootIncoming hfit := by
        intro h
        apply hkill
        simp [h]
      have ht : rootIncoming hfit ∉ es := by
        intro hm
        exact hkill (List.mem_cons_of_mem e hm)
      simp only [rawRun]
      exact ih (rawStep hfit hw cap C e)
        (prefixDomain_safeStep hw hfit cap C k P e he) ht

private theorem prefixDomain_advance {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (C : Fin n → AgentState w)
    (k : Nat) (hk : k + 1 ≤ w) (P : PrefixDomain hw hfit C k) :
    let j : Fin w := ⟨k, by omega⟩
    PrefixDomain hw hfit (rawStep hfit hw cap C (site hfit j)) (k + 1) := by
  let j : Fin w := ⟨k, by omega⟩
  have he : site hfit j ≠ rootIncoming hfit := site_ne_rootIncoming hfit j
  have Ps := prefixDomain_safeStep hw hfit cap C k P (site hfit j) he
  have hc := raw_site_initiator_clear hw hfit cap C j
  refine {
    label := Ps.label
    reset := ?_
    root_carry := ?_ }
  · intro i hi
    by_cases hlow : i.val < k
    · exact Ps.reset i hlow
    · have hiv : i.val = k := by omega
      have hieq : i = j := by
        apply Fin.ext
        change i.val = k
        exact hiv
      subst i
      exact hc.1
  · intro _
    by_cases hk0 : k = 0
    · subst k
      simpa only [j, Line.first] using hc.2
    · exact Ps.root_carry (by omega)

private theorem prefix_sublist_domain {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (C : Fin n → AgentState w)
    (hlabel : ∀ i : Fin w, (C (site hfit i)).label = i)
    (k : Nat) (hk : k ≤ w - 1) (es : List (Fin n))
    (hkill : rootIncoming hfit ∉ es)
    (hsub : (prefixWord hfit k (by omega)).Sublist es) :
    PrefixDomain hw hfit (rawRun hfit hw cap C es) k := by
  induction k generalizing es with
  | zero =>
      have P0 : PrefixDomain hw hfit C 0 := {
        label := hlabel
        reset := by
          intro i hi
          omega
        root_carry := by
          intro hk
          omega }
      exact prefixDomain_safeRun hw hfit cap C 0 P0 es hkill
  | succ k ih =>
      rw [prefixWord_succ hfit k (by omega)] at hsub
      rcases List.append_sublist_iff.mp hsub with
        ⟨pre, rest, hes, hpreSub, hone⟩
      have hm : site hfit (⟨k, by omega⟩ : Fin w) ∈ rest :=
        List.singleton_sublist.mp hone
      rcases mem_split hm with ⟨mid, post, hrest⟩
      have hpreKill : rootIncoming hfit ∉ pre := by
        intro hm
        apply hkill
        rw [hes, hrest]
        simp [hm]
      have hmidKill : rootIncoming hfit ∉ mid := by
        intro hm
        apply hkill
        rw [hes, hrest]
        simp [hm]
      have hpostKill : rootIncoming hfit ∉ post := by
        intro hm
        apply hkill
        rw [hes, hrest]
        simp [hm]
      have hp := ih (by omega) pre hpreKill hpreSub
      have hmided := prefixDomain_safeRun hw hfit cap
        (rawRun hfit hw cap C pre) k hp mid hmidKill
      have hadv := prefixDomain_advance hw hfit cap
        (rawRun hfit hw cap (rawRun hfit hw cap C pre) mid)
        k (by omega) hmided
      have hpost := prefixDomain_safeRun hw hfit cap
        (rawStep hfit hw cap
          (rawRun hfit hw cap (rawRun hfit hw cap C pre) mid)
          (site hfit (⟨k, by omega⟩ : Fin w)))
        (k + 1) hadv post hpostKill
      rw [hes, hrest, BirthWaitClockMass.ResetEntry.rawRun_append,
        BirthWaitClockMass.ResetEntry.rawRun_append]
      simpa only [rawRun] using hpost

private theorem entryWord_eq_prefix_last {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) :
    entryWord hfit =
      prefixWord hfit (w - 1) (by omega) ++
        [site hfit (Line.last hw)] := by
  unfold entryWord
  have hs := prefixWord_succ hfit (w - 1)
    (by omega : w - 1 + 1 ≤ w)
  have heq : w - 1 + 1 = w := by omega
  simpa only [heq, Line.last] using hs

/-- Safe-interleaving entry producer.  The whole raw word is unchanged and may
contain arbitrary root-incoming-free edges before, between, and after the
requested ascending sweep.  Only the initial physical line labels are assumed. -/
theorem safe_sublist_entry_produces {w n : Nat}
    (hw : 2 ≤ w) (hfit : w < n) (cap : Nat)
    (C : Fin n → AgentState w)
    (hlabel : ∀ i : Fin w, (C (site hfit i)).label = i)
    (es : List (Fin n))
    (hkill : rootIncoming hfit ∉ es)
    (hsub : (entryWord hfit).Sublist es) :
    ∃ S : BirthWaitClockMass.RawRing.State hw hfit,
      S.conf = rawRun hfit hw cap C es := by
  rw [entryWord_eq_prefix_last hw hfit] at hsub
  rcases List.append_sublist_iff.mp hsub with
    ⟨pre, rest, hes, hpreSub, hone⟩
  have hm : site hfit (Line.last hw) ∈ rest :=
    List.singleton_sublist.mp hone
  rcases mem_split hm with ⟨mid, post, hrest⟩
  have hpreKill : rootIncoming hfit ∉ pre := by
    intro hm
    apply hkill
    rw [hes, hrest]
    simp [hm]
  have hmidKill : rootIncoming hfit ∉ mid := by
    intro hm
    apply hkill
    rw [hes, hrest]
    simp [hm]
  have hpostKill : rootIncoming hfit ∉ post := by
    intro hm
    apply hkill
    rw [hes, hrest]
    simp [hm]
  have hp := prefix_sublist_domain hw hfit cap C hlabel
    (w - 1) (Nat.le_refl _) pre hpreKill hpreSub
  have hmided := prefixDomain_safeRun hw hfit cap
    (rawRun hfit hw cap C pre) (w - 1) hp mid hmidKill
  let D := rawRun hfit hw cap (rawRun hfit hw cap C pre) mid
  let t : Fin w := Line.last hw
  let E := rawStep hfit hw cap D (site hfit t)
  have htSafe : site hfit t ≠ rootIncoming hfit :=
    site_ne_rootIncoming hfit t
  have hpartial : PrefixDomain hw hfit E (w - 1) := by
    exact prefixDomain_safeStep hw hfit cap D (w - 1) hmided
      (site hfit t) htSafe
  have htc :
      (E (site hfit t)).reset = false ∧
        (E (site hfit t)).carry = false := by
    exact raw_site_initiator_clear hw hfit cap D t
  let L : BirthWaitClockMass.Line hw := {
    cell := fun i => E (site hfit i)
    label := hpartial.label
    reset_clear := by
      intro i
      by_cases hi : i.val < w - 1
      · exact hpartial.reset i hi
      · have hiv : i.val = w - 1 := by
          have hiw := i.isLt
          omega
        have hieq : i = t := by
          apply Fin.ext
          change i.val = w - 1
          exact hiv
        subst i
        exact htc.1
    root_carry := hpartial.root_carry (by omega)
    terminal_carry := by
      simpa only [t] using htc.2 }
  let S0 : BirthWaitClockMass.RawRing.State hw hfit := {
    conf := E
    line := L
    agree := by
      intro i
      rfl }
  refine ⟨safeRun hw hfit cap S0
    (liftWord hfit post hpostKill), ?_⟩
  calc
    (safeRun hw hfit cap S0
        (liftWord hfit post hpostKill)).conf =
        rawRun hfit hw cap S0.conf post := by
      have hs := safeRun_conf hw hfit cap S0
        (liftWord hfit post hpostKill)
      rw [erase_liftWord hfit post hpostKill] at hs
      exact hs
    _ = rawRun hfit hw cap C es := by
      change rawRun hfit hw cap E post = rawRun hfit hw cap C es
      rw [hes, hrest, BirthWaitClockMass.ResetEntry.rawRun_append,
        BirthWaitClockMass.ResetEntry.rawRun_append]
      rfl

end BirthWaitClockMass.ResetInterleaving

#print axioms BirthWaitClockMass.ResetInterleaving.safe_sublist_entry_produces
