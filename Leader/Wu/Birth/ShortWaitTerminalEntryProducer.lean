import Leader.Wu.Birth.ShortWaitTerminalEntryInterleaving
import Leader.Wu.Birth.ShortWaitTerminalEntryCompleted


namespace BirthShortWaitTerminalEntryInterleaving


open PPLL PPLLRepair
open BirthShortWaitDomainWitness
open BirthShortWait BirthShortWaitProjection BirthShortWaitRawRing
open BirthWaitClockMass
open BirthWaitClockMass.Line
open BirthWaitClockMass.RawRing
open BirthWaitClockMass.ResetEntry
open BirthShortWaitTerminalEntryRepair


set_option autoImplicit false
set_option Elab.async false


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


private theorem entryRawRun_append {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (C : Fin n → AgentState psi) (a b : List (Fin n)) :
    entryRawRun hpsi hw hle hfit cap C (a ++ b) =
      entryRawRun hpsi hw hle hfit cap
        (entryRawRun hpsi hw hle hfit cap C a) b := by
  induction a generalizing C with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append, entryRawRun]
      exact ih (entryRawStep hpsi hw hle hfit cap C e)


private theorem prefix_sublist_domain {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat) (C : Fin n → AgentState psi)
    (hlabel : ∀ i : Fin width, (C (site hfit i)).label.val = i.val)
    (k : Nat) (hk : k ≤ width - 1) (es : List (Fin n))
    (hkill : rootIncoming hfit ∉ es)
    (hsub : (prefixWord hfit k (by omega)).Sublist es) :
    EntryPrefixDomain hw hfit
      (entryRawRun hpsi hw hle hfit cap C es) k := by
  induction k generalizing es with
  | zero =>
      have P0 : EntryPrefixDomain hw hfit C 0 := {
        line_label := hlabel
        reset := by
          intro i hi
          omega
        root_carry := by
          intro hk
          omega }
      exact entryPrefix_safeRun hpsi hw hle hfit cap C 0
        (by omega) P0 es hkill
  | succ k ih =>
      rw [prefixWord_succ hfit k (by omega)] at hsub
      rcases List.append_sublist_iff.mp hsub with
        ⟨pre, rest, hes, hpreSub, hone⟩
      have hm : site hfit (⟨k, by omega⟩ : Fin width) ∈ rest :=
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
      have hmided := entryPrefix_safeRun hpsi hw hle hfit cap
        (entryRawRun hpsi hw hle hfit cap C pre)
        k (by omega) hp mid hmidKill
      have hadv := entryPrefix_advance hpsi hw hle hfit cap
        (entryRawRun hpsi hw hle hfit cap
          (entryRawRun hpsi hw hle hfit cap C pre) mid)
        k (by omega) hmided
      have hpost := entryPrefix_safeRun hpsi hw hle hfit cap
        (entryRawStep hpsi hw hle hfit cap
          (entryRawRun hpsi hw hle hfit cap
            (entryRawRun hpsi hw hle hfit cap C pre) mid)
          (site hfit (⟨k, by omega⟩ : Fin width)))
        (k + 1) (by omega) hadv post hpostKill
      rw [hes, hrest,
        entryRawRun_append hpsi hw hle hfit cap,
        entryRawRun_append hpsi hw hle hfit cap]
      simpa only [entryRawRun] using hpost


private theorem entryWord_eq_prefix_last {width n : Nat}
    (hw : 2 ≤ width) (hfit : width < n) :
    entryWord hfit =
      prefixWord hfit (width - 1) (by omega) ++
        [site hfit (Line.last hw)] := by
  unfold entryWord
  have hs := prefixWord_succ hfit (width - 1)
    (by omega : width - 1 + 1 ≤ width)
  have heq : width - 1 + 1 = width := by omega
  simpa only [heq, Line.last] using hs


/-- Repaired safe-interleaving entry producer on the literal physical run.
Only the initial physical line labels are assumed. -/
theorem safe_sublist_entry_produces {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (C : Fin n → AgentState psi)
    (hlabel : ∀ i : Fin width, (C (site hfit i)).label.val = i.val)
    (es : List (Fin n))
    (hkill : rootIncoming hfit ∉ es)
    (hsub : (entryWord hfit).Sublist es) :
    ∃ S : BirthShortWaitRawRing.State (psi := psi) hw hfit,
      S.conf = entryRawRun hpsi hw hle hfit cap C es := by
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


  have hp := prefix_sublist_domain hpsi hw hle hfit cap C hlabel
    (width - 1) (Nat.le_refl _) pre hpreKill hpreSub
  have hmided := entryPrefix_safeRun hpsi hw hle hfit cap
    (entryRawRun hpsi hw hle hfit cap C pre)
    (width - 1) (Nat.le_refl _) hp mid hmidKill


  let D := entryRawRun hpsi hw hle hfit cap
    (entryRawRun hpsi hw hle hfit cap C pre) mid
  let t : Fin width := Line.last hw
  let E := entryRawStep hpsi hw hle hfit cap D (site hfit t)


  have htSafe : site hfit t ≠ rootIncoming hfit :=
    site_ne_rootIncoming hfit t
  have hpartial : EntryPrefixDomain hw hfit E (width - 1) := by
    exact entryPrefix_safeStep hpsi hw hle hfit cap D
      (width - 1) (Nat.le_refl _) hmided (site hfit t) htSafe


  have htlabel :
      (D (site hfit t)).label =
        widthTerminal (by omega : 0 < width) hle := by
    apply Fin.ext
    have h := hmided.line_label t
    simpa only [t, Line.last, widthTerminal] using h


  have htc0 := waitWidthEntry_terminal_initiator_clear
    hpsi hw hle cap
    (D (site hfit t))
    (D ((ring hfit).rightNeighbor (site hfit t))) htlabel
  have htc :
      (E (site hfit t)).reset = false ∧
        (E (site hfit t)).carry = false := by
    simpa [E, entryRawStep] using htc0


  have hb : ∀ i : Fin width,
      (E (site hfit i)).label.val < width := by
    intro i
    rw [hpartial.line_label i]
    exact i.isLt


  let L : BirthWaitClockMass.Line hw := {
    cell := fun i => waitPrefixProject (E (site hfit i)) (hb i)
    label := by
      intro i
      apply Fin.ext
      simpa only [waitPrefixProject_label_val] using hpartial.line_label i
    reset_clear := by
      intro i
      by_cases hi : i.val < width - 1
      · simpa only [waitPrefixProject_reset] using hpartial.reset i hi
      · have hiv : i.val = width - 1 := by
          have hiw := i.isLt
          omega
        have hit : i = t := by
          apply Fin.ext
          change i.val = width - 1
          exact hiv
        subst i
        simpa only [waitPrefixProject_reset] using htc.1
    root_carry := by
      simpa only [waitPrefixProject_carry] using
        hpartial.root_carry (by omega)
    terminal_carry := by
      simpa only [waitPrefixProject_carry] using htc.2 }


  let S0 : BirthShortWaitRawRing.State (psi := psi) hw hfit := {
    conf := E
    line := L
    agree := by
      intro i
      unfold BirthShortWaitRawRing.KeyAgree
      change WaitKey.ofState (E (site hfit i)) =
        WaitKey.ofState (waitPrefixProject (E (site hfit i)) (hb i))
      exact (WaitKey_of_waitPrefixProject
        (E (site hfit i)) (hb i)).symm }


  rcases entryCompleted_safeRun hpsi hw hle hfit cap S0 post hpostKill with
    ⟨T, hT⟩
  refine ⟨T, ?_⟩
  calc
    T.conf = entryRawRun hpsi hw hle hfit cap S0.conf post := hT
    _ = entryRawRun hpsi hw hle hfit cap C es := by
      change entryRawRun hpsi hw hle hfit cap E post =
        entryRawRun hpsi hw hle hfit cap C es
      rw [hes, hrest,
        entryRawRun_append hpsi hw hle hfit cap,
        entryRawRun_append hpsi hw hle hfit cap]
      rfl


end BirthShortWaitTerminalEntryInterleaving


#print axioms BirthShortWaitTerminalEntryInterleaving.safe_sublist_entry_produces
