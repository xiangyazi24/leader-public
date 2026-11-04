import Leader.Wu.Birth.ShortWaitTerminalEntryRepair

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

private theorem active_regs {psi width cap : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi) (hl : l.label.val < width)
    (hr : r.label.val < width) :
    waitRegsPair (waitWidthEntry hpsi hwidth hle cap l r) =
      waitRegsPair (waitSaturated hwidth cap
        (waitPrefixProject l hl) (waitPrefixProject r hr)) := by
  rw [waitWidthEntry_eq_old_of_active_labels hpsi hwidth hle cap l r hl hr]
  simpa only using waitWidth_regs_eq_waitSaturated_prefix
    (kappa := cap) hpsi hwidth hle l r hl hr

private theorem active_responder_reset {psi width cap : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi) (hl : l.label.val < width)
    (hr : r.label.val < width) (hr0 : r.label.val ≠ 0)
    (hlz : l.reset = false) (hrz : r.reset = false)
    (hlc : l.label.val = 0 → l.carry = false) :
    (waitWidthEntry hpsi hwidth hle cap l r).2.reset = false := by
  have hr0' : (waitPrefixProject r hr).label ≠ (⟨0, hwidth⟩ : Fin width) := by
    intro h
    apply hr0
    have hv := congrArg Fin.val h
    simpa only [waitPrefixProject_label_val] using hv
  have hlc' :
      (waitPrefixProject l hl).label = (⟨0, hwidth⟩ : Fin width) →
        (waitPrefixProject l hl).carry = false := by
    intro h
    have hv := congrArg Fin.val h
    have hv' : l.label.val = 0 := by
      simpa only [waitPrefixProject_label_val] using hv
    simpa only [waitPrefixProject_carry] using hlc hv'
  have hrow := BirthWaitClockMass.internal_register_row hwidth cap
    (waitPrefixProject l hl) (waitPrefixProject r hr) hr0'
    (by simpa only [waitPrefixProject_reset] using hlz)
    (by simpa only [waitPrefixProject_reset] using hrz) hlc'
  have hz :
      (waitSaturated hwidth cap
        (waitPrefixProject l hl) (waitPrefixProject r hr)).2.reset = false := by
    have h := congrArg
      (fun p : Registers × Registers => p.2.reset) hrow
    simpa only [registerPair, registers] using h
  have hp := congrArg Prod.snd
    (active_regs (cap := cap) hpsi hwidth hle l r hl hr)
  have h := congrArg WaitRegs.reset hp
  simpa only [waitRegsPair, WaitRegs.ofState] using h.trans hz

private theorem waitWidthEntry_label_frame {psi width cap : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi) :
    (waitWidthEntry hpsi hwidth hle cap l r).1.label = l.label ∧
      (waitWidthEntry hpsi hwidth hle cap l r).2.label = r.label := by
  simp [waitWidthEntry, waitSaturatedPrepare, terminalInactiveClear,
    waitWidthCarry, waitWidthReset, waitWidthFinish]

private theorem step_initiator {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat) (C : Fin n → AgentState psi)
    (e : Fin n) :
    entryRawStep hpsi hw hle hfit cap C e e =
      (waitWidthEntry hpsi (by omega) hle cap
        (C e) (C ((ring hfit).rightNeighbor e))).1 := by
  simp [entryRawStep]

private theorem step_responder {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat) (C : Fin n → AgentState psi)
    (e : Fin n) (he : e ≠ rootIncoming hfit) :
    entryRawStep hpsi hw hle hfit cap C e
        ((ring hfit).rightNeighbor e) =
      (waitWidthEntry hpsi (by omega) hle cap
        (C e) (C ((ring hfit).rightNeighbor e))).2 := by
  simp [entryRawStep, updatePair_responder,
    right_ne_self_of_safe hfit e he]

/-- Literal repaired raw step frames every physical label on a safe letter. -/
theorem entryRawStep_label {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat) (C : Fin n → AgentState psi)
    (e : Fin n) (he : e ≠ rootIncoming hfit) (x : Fin n) :
    (entryRawStep hpsi hw hle hfit cap C e x).label = (C x).label := by
  have hf := waitWidthEntry_label_frame (cap := cap) hpsi (by omega : 0 < width) hle
    (C e) (C ((ring hfit).rightNeighbor e))
  by_cases hi : x = e
  · subst x; rw [step_initiator]; exact hf.1
  · by_cases hr : x = (ring hfit).rightNeighbor e
    · subst x; rw [step_responder hpsi hw hle hfit cap C e he]; exact hf.2
    · unfold entryRawStep
      rw [updatePair_other C e ((ring hfit).rightNeighbor e) x _ hi hr]

/-- A lawful nonterminal line initiator is active with its real next line site,
so the repaired physical row clears its reset/carry with no old-bit premise. -/
theorem entryRawStep_site_nonterminal_clear {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat) (C : Fin n → AgentState psi)
    (i : Fin width) (hi : i.val < width - 1)
    (hlabel : ∀ j : Fin width, (C (site hfit j)).label.val = j.val) :
    (entryRawStep hpsi hw hle hfit cap C (site hfit i)
      (site hfit i)).reset = false ∧
    (entryRawStep hpsi hw hle hfit cap C (site hfit i)
      (site hfit i)).carry = false := by
  let j : Fin width := ⟨i.val + 1, by omega⟩
  have hright : (ring hfit).rightNeighbor (site hfit i) = site hfit j := by
    apply Fin.ext
    rw [right_of_safe hfit (site hfit i) (site_ne_rootIncoming hfit i)]
    rfl
  have hl : (C (site hfit i)).label.val < width := by
    rw [hlabel i]; exact i.isLt
  have hr : (C ((ring hfit).rightNeighbor (site hfit i))).label.val < width := by
    rw [hright, hlabel j]; exact j.isLt
  have hp := congrArg Prod.fst
    (active_regs (cap := cap) hpsi (by omega : 0 < width) hle
      (C (site hfit i)) (C ((ring hfit).rightNeighbor (site hfit i))) hl hr)
  have hs := wait_initiator_clear (by omega : 0 < width) cap
    (waitPrefixProject (C (site hfit i)) hl)
    (waitPrefixProject (C ((ring hfit).rightNeighbor (site hfit i))) hr)
  rw [step_initiator]
  constructor
  · have h := congrArg WaitRegs.reset hp
    simpa only [waitRegsPair, WaitRegs.ofState] using h.trans hs.1
  · have h := congrArg WaitRegs.carry hp
    simpa only [waitRegsPair, WaitRegs.ofState] using h.trans hs.2

structure EntryPrefixDomain {psi width n : Nat}
    (hw : 2 ≤ width) (hfit : width < n)
    (D : Fin n → AgentState psi) (k : Nat) : Prop where
  line_label : ∀ i : Fin width, (D (site hfit i)).label.val = i.val
  reset : ∀ i : Fin width, i.val < k → (D (site hfit i)).reset = false
  root_carry : 0 < k → (D (site hfit (Line.first hw))).carry = false

private theorem safe_root_carry {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat) (C : Fin n → AgentState psi)
    (k : Nat) (P : EntryPrefixDomain hw hfit C k)
    (e : Fin n) (he : e ≠ rootIncoming hfit) (hk : 0 < k) :
    (entryRawStep hpsi hw hle hfit cap C e
      (site hfit (Line.first hw))).carry = false := by
  by_cases hi : e = site hfit (Line.first hw)
  · subst e
    exact (entryRawStep_site_nonterminal_clear hpsi hw hle hfit cap C
      (Line.first hw) (by simp only [Line.first]; omega) P.line_label).2
  · have hr : (ring hfit).rightNeighbor e ≠ site hfit (Line.first hw) := by
      intro h
      have hv := congrArg Fin.val h
      rw [right_of_safe hfit e he] at hv
      change e.val + 1 = 0 at hv
      omega
    unfold entryRawStep
    rw [updatePair_other C e ((ring hfit).rightNeighbor e)
      (site hfit (Line.first hw)) _ (Ne.symm hi) (Ne.symm hr)]
    exact P.root_carry hk

private theorem safe_prefix_reset {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat) (C : Fin n → AgentState psi)
    (k : Nat) (hk : k ≤ width - 1) (P : EntryPrefixDomain hw hfit C k)
    (e : Fin n) (he : e ≠ rootIncoming hfit)
    (i : Fin width) (hi : i.val < k) :
    (entryRawStep hpsi hw hle hfit cap C e (site hfit i)).reset = false := by
  by_cases hinit : e = site hfit i
  · subst e
    exact (entryRawStep_site_nonterminal_clear hpsi hw hle hfit cap C i
      (by omega) P.line_label).1
  · by_cases hresp : (ring hfit).rightNeighbor e = site hfit i
    · have hv := congrArg Fin.val hresp
      rw [right_of_safe hfit e he] at hv
      change e.val + 1 = i.val at hv
      have hew : e.val < width := by have := i.isLt; omega
      let j : Fin width := ⟨e.val, hew⟩
      have hej : e = site hfit j := by apply Fin.ext; rfl
      have hjk : j.val < k := by dsimp [j]; omega
      have hl : (C e).label.val < width := by
        rw [hej, P.line_label j]; exact j.isLt
      have hr : (C (site hfit i)).label.val < width := by
        rw [P.line_label i]; exact i.isLt
      have hr0 : (C (site hfit i)).label.val ≠ 0 := by
        intro hz
        have hiLab := P.line_label i
        omega
      have hlc : (C e).label.val = 0 → (C e).carry = false := by
        intro hz
        rw [hej] at hz ⊢
        have hj0v : j.val = 0 := by
          have hjLab := P.line_label j
          omega
        have hj0 : j = Line.first hw := by
          apply Fin.ext
          simpa only [Line.first] using hj0v
        rw [hj0]
        exact P.root_carry (by omega)
      have hz := active_responder_reset (cap := cap) hpsi (by omega : 0 < width) hle
        (C e) (C (site hfit i)) hl hr hr0
        (by rw [hej]; exact P.reset j hjk) (P.reset i hi) hlc
      calc
        (entryRawStep hpsi hw hle hfit cap C e (site hfit i)).reset =
            (waitWidthEntry hpsi (by omega) hle cap
              (C e) (C (site hfit i))).2.reset := by
          rw [← hresp, step_responder hpsi hw hle hfit cap C e he, hresp]
        _ = false := hz
    · unfold entryRawStep
      rw [updatePair_other C e ((ring hfit).rightNeighbor e)
        (site hfit i) _ (Ne.symm hinit) (Ne.symm hresp)]
      exact P.reset i hi

/-- Any root-incoming-free repaired letter preserves an already processed prefix. -/
theorem entryPrefix_safeStep {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat) (C : Fin n → AgentState psi)
    (k : Nat) (hk : k ≤ width - 1) (P : EntryPrefixDomain hw hfit C k)
    (e : Fin n) (he : e ≠ rootIncoming hfit) :
    EntryPrefixDomain hw hfit (entryRawStep hpsi hw hle hfit cap C e) k := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have h := congrArg Fin.val
      (entryRawStep_label hpsi hw hle hfit cap C e he (site hfit i))
    exact h.trans (P.line_label i)
  · intro i hi
    exact safe_prefix_reset hpsi hw hle hfit cap C k hk P e he i hi
  · intro hk0
    exact safe_root_carry hpsi hw hle hfit cap C k P e he hk0

/-- The same prefix invariant survives an arbitrary root-incoming-free real word. -/
theorem entryPrefix_safeRun {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat) (C : Fin n → AgentState psi)
    (k : Nat) (hk : k ≤ width - 1) (P : EntryPrefixDomain hw hfit C k)
    (es : List (Fin n)) (hkill : rootIncoming hfit ∉ es) :
    EntryPrefixDomain hw hfit (entryRawRun hpsi hw hle hfit cap C es) k := by
  induction es generalizing C with
  | nil => exact P
  | cons e es ih =>
      have he : e ≠ rootIncoming hfit := by
        intro h; apply hkill; simp [h]
      have ht : rootIncoming hfit ∉ es := by
        intro hm; exact hkill (List.mem_cons_of_mem e hm)
      simp only [entryRawRun]
      exact ih (entryRawStep hpsi hw hle hfit cap C e)
        (entryPrefix_safeStep hpsi hw hle hfit cap C k hk P e he) ht

/-- Scheduling the next prescribed nonterminal entry site advances k by one. -/
theorem entryPrefix_advance {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat) (C : Fin n → AgentState psi)
    (k : Nat) (hk : k + 1 ≤ width - 1)
    (P : EntryPrefixDomain hw hfit C k) :
    let j : Fin width := ⟨k, by omega⟩
    EntryPrefixDomain hw hfit
      (entryRawStep hpsi hw hle hfit cap C (site hfit j)) (k + 1) := by
  let j : Fin width := ⟨k, by omega⟩
  have he : site hfit j ≠ rootIncoming hfit := site_ne_rootIncoming hfit j
  have Ps := entryPrefix_safeStep hpsi hw hle hfit cap C k (by omega) P
    (site hfit j) he
  have hc := entryRawStep_site_nonterminal_clear hpsi hw hle hfit cap C j
    (by dsimp [j]; omega) P.line_label
  refine ⟨Ps.line_label, ?_, ?_⟩
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

end BirthShortWaitTerminalEntryInterleaving

#print axioms BirthShortWaitTerminalEntryInterleaving.entryRawStep_label
#print axioms BirthShortWaitTerminalEntryInterleaving.entryRawStep_site_nonterminal_clear
#print axioms BirthShortWaitTerminalEntryInterleaving.entryPrefix_safeStep
#print axioms BirthShortWaitTerminalEntryInterleaving.entryPrefix_safeRun
#print axioms BirthShortWaitTerminalEntryInterleaving.entryPrefix_advance

-- Literal imported psi=4,width=2,n=4 obstruction/repair witness, unchanged.
#check BirthShortWaitTerminalEntryRepair.target_range4
#check BirthShortWaitTerminalEntryRepair.old_terminal_still_dirty4
#check BirthShortWaitTerminalEntryRepair.repaired_terminal_clear4
#print axioms BirthShortWaitTerminalEntryRepair.old_terminal_still_dirty4
#print axioms BirthShortWaitTerminalEntryRepair.repaired_terminal_clear4
