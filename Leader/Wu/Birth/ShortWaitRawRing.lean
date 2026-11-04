import Leader.Wu.Birth.ShortWaitProjection
import Leader.Wu.Birth.WaitClockMassRawRing

set_option autoImplicit false
set_option Elab.async false

namespace BirthShortWaitRawRing

open PPLL PPLLRepair
open BirthShortWait BirthShortWaitDomainWitness BirthShortWaitProjection
open BirthWaitClockMass
open BirthWaitClockMass.RawRing

/-- Cross-carrier proof view: label value plus exactly the four WAIT registers. -/
def KeyAgree {psi width : Nat} (u : AgentState psi) (v : AgentState width) : Prop :=
  WaitKey.ofState u = WaitKey.ofState v

private theorem key_label {psi width : Nat}
    (u : AgentState psi) (v : AgentState width) (h : KeyAgree u v) :
    u.label.val = v.label.val := by
  unfold KeyAgree at h
  simpa [WaitKey.ofState] using congrArg WaitKey.label h

private theorem key_h_field {psi width : Nat}
    (u : AgentState psi) (v : AgentState width) (h : KeyAgree u v) :
    u.h_field = v.h_field := by
  unfold KeyAgree at h
  simpa [WaitKey.ofState] using congrArg WaitKey.h_field h

private theorem key_carry {psi width : Nat}
    (u : AgentState psi) (v : AgentState width) (h : KeyAgree u v) :
    u.carry = v.carry := by
  unfold KeyAgree at h
  simpa [WaitKey.ofState] using congrArg WaitKey.carry h

private theorem key_reset {psi width : Nat}
    (u : AgentState psi) (v : AgentState width) (h : KeyAgree u v) :
    u.reset = v.reset := by
  unfold KeyAgree at h
  simpa [WaitKey.ofState] using congrArg WaitKey.reset h

private theorem key_count {psi width : Nat}
    (u : AgentState psi) (v : AgentState width) (h : KeyAgree u v) :
    u.count = v.count := by
  unfold KeyAgree at h
  simpa [WaitKey.ofState] using congrArg WaitKey.count h

private theorem keyAgree_of_label_regs {psi width : Nat}
    (u : AgentState psi) (v : AgentState width)
    (hl : u.label.val = v.label.val)
    (hr : WaitRegs.ofState u = WaitRegs.ofState v) :
    KeyAgree u v := by
  have hh : u.h_field = v.h_field := by
    simpa [WaitRegs.ofState] using congrArg WaitRegs.h_field hr
  have hc : u.carry = v.carry := by
    simpa [WaitRegs.ofState] using congrArg WaitRegs.carry hr
  have hz : u.reset = v.reset := by
    simpa [WaitRegs.ofState] using congrArg WaitRegs.reset hr
  have hn : u.count = v.count := by
    simpa [WaitRegs.ofState] using congrArg WaitRegs.count hr
  unfold KeyAgree
  change (⟨u.label.val, u.h_field, u.carry, u.reset, u.count⟩ : WaitKey) =
    ⟨v.label.val, v.h_field, v.carry, v.reset, v.count⟩
  rw [hl, hh, hc, hz, hn]

/-- `waitWidth` never changes either label. -/
private theorem waitWidth_label_frame {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi) :
    (waitWidth hpsi hwidth hle kappa l r).1.label = l.label ∧
      (waitWidth hpsi hwidth hle kappa l r).2.label = r.label := by
  simp [waitWidth, waitSaturatedPrepare, waitWidthCarry,
    waitWidthReset, waitWidthFinish]

/-- Same-width `waitSaturated` key semantics depend only on `WaitKey` inputs.
The finish stage may inspect/change `wait`, but it is invisible to this view. -/
private theorem waitSaturated_key_congr {width kappa : Nat}
    (hwidth : 0 < width)
    (a b c d : AgentState width)
    (ha : KeyAgree a c) (hb : KeyAgree b d) :
    waitKeyPair (waitSaturated hwidth kappa a b) =
      waitKeyPair (waitSaturated hwidth kappa c d) := by
  have hal : a.label = c.label := Fin.ext (key_label a c ha)
  have hbl : b.label = d.label := Fin.ext (key_label b d hb)
  have hah := key_h_field a c ha
  have hac := key_carry a c ha
  have haz := key_reset a c ha
  have han := key_count a c ha
  have hbh := key_h_field b d hb
  have hbc := key_carry b d hb
  have hbz := key_reset b d hb
  have hbn := key_count b d hb
  simp [waitKeyPair, WaitKey.ofState, waitSaturated,
    waitSaturatedPrepare, waitSaturatedCarry, waitSaturatedReset,
    waitSaturatedFinish, hal, hbl, hah, hac, haz, han,
    hbh, hbc, hbz, hbn]

/-- Upgrade the accepted cross-psi register projection with the separately
framed labels.  No whole-state equality is used. -/
private theorem waitWidth_key_projection {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi)
    (hl : l.label.val < width) (hr : r.label.val < width) :
    let lp := waitPrefixProject l hl
    let rp := waitPrefixProject r hr
    waitKeyPair (waitWidth hpsi hwidth hle kappa l r) =
      waitKeyPair (waitSaturated hwidth kappa lp rp) := by
  let lp := waitPrefixProject l hl
  let rp := waitPrefixProject r hr
  change waitKeyPair (waitWidth hpsi hwidth hle kappa l r) =
    waitKeyPair (waitSaturated hwidth kappa lp rp)
  have hregs := waitWidth_regs_eq_waitSaturated_prefix
    (kappa := kappa) hpsi hwidth hle l r hl hr
  have hp := waitWidth_label_frame hpsi hwidth hle (kappa := kappa) l r
  have hs := wait_label_frame hwidth kappa lp rp
  apply Prod.ext
  · change KeyAgree
      (waitWidth hpsi hwidth hle kappa l r).1
      (waitSaturated hwidth kappa lp rp).1
    apply keyAgree_of_label_regs
    · rw [hp.1, hs.1]
      rfl
    · simpa [waitRegsPair] using congrArg Prod.fst hregs
  · change KeyAgree
      (waitWidth hpsi hwidth hle kappa l r).2
      (waitSaturated hwidth kappa lp rp).2
    apply keyAgree_of_label_regs
    · rw [hp.2, hs.2]
      rfl
    · simpa [waitRegsPair] using congrArg Prod.snd hregs

/-- Physical ring configuration plus only a key-level lawful-line projection.
All unrelated physical fields, and every physical site outside the line image,
remain unconstrained. -/
structure State {psi width n : Nat} (hw : 2 ≤ width) (hfit : width < n) where
  conf : Fin n → AgentState psi
  line : BirthWaitClockMass.Line hw
  agree : ∀ i : Fin width, KeyAgree (conf (site hfit i)) (line.cell i)

/-- One literal original ring edge.  Every edge calls physical `waitWidth`. -/
def rawStep {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (C : Fin n → AgentState psi) (e : Fin n) :
    Fin n → AgentState psi :=
  updatePair C e ((ring hfit).rightNeighbor e)
    (waitWidth hpsi (by omega : 0 < width) hle cap
      (C e) (C ((ring hfit).rightNeighbor e)))

@[simp] theorem rawStep_initiator {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (C : Fin n → AgentState psi) (e : Fin n) :
    rawStep hpsi hw hle hfit cap C e e =
      (waitWidth hpsi (by omega : 0 < width) hle cap
        (C e) (C ((ring hfit).rightNeighbor e))).1 := by
  simp [rawStep]

@[simp] theorem rawStep_responder {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (C : Fin n → AgentState psi) (e : Fin n)
    (hk : e ≠ rootIncoming hfit) :
    rawStep hpsi hw hle hfit cap C e ((ring hfit).rightNeighbor e) =
      (waitWidth hpsi (by omega : 0 < width) hle cap
        (C e) (C ((ring hfit).rightNeighbor e))).2 := by
  simp [rawStep, updatePair_responder,
    right_ne_self_of_safe hfit e hk]

/-- The physical internal row transports exactly the two proof-line keys. -/
private theorem internal_pair_key {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (S : State (psi := psi) hw hfit) (j : Fin (width - 1)) :
    waitKeyPair
        (waitWidth hpsi (by omega : 0 < width) hle cap
          (S.conf (port hfit j))
          (S.conf ((ring hfit).rightNeighbor (port hfit j)))) =
      waitKeyPair (Line.row cap S.line j) := by
  have hwidth : 0 < width := by omega
  have hL : KeyAgree (S.conf (port hfit j))
      (S.line.cell (Line.left j)) := by
    simpa only [port_eq_site_left hfit j] using S.agree (Line.left j)
  have hR : KeyAgree
      (S.conf ((ring hfit).rightNeighbor (port hfit j)))
      (S.line.cell (Line.right j)) := by
    simpa only [right_port hfit j] using S.agree (Line.right j)
  have hl : (S.conf (port hfit j)).label.val < width := by
    have hk := key_label _ _ hL
    have hline := congrArg Fin.val (S.line.label (Line.left j))
    have hj := j.isLt
    simp only [Line.left] at hline
    omega
  have hr :
      (S.conf ((ring hfit).rightNeighbor (port hfit j))).label.val < width := by
    have hk := key_label _ _ hR
    have hline := congrArg Fin.val (S.line.label (Line.right j))
    have hj := j.isLt
    simp only [Line.right] at hline
    omega
  have hLp : KeyAgree
      (waitPrefixProject (S.conf (port hfit j)) hl)
      (S.line.cell (Line.left j)) := by
    unfold KeyAgree
    rw [WaitKey_of_waitPrefixProject]
    exact hL
  have hRp : KeyAgree
      (waitPrefixProject
        (S.conf ((ring hfit).rightNeighbor (port hfit j))) hr)
      (S.line.cell (Line.right j)) := by
    unfold KeyAgree
    rw [WaitKey_of_waitPrefixProject]
    exact hR
  have hp := waitWidth_key_projection (kappa := cap) hpsi hwidth hle
    (S.conf (port hfit j))
    (S.conf ((ring hfit).rightNeighbor (port hfit j))) hl hr
  have hs := waitSaturated_key_congr (kappa := cap) hwidth
    (waitPrefixProject (S.conf (port hfit j)) hl)
    (waitPrefixProject
      (S.conf ((ring hfit).rightNeighbor (port hfit j))) hr)
    (S.line.cell (Line.left j)) (S.line.cell (Line.right j)) hLp hRp
  calc
    waitKeyPair
        (waitWidth hpsi hwidth hle cap
          (S.conf (port hfit j))
          (S.conf ((ring hfit).rightNeighbor (port hfit j)))) =
      waitKeyPair
        (waitSaturated hwidth cap
          (waitPrefixProject (S.conf (port hfit j)) hl)
          (waitPrefixProject
            (S.conf ((ring hfit).rightNeighbor (port hfit j))) hr)) := hp
    _ = waitKeyPair (Line.row cap S.line j) := by
      simpa only [Line.row] using hs

/-- LDR-BIRTH-SHORT-WAIT-RAW-INTERNAL: actual cross-psi transport on one
physical internal ring edge. -/
theorem internal_port_transport {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (S : State (psi := psi) hw hfit) (j : Fin (width - 1)) :
    KeyAgree
        (waitWidth hpsi (by omega : 0 < width) hle cap
          (S.conf (port hfit j))
          (S.conf ((ring hfit).rightNeighbor (port hfit j)))).1
        (Line.row cap S.line j).1 ∧
      KeyAgree
        (waitWidth hpsi (by omega : 0 < width) hle cap
          (S.conf (port hfit j))
          (S.conf ((ring hfit).rightNeighbor (port hfit j)))).2
        (Line.row cap S.line j).2 := by
  have h := internal_pair_key hpsi hw hle hfit cap S j
  constructor
  · simpa [KeyAgree, waitKeyPair] using congrArg Prod.fst h
  · simpa [KeyAgree, waitKeyPair] using congrArg Prod.snd h

private theorem internal_agree {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (S : State (psi := psi) hw hfit)
    (j : Fin (width - 1)) (i : Fin width) :
    KeyAgree
      (rawStep hpsi hw hle hfit cap S.conf (port hfit j) (site hfit i))
      ((Line.step cap S.line j).cell i) := by
  change KeyAgree
    (rawStep hpsi hw hle hfit cap S.conf (port hfit j) (site hfit i))
    (Line.update cap S.line j i)
  have ht := internal_port_transport hpsi hw hle hfit cap S j
  have hR := right_port hfit j
  by_cases hiL : i = Line.left j
  · subst i
    rw [Line.update_left, ← port_eq_site_left hfit j,
      rawStep_initiator hpsi hw hle hfit cap S.conf (port hfit j)]
    exact ht.1
  · by_cases hiR : i = Line.right j
    · subst i
      rw [Line.update_right, ← hR,
        rawStep_responder hpsi hw hle hfit cap S.conf (port hfit j)
          (port_ne_rootIncoming hfit j)]
      exact ht.2
    · have hp : site hfit i ≠ port hfit j := by
        intro h
        apply hiL
        apply Fin.ext
        have hv := congrArg Fin.val h
        simpa only [site, port, Line.left] using hv
      have hr : site hfit i ≠
          (ring hfit).rightNeighbor (port hfit j) := by
        rw [hR]
        intro h
        apply hiR
        apply Fin.ext
        have hv := congrArg Fin.val h
        simpa only [site] using hv
      rw [Line.update_other cap S.line j i hiL hiR]
      unfold rawStep
      rw [updatePair_other S.conf (port hfit j)
        ((ring hfit).rightNeighbor (port hfit j))
        (site hfit i) _ hp hr]
      exact S.agree i

/-- The only safe external edge touching a line site is terminal-outgoing.
Its initiator key is framed by the lawful terminal label/carry/reset fields;
the arbitrary outside responder is irrelevant. -/
private theorem terminal_initiator_key_frame {psi width kappa : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (l r : AgentState psi)
    (hlabel : l.label.val = width - 1)
    (hcarry : l.carry = false) (hreset : l.reset = false) :
    WaitKey.ofState
        (waitWidth hpsi (by omega : 0 < width) hle kappa l r).1 =
      WaitKey.ofState l := by
  have hl0 : l.label ≠ (⟨0, hpsi⟩ : Fin psi) := by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    rw [hlabel] at hv
    omega
  simp [waitWidth, waitSaturatedPrepare, waitWidthCarry,
    waitWidthReset, waitWidthFinish, WaitKey.ofState,
    hl0, hcarry, hreset]

private theorem external_agree {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (S : State (psi := psi) hw hfit)
    (e : Fin n) (hk : e ≠ rootIncoming hfit)
    (hext : ¬ e.val < width - 1) (i : Fin width) :
    KeyAgree
      (rawStep hpsi hw hle hfit cap S.conf e (site hfit i))
      (S.line.cell i) := by
  by_cases hout : e.val = width - 1
  · have heq : e = terminalOutgoing hfit := by
      apply Fin.ext
      exact hout
    subst e
    by_cases hi : i = Line.last hw
    · subst i
      have hag : KeyAgree
          (S.conf (terminalOutgoing hfit))
          (S.line.cell (Line.last hw)) := by
        rw [← site_last_eq_terminal hw hfit]
        exact S.agree (Line.last hw)
      have hlabel :
          (S.conf (terminalOutgoing hfit)).label.val = width - 1 := by
        calc
          (S.conf (terminalOutgoing hfit)).label.val =
              (S.line.cell (Line.last hw)).label.val := key_label _ _ hag
          _ = (Line.last hw).val :=
            congrArg Fin.val (S.line.label (Line.last hw))
          _ = width - 1 := rfl
      have hcarry :
          (S.conf (terminalOutgoing hfit)).carry = false := by
        calc
          (S.conf (terminalOutgoing hfit)).carry =
              (S.line.cell (Line.last hw)).carry := key_carry _ _ hag
          _ = false := S.line.terminal_carry
      have hreset :
          (S.conf (terminalOutgoing hfit)).reset = false := by
        calc
          (S.conf (terminalOutgoing hfit)).reset =
              (S.line.cell (Line.last hw)).reset := key_reset _ _ hag
          _ = false := S.line.reset_clear (Line.last hw)
      have hf := terminal_initiator_key_frame (kappa := cap) hpsi hw hle
        (S.conf (terminalOutgoing hfit))
        (S.conf ((ring hfit).rightNeighbor (terminalOutgoing hfit)))
        hlabel hcarry hreset
      rw [site_last_eq_terminal hw hfit,
        rawStep_initiator hpsi hw hle hfit cap S.conf
          (terminalOutgoing hfit)]
      exact hf.trans hag
    · have hne : site hfit i ≠ terminalOutgoing hfit := by
        intro h
        apply hi
        apply Fin.ext
        have hv := congrArg Fin.val h
        simpa only [site, terminalOutgoing, Line.last] using hv
      have hrval := right_of_safe hfit (terminalOutgoing hfit)
        (terminalOutgoing_ne_rootIncoming hfit hw)
      have hnr : site hfit i ≠
          (ring hfit).rightNeighbor (terminalOutgoing hfit) := by
        intro h
        have hv := congrArg Fin.val h
        rw [hrval] at hv
        have hii := i.isLt
        simp only [site, terminalOutgoing] at hv
        omega
      unfold rawStep
      rw [updatePair_other S.conf (terminalOutgoing hfit)
        ((ring hfit).rightNeighbor (terminalOutgoing hfit))
        (site hfit i) _ hne hnr]
      exact S.agree i
  · have hge : width ≤ e.val := by omega
    have hrval := right_of_safe hfit e hk
    have hne : site hfit i ≠ e := by
      intro h
      have hv := congrArg Fin.val h
      have hii := i.isLt
      simp only [site] at hv
      omega
    have hnr : site hfit i ≠ (ring hfit).rightNeighbor e := by
      intro h
      have hv := congrArg Fin.val h
      rw [hrval] at hv
      have hii := i.isLt
      simp only [site] at hv
      omega
    unfold rawStep
    rw [updatePair_other S.conf e ((ring hfit).rightNeighbor e)
      (site hfit i) _ hne hnr]
    exact S.agree i

/-- LDR-BIRTH-SHORT-WAIT-RAW-EXTERNAL: every non-internal, non-root-incoming
raw edge stutters on every proof-line key. -/
theorem external_safe_stutter {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (S : State (psi := psi) hw hfit)
    (e : Fin n) (hk : e ≠ rootIncoming hfit)
    (hext : ¬ e.val < width - 1) (i : Fin width) :
    KeyAgree
      (rawStep hpsi hw hle hfit cap S.conf e (site hfit i))
      (S.line.cell i) :=
  external_agree hpsi hw hle hfit cap S e hk hext i

/-- Explicit audit point: the terminal-outgoing edge is included in the
external stutter theorem, using only fields already supplied by `Line`. -/
theorem terminalOutgoing_stutter {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (S : State (psi := psi) hw hfit) (i : Fin width) :
    KeyAgree
      (rawStep hpsi hw hle hfit cap S.conf (terminalOutgoing hfit)
        (site hfit i))
      (S.line.cell i) := by
  exact external_safe_stutter hpsi hw hle hfit cap S
    (terminalOutgoing hfit)
    (terminalOutgoing_ne_rootIncoming hfit hw)
    (by simp [terminalOutgoing]) i

/-- Reuse the frozen raw-ring safe-letter type; only the state coupling changes. -/
abbrev SafeEdge {width n : Nat} (hfit : width < n) :=
  BirthWaitClockMass.RawRing.SafeEdge (w := width) (n := n) hfit

/-- Execute one original safe raw edge while updating only the proof projection
on internal ports. -/
def safeStep {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (S : State (psi := psi) hw hfit) (e : SafeEdge hfit) :
    State (psi := psi) hw hfit :=
  if h : e.1.val < width - 1 then
    let j : Fin (width - 1) := ⟨e.1.val, h⟩
    { conf := rawStep hpsi hw hle hfit cap S.conf e.1
      line := Line.step cap S.line j
      agree := by
        intro i
        have he : e.1 = port hfit j := by
          apply Fin.ext
          rfl
        rw [he]
        exact internal_agree hpsi hw hle hfit cap S j i }
  else
    { conf := rawStep hpsi hw hle hfit cap S.conf e.1
      line := S.line
      agree := external_agree hpsi hw hle hfit cap S e.1 e.2 h }

@[simp] theorem safeStep_conf {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (S : State (psi := psi) hw hfit) (e : SafeEdge hfit) :
    (safeStep hpsi hw hle hfit cap S e).conf =
      rawStep hpsi hw hle hfit cap S.conf e.1 := by
  unfold safeStep
  split <;> rfl

/-- Safe replay, still on the exact physical raw letters. -/
def safeRun {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat) :
    State (psi := psi) hw hfit → List (SafeEdge hfit) →
      State (psi := psi) hw hfit
  | S, [] => S
  | S, e :: es =>
      safeRun hpsi hw hle hfit cap
        (safeStep hpsi hw hle hfit cap S e) es

/-- Literal physical execution of the original `Fin n` word. -/
def rawRun {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat) :
    (Fin n → AgentState psi) → List (Fin n) → Fin n → AgentState psi
  | C, [] => C
  | C, e :: es =>
      rawRun hpsi hw hle hfit cap
        (rawStep hpsi hw hle hfit cap C e) es

theorem safeRun_line {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (S : State (psi := psi) hw hfit) (es : List (SafeEdge hfit)) :
    (safeRun hpsi hw hle hfit cap S es).line =
      Line.run cap S.line (lineWord hfit es) := by
  induction es generalizing S with
  | nil => rfl
  | cons e es ih =>
    by_cases h : e.1.val < width - 1
    · simp only [safeRun, lineWord, dif_pos h, safeStep, ih, Line.run]
    · simp only [safeRun, lineWord, dif_neg h, safeStep, ih]

theorem safeRun_conf {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (S : State (psi := psi) hw hfit) (es : List (SafeEdge hfit)) :
    (safeRun hpsi hw hle hfit cap S es).conf =
      rawRun hpsi hw hle hfit cap S.conf (eraseWord hfit es) := by
  induction es generalizing S with
  | nil => rfl
  | cons e es ih =>
    change
      (safeRun hpsi hw hle hfit cap
        (safeStep hpsi hw hle hfit cap S e) es).conf =
      rawRun hpsi hw hle hfit cap
        (rawStep hpsi hw hle hfit cap S.conf e.1)
        (eraseWord hfit es)
    rw [← safeStep_conf hpsi hw hle hfit cap S e]
    exact ih (safeStep hpsi hw hle hfit cap S e)

/-- LDR-BIRTH-SHORT-WAIT-RAW-REPLAY: the original physical word is replayed
unchanged up to the unique root-incoming edge.  The proof line sees exactly the
existing deterministic internal-port projection; external safe letters stutter.
No physical field outside `WaitKey`, and no outside physical site, is assumed. -/
theorem raw_word_key_replay {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (S : State (psi := psi) hw hfit) (es : List (Fin n))
    (hkill : rootIncoming hfit ∉ es) (i : Fin width) :
    KeyAgree
      (rawRun hpsi hw hle hfit cap S.conf es (site hfit i))
      ((Line.run cap S.line (projectRawWord hfit es hkill)).cell i) := by
  have h :=
    (safeRun hpsi hw hle hfit cap S (liftWord hfit es hkill)).agree i
  rw [safeRun_conf hpsi hw hle hfit cap S (liftWord hfit es hkill)] at h
  rw [safeRun_line hpsi hw hle hfit cap S (liftWord hfit es hkill)] at h
  rw [erase_liftWord hfit es hkill] at h
  simpa only [projectRawWord] using h

#print axioms BirthShortWaitRawRing.internal_port_transport
#print axioms BirthShortWaitRawRing.external_safe_stutter
#print axioms BirthShortWaitRawRing.terminalOutgoing_stutter
#print axioms BirthShortWaitRawRing.safeRun_conf
#print axioms BirthShortWaitRawRing.raw_word_key_replay

end BirthShortWaitRawRing
