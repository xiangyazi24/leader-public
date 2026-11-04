import Leader.Wu.Birth.WaitClockMassHit
import Leader.Wu.Safety.SignalCoherence

namespace BirthWaitClockMass.RawRing

open PPLL PPLLRepair
open BirthWaitClockMass.Line

set_option autoImplicit false
set_option Elab.async false

/-! No namespace-level proof variables: every declaration exposes exactly the
proofs it needs, so tactic elaboration cannot capture shadow copies. -/

/-- The concrete directed ring used by the replay. -/
def ring {w n : Nat} (hfit : w < n) : DirectedRing n :=
  ⟨by
    exact Nat.lt_of_le_of_lt (Nat.zero_le w) hfit⟩

/-- Physical image of a line cell. -/
def site {w n : Nat} (hfit : w < n) (i : Fin w) : Fin n :=
  ⟨i.val, by
    exact Nat.lt_trans i.isLt hfit⟩

/-- Physical image of an internal WAIT port. -/
def port {w n : Nat} (hfit : w < n) (j : Fin (w - 1)) : Fin n :=
  ⟨j.val, by
    have hj := j.isLt
    omega⟩

/-- The only edge entering physical site zero. -/
def rootIncoming {w n : Nat} (hfit : w < n) : Fin n :=
  ⟨n - 1, by omega⟩

/-- The edge leaving the terminal line cell toward site `w`. -/
def terminalOutgoing {w n : Nat} (hfit : w < n) : Fin n :=
  ⟨w - 1, by omega⟩

theorem port_eq_site_left {w n : Nat} (hfit : w < n)
    (j : Fin (w - 1)) :
    port hfit j = site hfit (Line.left j) := by
  apply Fin.ext
  rfl

theorem site_last_eq_terminal {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) :
    site hfit (Line.last hw) = terminalOutgoing hfit := by
  apply Fin.ext
  rfl

theorem port_ne_rootIncoming {w n : Nat} (hfit : w < n)
    (j : Fin (w - 1)) :
    port hfit j ≠ rootIncoming hfit := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  simp only [port, rootIncoming] at hv
  omega

theorem terminalOutgoing_ne_rootIncoming {w n : Nat}
    (hfit : w < n) (hwidth : 2 ≤ w) :
    terminalOutgoing hfit ≠ rootIncoming hfit := by
  intro h
  have hv := congrArg Fin.val h
  simp only [terminalOutgoing, rootIncoming] at hv
  omega

theorem right_of_safe {w n : Nat} (hfit : w < n)
    (e : Fin n) (hk : e ≠ rootIncoming hfit) :
    ((ring hfit).rightNeighbor e).val = e.val + 1 := by
  have he := e.isLt
  have hlast : e.val ≠ n - 1 := by
    intro hv
    apply hk
    apply Fin.ext
    simpa only [rootIncoming] using hv
  have hb : e.val + 1 < n := by omega
  change (e.val + 1) % n = e.val + 1
  exact Nat.mod_eq_of_lt hb

theorem right_ne_self_of_safe {w n : Nat} (hfit : w < n)
    (e : Fin n) (hk : e ≠ rootIncoming hfit) :
    (ring hfit).rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  rw [right_of_safe hfit e hk] at hv
  omega

theorem right_port {w n : Nat} (hfit : w < n)
    (j : Fin (w - 1)) :
    (ring hfit).rightNeighbor (port hfit j) =
      site hfit (Line.right j) := by
  apply Fin.ext
  rw [right_of_safe hfit (port hfit j)
    (port_ne_rootIncoming hfit j)]
  rfl

/-- One original raw directed-ring edge, with the literal saturating WAIT row. -/
def rawStep {w n : Nat} (hfit : w < n) (hwidth : 2 ≤ w)
    (cap : Nat) (C : Fin n → AgentState w) (e : Fin n) :
    Fin n → AgentState w :=
  updatePair C e ((ring hfit).rightNeighbor e)
    (waitSaturated (by omega : 0 < w) cap
      (C e) (C ((ring hfit).rightNeighbor e)))

@[simp] theorem rawStep_initiator {w n : Nat} (hfit : w < n)
    (hwidth : 2 ≤ w) (cap : Nat)
    (C : Fin n → AgentState w) (e : Fin n) :
    rawStep hfit hwidth cap C e e =
      (waitSaturated (by omega : 0 < w) cap
        (C e) (C ((ring hfit).rightNeighbor e))).1 := by
  simp [rawStep]

@[simp] theorem rawStep_responder {w n : Nat} (hfit : w < n)
    (hwidth : 2 ≤ w) (cap : Nat)
    (C : Fin n → AgentState w) (e : Fin n)
    (hk : e ≠ rootIncoming hfit) :
    rawStep hfit hwidth cap C e ((ring hfit).rightNeighbor e) =
      (waitSaturated (by omega : 0 < w) cap
        (C e) (C ((ring hfit).rightNeighbor e))).2 := by
  simp [rawStep, updatePair_responder,
    right_ne_self_of_safe hfit e hk]

/-- A physical ring configuration bundled with exactly the checked lawful line. -/
structure State {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) where
  conf : Fin n → AgentState w
  line : BirthWaitClockMass.Line hw
  agree : ∀ i : Fin w, line.cell i = conf (site hfit i)

private theorem internal_agree {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (S : State hw hfit)
    (j : Fin (w - 1)) (i : Fin w) :
    (Line.step cap S.line j).cell i =
      rawStep hfit hw cap S.conf (port hfit j) (site hfit i) := by
  change Line.update cap S.line j i = _
  have hL := port_eq_site_left hfit j
  have hR := right_port hfit j
  by_cases hiL : i = Line.left j
  · subst i
    rw [Line.update_left, ← hL,
      rawStep_initiator hfit hw cap S.conf (port hfit j)]
    simp only [Line.row]
    rw [hR, hL, ← S.agree (Line.left j),
      ← S.agree (Line.right j)]
  · by_cases hiR : i = Line.right j
    · subst i
      rw [Line.update_right, ← hR,
        rawStep_responder hfit hw cap S.conf (port hfit j)
          (port_ne_rootIncoming hfit j)]
      simp only [Line.row]
      rw [hR, hL, ← S.agree (Line.left j),
        ← S.agree (Line.right j)]
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
        have hv := congrArg (fun x : Fin n => x.val) h
        simpa only [site] using hv
      rw [Line.update_other cap S.line j i hiL hiR]
      unfold rawStep
      rw [updatePair_other S.conf (port hfit j)
        ((ring hfit).rightNeighbor (port hfit j))
        (site hfit i) _ hp hr]
      exact S.agree i

private theorem external_agree {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (S : State hw hfit)
    (e : Fin n) (hk : e ≠ rootIncoming hfit)
    (hext : ¬ e.val < w - 1) (i : Fin w) :
    S.line.cell i = rawStep hfit hw cap S.conf e (site hfit i) := by
  by_cases hout : e.val = w - 1
  · have heq : e = terminalOutgoing hfit := by
      apply Fin.ext
      exact hout
    subst e
    by_cases hi : i = Line.last hw
    · subst i
      have hlabel :
          (S.conf (terminalOutgoing hfit)).label =
            ⟨w - 1, by omega⟩ := by
        rw [← site_last_eq_terminal hw hfit,
          ← S.agree (Line.last hw)]
        simpa only [Line.last] using S.line.label (Line.last hw)
      have hcarry :
          (S.conf (terminalOutgoing hfit)).carry = false := by
        rw [← site_last_eq_terminal hw hfit,
          ← S.agree (Line.last hw)]
        exact S.line.terminal_carry
      have hreset :
          (S.conf (terminalOutgoing hfit)).reset = false := by
        rw [← site_last_eq_terminal hw hfit,
          ← S.agree (Line.last hw)]
        exact S.line.reset_clear (Line.last hw)
      have hf := terminal_outgoing_frame hw cap
        (S.conf (terminalOutgoing hfit))
        (S.conf ((ring hfit).rightNeighbor (terminalOutgoing hfit)))
        hlabel hcarry hreset
      calc
        S.line.cell (Line.last hw) =
            S.conf (terminalOutgoing hfit) := by
          rw [← site_last_eq_terminal hw hfit]
          exact S.agree (Line.last hw)
        _ = (waitSaturated (by omega : 0 < w) cap
              (S.conf (terminalOutgoing hfit))
              (S.conf ((ring hfit).rightNeighbor
                (terminalOutgoing hfit)))).1 := hf.symm
        _ = rawStep hfit hw cap S.conf (terminalOutgoing hfit)
              (site hfit (Line.last hw)) := by
          rw [site_last_eq_terminal hw hfit]
          exact (rawStep_initiator hfit hw cap S.conf
            (terminalOutgoing hfit)).symm
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
  · have hge : w ≤ e.val := by omega
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

/-- Raw ring edges other than the unique root-incoming edge. -/
abbrev SafeEdge {w n : Nat} (hfit : w < n) :=
  {e : Fin n // e ≠ rootIncoming hfit}

/-- Embed one requested line port as its exact raw-ring edge. -/
def safePort {w n : Nat} (hfit : w < n)
    (j : Fin (w - 1)) : SafeEdge hfit :=
  ⟨port hfit j, port_ne_rootIncoming hfit j⟩

/-- Execute one safe raw edge and retain its exact physical configuration. -/
def safeStep {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (S : State hw hfit) (e : SafeEdge hfit) :
    State hw hfit :=
  if h : e.1.val < w - 1 then
    let j : Fin (w - 1) := ⟨e.1.val, h⟩
    { conf := rawStep hfit hw cap S.conf e.1
      line := Line.step cap S.line j
      agree := by
        intro i
        have he : e.1 = port hfit j := by
          apply Fin.ext
          rfl
        rw [he]
        exact internal_agree hw hfit cap S j i }
  else
    { conf := rawStep hfit hw cap S.conf e.1
      line := S.line
      agree := external_agree hw hfit cap S e.1 e.2 h }

@[simp] theorem safeStep_conf {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (S : State hw hfit)
    (e : SafeEdge hfit) :
    (safeStep hw hfit cap S e).conf =
      rawStep hfit hw cap S.conf e.1 := by
  unfold safeStep
  split <;> rfl

/-- Internal-port projection of a safe raw word; all other raw letters stutter. -/
def lineWord {w n : Nat} (hfit : w < n) :
    List (SafeEdge hfit) → List (Fin (w - 1))
  | [] => []
  | e :: es =>
      if h : e.1.val < w - 1 then
        ⟨e.1.val, h⟩ :: lineWord hfit es
      else
        lineWord hfit es

/-- The original raw Fin-n word, with no relabeling. -/
def eraseWord {w n : Nat} (hfit : w < n)
    (es : List (SafeEdge hfit)) : List (Fin n) :=
  es.map Subtype.val

def safeRun {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) : State hw hfit → List (SafeEdge hfit) → State hw hfit
  | S, [] => S
  | S, e :: es =>
      safeRun hw hfit cap (safeStep hw hfit cap S e) es

def rawRun {w n : Nat} (hfit : w < n) (hwidth : 2 ≤ w)
    (cap : Nat) :
    (Fin n → AgentState w) → List (Fin n) → Fin n → AgentState w
  | C, [] => C
  | C, e :: es =>
      rawRun hfit hwidth cap (rawStep hfit hwidth cap C e) es

theorem safeRun_line {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (S : State hw hfit) (es : List (SafeEdge hfit)) :
    (safeRun hw hfit cap S es).line =
      Line.run cap S.line (lineWord hfit es) := by
  induction es generalizing S with
  | nil => rfl
  | cons e es ih =>
    by_cases h : e.1.val < w - 1
    · simp only [safeRun, lineWord, dif_pos h, safeStep, ih, Line.run]
    · simp only [safeRun, lineWord, dif_neg h, safeStep, ih]

theorem safeRun_conf {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (S : State hw hfit) (es : List (SafeEdge hfit)) :
    (safeRun hw hfit cap S es).conf =
      rawRun hfit hw cap S.conf (eraseWord hfit es) := by
  induction es generalizing S with
  | nil => rfl
  | cons e es ih =>
    change
      (safeRun hw hfit cap (safeStep hw hfit cap S e) es).conf =
        rawRun hfit hw cap
          (rawStep hfit hw cap S.conf e.1)
          (eraseWord hfit es)
    rw [← safeStep_conf hw hfit cap S e]
    exact ih (safeStep hw hfit cap S e)

theorem lineWord_map_safePort {w n : Nat} (hfit : w < n)
    (xs : List (Fin (w - 1))) :
    lineWord hfit (xs.map (safePort hfit)) = xs := by
  induction xs with
  | nil => rfl
  | cons j js ih =>
    have hj : (safePort hfit j).1.val < w - 1 := j.isLt
    simp only [List.map_cons, lineWord, dif_pos hj]
    have he :
        (⟨(safePort hfit j).1.val, hj⟩ : Fin (w - 1)) = j := by
      apply Fin.ext
      rfl
    rw [he, ih]

/-- Exact raw physical service word. Its length is `3*2^(w-1)-2`. -/
def hitWord {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) :
    List (SafeEdge hfit) :=
  (Line.hitPattern hw).map (safePort hfit)

theorem hitWord_projects {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) :
    lineWord hfit (hitWord hw hfit) = Line.hitPattern hw := by
  exact lineWord_map_safePort hfit (Line.hitPattern hw)

theorem hitWord_length {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) :
    (hitWord hw hfit).length + 2 = 3 * 2 ^ (w - 1) := by
  simpa only [hitWord, List.length_map] using
    Line.hitPattern_length (hw := hw)

theorem hitWord_length_eq {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) :
    (hitWord hw hfit).length = 3 * 2 ^ (w - 1) - 2 := by
  have h := hitWord_length hw hfit
  omega

/-- The line terminal count is literally the physical count field. -/
def physicalTerminalCount {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (S : State hw hfit) : Nat :=
  (S.conf (site hfit (Line.last hw))).count

theorem physicalTerminalCount_eq {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (S : State hw hfit) :
    physicalTerminalCount hw hfit S = Line.terminalCount S.line := by
  unfold physicalTerminalCount Line.terminalCount
  exact (congrArg AgentState.count (S.agree (Line.last hw))).symm

/-- Any safe raw word whose projection contains the service pattern increases
that same physical terminal count. -/
theorem safe_word_hit {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (S : State hw hfit) (es : List (SafeEdge hfit))
    (hc : physicalTerminalCount hw hfit S < cap)
    (hsub : (Line.hitPattern hw).Sublist (lineWord hfit es)) :
    physicalTerminalCount hw hfit S <
      physicalTerminalCount hw hfit (safeRun hw hfit cap S es) := by
  have hc' : Line.terminalCount S.line < cap := by
    simpa only [physicalTerminalCount_eq] using hc
  rw [physicalTerminalCount_eq hw hfit S,
    physicalTerminalCount_eq hw hfit (safeRun hw hfit cap S es),
    safeRun_line hw hfit cap S es]
  exact Line.hitPattern_forces_increase cap S.line (lineWord hfit es)
    hc' hsub

/-- Exact physical correspondence to the original Fin-n raw word. -/
theorem safe_word_raw_terminal {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (S : State hw hfit)
    (es : List (SafeEdge hfit)) :
    physicalTerminalCount hw hfit (safeRun hw hfit cap S es) =
      (rawRun hfit hw cap S.conf (eraseWord hfit es)
        (site hfit (Line.last hw))).count := by
  unfold physicalTerminalCount
  rw [safeRun_conf hw hfit cap S es]

/-- A direct finite raw ring witness using exactly the recursive service word. -/
theorem hitWord_raw_increase {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (S : State hw hfit)
    (hc : physicalTerminalCount hw hfit S < cap) :
    (S.conf (site hfit (Line.last hw))).count <
      (rawRun hfit hw cap S.conf (eraseWord hfit (hitWord hw hfit))
        (site hfit (Line.last hw))).count := by
  have hi := safe_word_hit hw hfit cap S (hitWord hw hfit) hc (by
    rw [hitWord_projects hw hfit]
    exact List.Sublist.refl _)
  have hr := safe_word_raw_terminal hw hfit cap S (hitWord hw hfit)
  rw [hr] at hi
  change (S.conf (site hfit (Line.last hw))).count < _ at hi
  exact hi

/-- Convert an original raw word avoiding the reset edge into safe letters. -/
def liftWord {w n : Nat} (hfit : w < n) :
    (es : List (Fin n)) → rootIncoming hfit ∉ es → List (SafeEdge hfit)
  | [], _ => []
  | e :: es, h =>
      ⟨e, fun he => h (by subst e; simp)⟩ ::
        liftWord hfit es (fun hm => h (List.mem_cons_of_mem e hm))

theorem erase_liftWord {w n : Nat} (hfit : w < n)
    (es : List (Fin n)) (h : rootIncoming hfit ∉ es) :
    eraseWord hfit (liftWord hfit es h) = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [liftWord, eraseWord, List.map_cons]
    congr 1
    exact ih _

/-- Deterministic internal-port projection of an original raw Fin-n word. -/
def projectRawWord {w n : Nat} (hfit : w < n)
    (es : List (Fin n)) (h : rootIncoming hfit ∉ es) :
    List (Fin (w - 1)) :=
  lineWord hfit (liftWord hfit es h)

/-- Main producer for the matcher consumer: no scheduler is filtered or
renormalized. -/
theorem raw_word_hit {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (S : State hw hfit) (es : List (Fin n))
    (hkill : rootIncoming hfit ∉ es)
    (hc : (S.conf (site hfit (Line.last hw))).count < cap)
    (hsub : (Line.hitPattern hw).Sublist
      (projectRawWord hfit es hkill)) :
    (S.conf (site hfit (Line.last hw))).count <
      (rawRun hfit hw cap S.conf es
        (site hfit (Line.last hw))).count := by
  have hs : (Line.hitPattern hw).Sublist
      (lineWord hfit (liftWord hfit es hkill)) := by
    simpa only [projectRawWord] using hsub
  have hc' : physicalTerminalCount hw hfit S < cap := by
    simpa only [physicalTerminalCount] using hc
  have hi := safe_word_hit hw hfit cap S
    (liftWord hfit es hkill) hc' hs
  have hr := safe_word_raw_terminal hw hfit cap S
    (liftWord hfit es hkill)
  rw [hr] at hi
  have he := erase_liftWord hfit es hkill
  rw [he] at hi
  change (S.conf (site hfit (Line.last hw))).count < _ at hi
  exact hi

end BirthWaitClockMass.RawRing

#print axioms BirthWaitClockMass.RawRing.port_eq_site_left
#print axioms BirthWaitClockMass.RawRing.site_last_eq_terminal
#print axioms BirthWaitClockMass.RawRing.port_ne_rootIncoming
#print axioms BirthWaitClockMass.RawRing.terminalOutgoing_ne_rootIncoming
#print axioms BirthWaitClockMass.RawRing.right_of_safe
#print axioms BirthWaitClockMass.RawRing.right_ne_self_of_safe
#print axioms BirthWaitClockMass.RawRing.right_port
#print axioms BirthWaitClockMass.RawRing.rawStep_initiator
#print axioms BirthWaitClockMass.RawRing.rawStep_responder
#print axioms BirthWaitClockMass.RawRing.safeStep_conf
#print axioms BirthWaitClockMass.RawRing.safeRun_line
#print axioms BirthWaitClockMass.RawRing.safeRun_conf
#print axioms BirthWaitClockMass.RawRing.lineWord_map_safePort
#print axioms BirthWaitClockMass.RawRing.hitWord_projects
#print axioms BirthWaitClockMass.RawRing.hitWord_length
#print axioms BirthWaitClockMass.RawRing.hitWord_length_eq
#print axioms BirthWaitClockMass.RawRing.physicalTerminalCount_eq
#print axioms BirthWaitClockMass.RawRing.safe_word_hit
#print axioms BirthWaitClockMass.RawRing.safe_word_raw_terminal
#print axioms BirthWaitClockMass.RawRing.hitWord_raw_increase
#print axioms BirthWaitClockMass.RawRing.erase_liftWord
#print axioms BirthWaitClockMass.RawRing.raw_word_hit
