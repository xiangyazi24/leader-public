import Leader.Wu.Birth.ShortDoneTerminalPassiveLocalTripleCount
import Leader.Wu.Birth.ShortWaitTerminalEntryProducer

namespace BirthShortDoneTerminalPassiveLocal3Producer

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWait BirthShortWaitProjection
open BirthWaitClockMass BirthWaitClockMass.Line
open BirthWaitClockMass.RawRing BirthWaitClockMass.ResetEntry
open BirthShortWaitDomainWitness BirthShortWaitRawRing
open BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Count
open FiniteUniformStoppingTree ControlledSchedulerMass

set_option autoImplicit false
set_option pp.structureInstances false

variable {psi kappa tau n : Nat}

/-- Root half of the width-two completed WAIT domain. -/
def RootClear3 (hn : 4 <= n) (C : FC n psi kappa tau) : Prop :=
  (raw (C (p0 hn))).reset = false /\
  (raw (C (p0 hn))).carry = false

/-- Real reached entry target: the raw projection of this actual full-host
configuration packages as the existing corrected width-two raw-ring State. -/
def OrderedWaitEntry2 (hn : 4 <= n) (C : FC n psi kappa tau) : Prop :=
  exists S : BirthShortWaitRawRing.State (psi := psi)
      (by decide : 2 <= 2) (by omega : 2 < n),
    S.conf = fun x => raw (C x)

def LocalWaitEntry2 (hpsi : 0 < psi) (hn : 4 <= n)
    (C : FC n psi kappa tau) : Prop :=
  LocalLine3 hpsi hn C /\ OrderedWaitEntry2 hn C

private theorem line2_label (hpsi : 0 < psi) (hn : 4 <= n)
    (hfit : 2 < n) (C : FC n psi kappa tau)
    (h : LocalLine3 hpsi hn C) (i : Fin 2) :
    (raw (C (site hfit i))).label.val = i.val := by
  have hi : i.val = 0 \/ i.val = 1 := by omega
  rcases hi with hi | hi
  · have hs : site hfit i = p0 hn := by
      apply Fin.ext
      exact hi
    rw [hs, h.lab0]
    omega
  · have hs : site hfit i = p1 hn := by
      apply Fin.ext
      exact hi
    rw [hs, h.lab1]
    omega

/-- Four literal physical WAIT fields are exactly enough to package the
reached full host as the existing width-two raw-ring entry state. -/
private theorem ordered_of_clears (hpsi : 0 < psi) (hn : 4 <= n)
    (C : FC n psi kappa tau) (hline : LocalLine3 hpsi hn C)
    (hz0 : (raw (C (p0 hn))).reset = false)
    (hc0 : (raw (C (p0 hn))).carry = false)
    (hz1 : (raw (C (p1 hn))).reset = false)
    (hc1 : (raw (C (p1 hn))).carry = false) :
    OrderedWaitEntry2 hn C := by
  unfold OrderedWaitEntry2
  let hfit : 2 < n := by omega
  have hlab : forall i : Fin 2,
      (raw (C (site hfit i))).label.val = i.val :=
    line2_label hpsi hn hfit C hline
  have hlt (i : Fin 2) : (raw (C (site hfit i))).label.val < 2 := by
    rw [hlab i]
    exact i.isLt
  let L : BirthWaitClockMass.Line (by decide : 2 <= 2) := {
    cell := fun i => waitPrefixProject (raw (C (site hfit i))) (hlt i)
    label := by
      intro i
      apply Fin.ext
      simpa only [waitPrefixProject_label_val] using hlab i
    reset_clear := by
      intro i
      have hi : i.val = 0 \/ i.val = 1 := by omega
      rcases hi with hi | hi
      · have hs : site hfit i = p0 hn := by apply Fin.ext; exact hi
        simpa only [waitPrefixProject_reset, hs] using hz0
      · have hs : site hfit i = p1 hn := by apply Fin.ext; exact hi
        simpa only [waitPrefixProject_reset, hs] using hz1
    root_carry := by
      have hs : site hfit (Line.first (by decide : 2 <= 2)) = p0 hn := by
        apply Fin.ext
        rfl
      simpa only [waitPrefixProject_carry, hs] using hc0
    terminal_carry := by
      have hs : site hfit (Line.last (by decide : 2 <= 2)) = p1 hn := by
        apply Fin.ext
        rfl
      simpa only [waitPrefixProject_carry, hs] using hc1 }
  let S : BirthShortWaitRawRing.State (psi := psi)
      (by decide : 2 <= 2) hfit := {
    conf := fun x => raw (C x)
    line := L
    agree := by
      intro i
      unfold BirthShortWaitRawRing.KeyAgree
      dsimp only [L]
      rw [WaitKey_of_waitPrefixProject] }
  exact ⟨S, rfl⟩

private theorem safe_p0 (hn : 4 <= n) : SafeLine3Edge hn (p0 hn) := by
  constructor
  · exact Fin.ne_of_val_ne (by simp [p0, p2])
  · exact Fin.ne_of_val_ne (by simp [p0, leftCross]; omega)

private theorem safe_p1 (hn : 4 <= n) : SafeLine3Edge hn (p1 hn) := by
  constructor
  · exact Fin.ne_of_val_ne (by simp [p1, p2])
  · exact Fin.ne_of_val_ne (by simp [p1, leftCross]; omega)

/-- Active width-two source labels 0,1 make the repaired row identical to the
old active-prefix WAIT row, whose initiator clears reset/carry. -/
private theorem active_left_clear2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (l r : AgentState psi)
    (hl : l.label.val = 0) (hr : r.label.val = 1) :
    let q := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r
    q.1.reset = false /\ q.1.carry = false := by
  dsimp only
  have hl2 : l.label.val < 2 := by omega
  have hr2 : r.label.val < 2 := by omega
  rw [waitWidthEntry_eq_old_of_active_labels
    hpsi (by decide : 0 < 2) h2 kappa l r hl2 hr2]
  have hp := waitWidth_regs_eq_waitSaturated_prefix
    (kappa := kappa) hpsi (by decide : 0 < 2) h2 l r hl2 hr2
  have hs := BirthWaitClockMass.ResetEntry.wait_initiator_clear
    (by decide : 0 < 2) kappa
    (waitPrefixProject l hl2) (waitPrefixProject r hr2)
  have hL := congrArg Prod.fst hp
  constructor
  · have h := congrArg WaitRegs.reset hL
    simpa only [waitRegsPair, WaitRegs.ofState] using h.trans hs.1
  · have h := congrArg WaitRegs.carry hL
    simpa only [waitRegsPair, WaitRegs.ofState] using h.trans hs.2

private theorem terminal_left_clear2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (l r : AgentState psi) (hl : l.label.val = 1) :
    let q := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r
    q.1.reset = false /\ q.1.carry = false := by
  have ht : l.label = widthTerminal (by decide : 0 < 2) h2 := by
    apply Fin.ext
    simpa [widthTerminal] using hl
  exact waitWidthEntry_terminal_initiator_clear
    hpsi (by decide : 2 <= 2) h2 kappa l r ht

private theorem p0_clear_of_projection (hpsi : 0 < psi) (h2 : 2 <= psi)
    (hn : 4 <= n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (hline : LocalLine3 hpsi hn C)
    (hp : RowProjection2 hpsi h2 kappa tau ring C (p0 hn)) :
    RootClear3 hn (hostStep hpsi h2 ring C (p0 hn)) := by
  let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa
    (raw (C (p0 hn))) (raw (C (p1 hn)))
  let q := BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2
    (C (p0 hn)) (C (p1 hn))
  have hp' := hp
  unfold RowProjection2 at hp'
  simp only [right_p0] at hp'
  change clock (raw q.1) = clock w.1 /\ clock (raw q.2) = clock w.2 at hp'
  have hc := active_left_clear2 hpsi h2 kappa
    (raw (C (p0 hn))) (raw (C (p1 hn))) hline.lab0 hline.lab1
  change w.1.reset = false /\ w.1.carry = false at hc
  have hz := congrArg (fun z : Clock psi => z.reset) hp'.1
  have hk := congrArg (fun z : Clock psi => z.carry) hp'.1
  change (raw q.1).reset = w.1.reset at hz
  change (raw q.1).carry = w.1.carry at hk
  have hout : (raw q.1).reset = false /\ (raw q.1).carry = false :=
    ⟨hz.trans hc.1, hk.trans hc.2⟩
  unfold RootClear3
  rw [hostStep_left]
  simpa only [right_p0, q] using hout

private theorem p1_clear_of_projection (hpsi : 0 < psi) (h2 : 2 <= psi)
    (hn : 4 <= n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (hline : LocalLine3 hpsi hn C)
    (hp : RowProjection2 hpsi h2 kappa tau ring C (p1 hn)) :
    let C' := hostStep hpsi h2 ring C (p1 hn)
    (raw (C' (p1 hn))).reset = false /\
      (raw (C' (p1 hn))).carry = false := by
  let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa
    (raw (C (p1 hn))) (raw (C (p2 hn)))
  let q := BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2
    (C (p1 hn)) (C (p2 hn))
  have hp' := hp
  unfold RowProjection2 at hp'
  simp only [right_p1] at hp'
  change clock (raw q.1) = clock w.1 /\ clock (raw q.2) = clock w.2 at hp'
  have hc := terminal_left_clear2 hpsi h2 kappa
    (raw (C (p1 hn))) (raw (C (p2 hn))) hline.lab1
  change w.1.reset = false /\ w.1.carry = false at hc
  have hz := congrArg (fun z : Clock psi => z.reset) hp'.1
  have hk := congrArg (fun z : Clock psi => z.carry) hp'.1
  change (raw q.1).reset = w.1.reset at hz
  change (raw q.1).carry = w.1.carry at hk
  dsimp only
  rw [hostStep_left]
  simpa only [right_p1, q] using And.intro (hz.trans hc.1) (hk.trans hc.2)

private theorem root_preserved_p1 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (hn : 4 <= n) (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hroot : RootClear3 hn C) :
    RootClear3 hn (hostStep hpsi h2 ring C (p1 hn)) := by
  have h01 : p0 hn ≠ p1 hn := Fin.ne_of_val_ne (by simp [p0, p1])
  have h02 : p0 hn ≠ ring.rightNeighbor (p1 hn) := by
    simpa only [right_p1] using Fin.ne_of_val_ne (by simp [p0, p2])
  unfold RootClear3 at hroot ⊢
  rw [hostStep_other hpsi h2 ring C (p1 hn) (p0 hn) h01 h02]
  exact hroot

private theorem root_preserved_outside (hpsi : 0 < psi) (h2 : 2 <= psi)
    (hn : 4 <= n) (ring : DirectedRing n) (C : FC n psi kappa tau)
    (e : Fin n) (hsafe : SafeLine3Edge hn e)
    (hout : ¬ (InternalLine3Edge hn e)) (hroot : RootClear3 hn C) :
    RootClear3 hn (hostStep hpsi h2 ring C e) := by
  have he0 : e ≠ p0 hn := fun h => hout (Or.inl h)
  have hlast : e.val ≠ n - 1 := by
    intro hv
    apply hsafe.2
    apply Fin.ext
    simpa [leftCross] using hv
  have hr : (ring.rightNeighbor e).val = e.val + 1 := by
    change (e.val + 1) % n = e.val + 1
    exact Nat.mod_eq_of_lt (by have := e.isLt; omega)
  have h0r : p0 hn ≠ ring.rightNeighbor e := by
    intro h
    have hv := congrArg Fin.val h
    rw [hr] at hv
    simp only [p0] at hv
    omega
  unfold RootClear3 at hroot ⊢
  rw [hostStep_other hpsi h2 ring C e (p0 hn) (Ne.symm he0) h0r]
  exact hroot

private theorem p0_step (hpsi : 0 < psi) (h2 : 2 <= psi)
    (hn : 4 <= n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (hline : LocalLine3 hpsi hn C)
    (hpre : RowPreCap2 hpsi h2 kappa ring C (p0 hn)) :
    let C' := hostStep hpsi h2 ring C (p0 hn)
    LocalLine3 hpsi hn C' /\
      RowProjection2 hpsi h2 kappa tau ring C (p0 hn) /\ RootClear3 hn C' := by
  dsimp only
  have hs := local3_one_step hpsi h2 hn kappa tau ring C (p0 hn)
    hline (safe_p0 hn) (fun _ => hpre)
  have hp := hs.2 (Or.inl rfl)
  exact ⟨hs.1, hp, p0_clear_of_projection hpsi h2 hn kappa tau ring C hline hp⟩

private theorem p1_entry_step (hpsi : 0 < psi) (h2 : 2 <= psi)
    (hn : 4 <= n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (hline : LocalLine3 hpsi hn C)
    (hroot : RootClear3 hn C)
    (hpre : RowPreCap2 hpsi h2 kappa ring C (p1 hn)) :
    let C' := hostStep hpsi h2 ring C (p1 hn)
    RowProjection2 hpsi h2 kappa tau ring C (p1 hn) /\ LocalWaitEntry2 hpsi hn C' := by
  dsimp only
  have hs := local3_one_step hpsi h2 hn kappa tau ring C (p1 hn)
    hline (safe_p1 hn) (fun _ => hpre)
  have hp := hs.2 (Or.inr rfl)
  have ht := p1_clear_of_projection hpsi h2 hn kappa tau ring C hline hp
  dsimp only at ht
  have hr := root_preserved_p1 hpsi h2 hn ring C hroot
  have he := ordered_of_clears hpsi hn
    (hostStep hpsi h2 ring C (p1 hn)) hs.1 hr.1 hr.2 ht.1 ht.2
  exact ⟨hp, hs.1, he⟩

/-- Current internal cap endpoint. No row is executed in this branch. -/
def Local3CapNow (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (C : FC n psi kappa tau)
    (e : Fin n) : Prop :=
  LocalLine3 hpsi hn C /\ SafeLine3Edge hn e /\ InternalLine3Edge hn e /\
    RowCap2 hpsi h2 kappa ring C e

/-- Physical suffix after an actual p0 has already occurred pre-cap. -/
def Local3AfterP0 (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) :
    FC n psi kappa tau -> List (Fin n) -> Prop
  | _, [] => False
  | C, e :: es =>
      Local3CapNow hpsi h2 hn kappa tau ring C e \/
      (e = p1 hn /\ LocalLine3 hpsi hn C /\
        RowPreCap2 hpsi h2 kappa ring C e /\
        RowProjection2 hpsi h2 kappa tau ring C e /\
        LocalWaitEntry2 hpsi hn (hostStep hpsi h2 ring C e)) \/
      (e = p0 hn /\ LocalLine3 hpsi hn C /\
        RowPreCap2 hpsi h2 kappa ring C e /\
        RowProjection2 hpsi h2 kappa tau ring C e /\
        Local3AfterP0 hpsi h2 hn kappa tau ring
          (hostStep hpsi h2 ring C e) es) \/
      (SafeLine3Edge hn e /\ ¬ (InternalLine3Edge hn e) /\
        LocalLine3 hpsi hn C /\
        Local3AfterP0 hpsi h2 hn kappa tau ring
          (hostStep hpsi h2 ring C e) es)

/-- Actual host-prefix event. Cap branches stop before the cap row. Entry can
only occur in `Local3AfterP0`, so the physical p0 row precedes the final p1 row. -/
def Local3EntryOrCap (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) :
    FC n psi kappa tau -> List (Fin n) -> Prop
  | _, [] => False
  | C, e :: es =>
      Local3CapNow hpsi h2 hn kappa tau ring C e \/
      (e = p0 hn /\ LocalLine3 hpsi hn C /\
        RowPreCap2 hpsi h2 kappa ring C e /\
        RowProjection2 hpsi h2 kappa tau ring C e /\
        Local3AfterP0 hpsi h2 hn kappa tau ring
          (hostStep hpsi h2 ring C e) es) \/
      (e = p1 hn /\ LocalLine3 hpsi hn C /\
        RowPreCap2 hpsi h2 kappa ring C e /\
        RowProjection2 hpsi h2 kappa tau ring C e /\
        Local3EntryOrCap hpsi h2 hn kappa tau ring
          (hostStep hpsi h2 ring C e) es) \/
      (SafeLine3Edge hn e /\ ¬ (InternalLine3Edge hn e) /\
        LocalLine3 hpsi hn C /\
        Local3EntryOrCap hpsi h2 hn kappa tau ring
          (hostStep hpsi h2 ring C e) es)

private theorem twoCross_false_eq (hn : 4 <= n) (e : Fin n) :
    twoCrossStep hn false e =
      if e = p0 hn then .active true
      else if e = p2 hn then .failure
      else if e = leftCross hn then .failure
      else .active false := by rfl

private theorem twoCross_true_eq (hn : 4 <= n) (e : Fin n) :
    twoCrossStep hn true e =
      if e = p1 hn then .success
      else if e = p2 hn then .failure
      else if e = leftCross hn then .failure
      else .active true := by rfl

private theorem after_success (hpsi : 0 < psi) (h2 : 2 <= psi)
    (hn : 4 <= n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (hline : LocalLine3 hpsi hn C)
    (hroot : RootClear3 hn C) (es : List (Fin n))
    (hs : runWord (twoCrossStep hn) (.active true) es = .success) :
    Local3AfterP0 hpsi h2 hn kappa tau ring C es := by
  induction es generalizing C with
  | nil => simpa [runWord] using hs
  | cons e es ih =>
      simp only [runWord, stepNode] at hs
      rw [twoCross_true_eq] at hs
      by_cases h1 : e = p1 hn
      · subst e
        rw [if_pos rfl] at hs
        by_cases hc : RowCap2 hpsi h2 kappa ring C (p1 hn)
        · exact Or.inl ⟨hline, safe_p1 hn, Or.inr rfl, hc⟩
        · have hp : RowPreCap2 hpsi h2 kappa ring C (p1 hn) := by
            exact hc
          have he := p1_entry_step hpsi h2 hn kappa tau ring C hline hroot hp
          dsimp only at he
          exact Or.inr (Or.inl ⟨rfl, hline, hp, he.1, he.2⟩)
      · rw [if_neg h1] at hs
        by_cases h2e : e = p2 hn
        · subst e
          rw [if_pos rfl] at hs
          have hf : False := by simpa [runWord] using hs
          exact hf.elim
        · rw [if_neg h2e] at hs
          by_cases hl : e = leftCross hn
          · subst e
            rw [if_pos rfl] at hs
            have hf : False := by simpa [runWord] using hs
            exact hf.elim
          · rw [if_neg hl] at hs
            by_cases h0 : e = p0 hn
            · subst e
              by_cases hc : RowCap2 hpsi h2 kappa ring C (p0 hn)
              · exact Or.inl ⟨hline, safe_p0 hn, Or.inl rfl, hc⟩
              · have hp : RowPreCap2 hpsi h2 kappa ring C (p0 hn) := by
                  exact hc
                have hx := p0_step hpsi h2 hn kappa tau ring C hline hp
                dsimp only at hx
                have hnxt := ih (C := hostStep hpsi h2 ring C (p0 hn))
                  hx.1 hx.2.2 hs
                exact Or.inr (Or.inr (Or.inl
                  ⟨rfl, hline, hp, hx.2.1, hnxt⟩))
            · have hsafe : SafeLine3Edge hn e := ⟨h2e, hl⟩
              have hout : ¬ (InternalLine3Edge hn e) := by
                intro hi
                rcases hi with hi | hi
                · exact h0 hi
                · exact h1 hi
              have hx := local3_one_step hpsi h2 hn kappa tau ring C e
                hline hsafe (fun hi => (hout hi).elim)
              have hr := root_preserved_outside hpsi h2 hn ring C e
                hsafe hout hroot
              have hnxt := ih (C := hostStep hpsi h2 ring C e) hx.1 hr hs
              exact Or.inr (Or.inr (Or.inr ⟨hsafe, hout, hline, hnxt⟩))

private theorem before_success (hpsi : 0 < psi) (h2 : 2 <= psi)
    (hn : 4 <= n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (hline : LocalLine3 hpsi hn C)
    (es : List (Fin n))
    (hs : runWord (twoCrossStep hn) (.active false) es = .success) :
    Local3EntryOrCap hpsi h2 hn kappa tau ring C es := by
  induction es generalizing C with
  | nil => simpa [runWord] using hs
  | cons e es ih =>
      simp only [runWord, stepNode] at hs
      rw [twoCross_false_eq] at hs
      by_cases h0 : e = p0 hn
      · subst e
        rw [if_pos rfl] at hs
        by_cases hc : RowCap2 hpsi h2 kappa ring C (p0 hn)
        · exact Or.inl ⟨hline, safe_p0 hn, Or.inl rfl, hc⟩
        · have hp : RowPreCap2 hpsi h2 kappa ring C (p0 hn) := by exact hc
          have hx := p0_step hpsi h2 hn kappa tau ring C hline hp
          dsimp only at hx
          have hnxt := after_success hpsi h2 hn kappa tau ring
            (hostStep hpsi h2 ring C (p0 hn)) hx.1 hx.2.2 es hs
          exact Or.inr (Or.inl ⟨rfl, hline, hp, hx.2.1, hnxt⟩)
      · rw [if_neg h0] at hs
        by_cases h2e : e = p2 hn
        · subst e
          rw [if_pos rfl] at hs
          have hf : False := by simpa [runWord] using hs
          exact hf.elim
        · rw [if_neg h2e] at hs
          by_cases hl : e = leftCross hn
          · subst e
            rw [if_pos rfl] at hs
            have hf : False := by simpa [runWord] using hs
            exact hf.elim
          · rw [if_neg hl] at hs
            by_cases h1 : e = p1 hn
            · subst e
              by_cases hc : RowCap2 hpsi h2 kappa ring C (p1 hn)
              · exact Or.inl ⟨hline, safe_p1 hn, Or.inr rfl, hc⟩
              · have hp : RowPreCap2 hpsi h2 kappa ring C (p1 hn) := by exact hc
                have hx := local3_one_step hpsi h2 hn kappa tau ring C (p1 hn)
                  hline (safe_p1 hn) (fun _ => hp)
                have hproj := hx.2 (Or.inr rfl)
                have hnxt := ih (C := hostStep hpsi h2 ring C (p1 hn)) hx.1 hs
                exact Or.inr (Or.inr (Or.inl
                  ⟨rfl, hline, hp, hproj, hnxt⟩))
            · have hsafe : SafeLine3Edge hn e := ⟨h2e, hl⟩
              have hout : ¬ (InternalLine3Edge hn e) := by
                intro hi
                rcases hi with hi | hi
                · exact h0 hi
                · exact h1 hi
              have hx := local3_one_step hpsi h2 hn kappa tau ring C e
                hline hsafe (fun hi => (hout hi).elim)
              have hnxt := ih (C := hostStep hpsi h2 ring C e) hx.1 hs
              exact Or.inr (Or.inr (Or.inr ⟨hsafe, hout, hline, hnxt⟩))

/-- Every successful word of the original two-cross matcher has an actual
TerminalHost prefix that either stops at the current positive cap (without
executing it) or reaches the real ordered width-two WAIT entry domain. -/
theorem twoCross_success_entry_or_cap
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (hline : LocalLine3 hpsi hn C)
    (es : List (Fin n))
    (hs : runWord (twoCrossStep hn) (.active false) es = .success) :
    Local3EntryOrCap hpsi h2 hn kappa tau ring C es :=
  before_success hpsi h2 hn kappa tau ring C hline es hs

#print axioms BirthShortDoneTerminalPassiveLocal3Producer.twoCross_success_entry_or_cap

end BirthShortDoneTerminalPassiveLocal3Producer
