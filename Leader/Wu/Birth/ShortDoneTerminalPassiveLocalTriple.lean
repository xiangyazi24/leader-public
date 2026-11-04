import Leader.Wu.Birth.ShortDoneTerminalPassiveCyclicScope

namespace BirthShortDoneTerminalPassiveLocal3

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWait BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR1 BirthShortDoneTerminalPassiveR3
open BirthShortDoneTerminalPassiveR4 BirthShortDoneTerminalPassiveR5
open BirthShortDoneTerminalPassiveScopeAudit

set_option autoImplicit false
set_option pp.structureInstances false

variable {psi kappa tau n : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthShortDoneTerminalPassiveR4.FullConfig n psi kappa tau

def p0 (hn : 4 ≤ n) : Fin n := ⟨0, by omega⟩
def p1 (hn : 4 ≤ n) : Fin n := ⟨1, by omega⟩
def p2 (hn : 4 ≤ n) : Fin n := ⟨2, by omega⟩
def p3 (hn : 4 ≤ n) : Fin n := ⟨3, by omega⟩
def leftCross (hn : 4 ≤ n) : Fin n := ⟨n - 1, by omega⟩

@[simp] theorem right_p0 (hn : 4 ≤ n) (ring : DirectedRing n) :
    ring.rightNeighbor (p0 hn) = p1 hn := by
  apply Fin.ext
  change (0 + 1) % n = 1
  exact Nat.mod_eq_of_lt (by omega)

@[simp] theorem right_p1 (hn : 4 ≤ n) (ring : DirectedRing n) :
    ring.rightNeighbor (p1 hn) = p2 hn := by
  apply Fin.ext
  change (1 + 1) % n = 2
  exact Nat.mod_eq_of_lt (by omega)

@[simp] theorem right_p2 (hn : 4 ≤ n) (ring : DirectedRing n) :
    ring.rightNeighbor (p2 hn) = p3 hn := by
  apply Fin.ext
  change (2 + 1) % n = 3
  exact Nat.mod_eq_of_lt (by omega)

@[simp] theorem right_leftCross (hn : 4 ≤ n) (ring : DirectedRing n) :
    ring.rightNeighbor (leftCross hn) = p0 hn := by
  apply Fin.ext
  change (n - 1 + 1) % n = 0
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]

structure LocalLine3 (hpsi : 0 < psi) (hn : 4 ≤ n)
    (C : FC n psi kappa tau) : Prop where
  pass0 : Passive (raw (C (p0 hn)))
  pass1 : Passive (raw (C (p1 hn)))
  pass2 : Passive (raw (C (p2 hn)))
  lab0 : (raw (C (p0 hn))).label.val = 0
  lab1 : (raw (C (p1 hn))).label.val = 1
  lab2 : (raw (C (p2 hn))).label.val = 2 % psi

/-- Exactly excludes `2→3` and `(n-1)→0`. -/
def SafeLine3Edge (hn : 4 ≤ n) (e : Fin n) : Prop :=
  e ≠ p2 hn ∧ e ≠ leftCross hn

def InternalLine3Edge (hn : 4 ≤ n) (e : Fin n) : Prop :=
  e = p0 hn ∨ e = p1 hn

private theorem localEdge0 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (hn : 4 ≤ n) (ring : DirectedRing n) (C : FC n psi kappa tau)
    (h : LocalLine3 hpsi hn C) :
    LocalPassiveEdge2 hpsi ring C (p0 hn) := by
  refine ⟨h.pass0, ?_, ?_⟩
  · simpa only [right_p0] using h.pass1
  · rw [right_p0]
    apply Fin.ext
    change (raw (C (p1 hn))).label.val =
      ((raw (C (p0 hn))).label.val + 1) % psi
    rw [h.lab1, h.lab0]
    simpa using (Nat.mod_eq_of_lt (by omega : 1 < psi)).symm

private theorem localEdge1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (hn : 4 ≤ n) (ring : DirectedRing n) (C : FC n psi kappa tau)
    (h : LocalLine3 hpsi hn C) :
    LocalPassiveEdge2 hpsi ring C (p1 hn) := by
  refine ⟨h.pass1, ?_, ?_⟩
  · simpa only [right_p1] using h.pass2
  · rw [right_p1]
    apply Fin.ext
    change (raw (C (p2 hn))).label.val =
      ((raw (C (p1 hn))).label.val + 1) % psi
    rw [h.lab2, h.lab1]

private theorem step0 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (hn : 4 ≤ n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (hline : LocalLine3 hpsi hn C)
    (hpre : RowPreCap2 hpsi h2 kappa ring C (p0 hn)) :
    LocalLine3 hpsi hn (hostStep hpsi h2 ring C (p0 hn)) ∧
      RowProjection2 hpsi h2 kappa tau ring C (p0 hn) := by
  have hs := local_row2_preCap hpsi h2 kappa tau ring C (p0 hn)
    (localEdge0 hpsi h2 hn ring C hline) hpre
  let q := BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2
    (C (p0 hn)) (C (ring.rightNeighbor (p0 hn)))
  change RowProjection2 hpsi h2 kappa tau ring C (p0 hn) ∧
    Passive (raw q.1) ∧ Passive (raw q.2) at hs
  have h10 : p1 hn ≠ p0 hn := Fin.ne_of_val_ne (by simp [p1, p0])
  have h20 : p2 hn ≠ p0 hn := Fin.ne_of_val_ne (by simp [p2, p0])
  have h21 : p2 hn ≠ p1 hn := Fin.ne_of_val_ne (by simp [p2, p1])
  have hne : ring.rightNeighbor (p0 hn) ≠ p0 hn := by
    simpa only [right_p0] using h10
  have hf := hostStep_label_frame_of_projection hpsi h2
    (by omega : 2 ≤ n) kappa tau ring C (p0 hn) hs.1
  have hp0 : Passive (raw (hostStep hpsi h2 ring C (p0 hn) (p0 hn))) := by
    rw [hostStep_left]
    simpa [q] using hs.2.1
  have hp1 : Passive (raw (hostStep hpsi h2 ring C (p0 hn) (p1 hn))) := by
    rw [← right_p0 hn ring, hostStep_right hpsi h2 ring C (p0 hn) hne]
    simpa [q] using hs.2.2
  have h2r : p2 hn ≠ ring.rightNeighbor (p0 hn) := by
    simpa only [right_p0] using h21
  have hp2 : Passive (raw (hostStep hpsi h2 ring C (p0 hn) (p2 hn))) := by
    rw [hostStep_other hpsi h2 ring C (p0 hn) (p2 hn) h20 h2r]
    exact hline.pass2
  exact ⟨{
    pass0 := hp0, pass1 := hp1, pass2 := hp2
    lab0 := (congrArg Fin.val (hf (p0 hn))).trans hline.lab0
    lab1 := (congrArg Fin.val (hf (p1 hn))).trans hline.lab1
    lab2 := (congrArg Fin.val (hf (p2 hn))).trans hline.lab2 }, hs.1⟩

private theorem step1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (hn : 4 ≤ n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (hline : LocalLine3 hpsi hn C)
    (hpre : RowPreCap2 hpsi h2 kappa ring C (p1 hn)) :
    LocalLine3 hpsi hn (hostStep hpsi h2 ring C (p1 hn)) ∧
      RowProjection2 hpsi h2 kappa tau ring C (p1 hn) := by
  have hs := local_row2_preCap hpsi h2 kappa tau ring C (p1 hn)
    (localEdge1 hpsi h2 hn ring C hline) hpre
  let q := BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2
    (C (p1 hn)) (C (ring.rightNeighbor (p1 hn)))
  change RowProjection2 hpsi h2 kappa tau ring C (p1 hn) ∧
    Passive (raw q.1) ∧ Passive (raw q.2) at hs
  have h01 : p0 hn ≠ p1 hn := Fin.ne_of_val_ne (by simp [p0, p1])
  have h02 : p0 hn ≠ p2 hn := Fin.ne_of_val_ne (by simp [p0, p2])
  have h21 : p2 hn ≠ p1 hn := Fin.ne_of_val_ne (by simp [p2, p1])
  have hne : ring.rightNeighbor (p1 hn) ≠ p1 hn := by
    simpa only [right_p1] using h21
  have hf := hostStep_label_frame_of_projection hpsi h2
    (by omega : 2 ≤ n) kappa tau ring C (p1 hn) hs.1
  have h0r : p0 hn ≠ ring.rightNeighbor (p1 hn) := by
    simpa only [right_p1] using h02
  have hp0 : Passive (raw (hostStep hpsi h2 ring C (p1 hn) (p0 hn))) := by
    rw [hostStep_other hpsi h2 ring C (p1 hn) (p0 hn) h01 h0r]
    exact hline.pass0
  have hp1 : Passive (raw (hostStep hpsi h2 ring C (p1 hn) (p1 hn))) := by
    rw [hostStep_left]
    simpa [q] using hs.2.1
  have hp2 : Passive (raw (hostStep hpsi h2 ring C (p1 hn) (p2 hn))) := by
    rw [← right_p1 hn ring, hostStep_right hpsi h2 ring C (p1 hn) hne]
    simpa [q] using hs.2.2
  exact ⟨{
    pass0 := hp0, pass1 := hp1, pass2 := hp2
    lab0 := (congrArg Fin.val (hf (p0 hn))).trans hline.lab0
    lab1 := (congrArg Fin.val (hf (p1 hn))).trans hline.lab1
    lab2 := (congrArg Fin.val (hf (p2 hn))).trans hline.lab2 }, hs.1⟩

private theorem right_val_of_not_left (hn : 4 ≤ n) (ring : DirectedRing n)
    (e : Fin n) (hleft : e ≠ leftCross hn) :
    (ring.rightNeighbor e).val = e.val + 1 := by
  have helast : e.val ≠ n - 1 := by
    intro hv
    apply hleft
    apply Fin.ext
    simpa [leftCross] using hv
  change (e.val + 1) % n = e.val + 1
  exact Nat.mod_eq_of_lt (by omega)

private theorem outside_stutter (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (hn : 4 ≤ n) (ring : DirectedRing n) (C : FC n psi kappa tau)
    (e : Fin n) (hsafe : SafeLine3Edge hn e)
    (hout : ¬ InternalLine3Edge hn e) :
    hostStep hpsi h2 ring C e (p0 hn) = C (p0 hn) ∧
    hostStep hpsi h2 ring C e (p1 hn) = C (p1 hn) ∧
    hostStep hpsi h2 ring C e (p2 hn) = C (p2 hn) := by
  have he0 : e ≠ p0 hn := fun h => hout (Or.inl h)
  have he1 : e ≠ p1 hn := fun h => hout (Or.inr h)
  have he0v : e.val ≠ 0 := by
    intro hv; apply he0; apply Fin.ext; simpa [p0] using hv
  have he1v : e.val ≠ 1 := by
    intro hv; apply he1; apply Fin.ext; simpa [p1] using hv
  have hr := right_val_of_not_left hn ring e hsafe.2
  have h0r : p0 hn ≠ ring.rightNeighbor e := by
    intro h; have hv := congrArg Fin.val h
    rw [hr] at hv; simp only [p0] at hv; omega
  have h1r : p1 hn ≠ ring.rightNeighbor e := by
    intro h; have hv := congrArg Fin.val h
    rw [hr] at hv; simp only [p1] at hv; omega
  have h2r : p2 hn ≠ ring.rightNeighbor e := by
    intro h; have hv := congrArg Fin.val h
    rw [hr] at hv; simp only [p2] at hv; omega
  exact ⟨
    hostStep_other hpsi h2 ring C e (p0 hn) (Ne.symm he0) h0r,
    hostStep_other hpsi h2 ring C e (p1 hn) (Ne.symm he1) h1r,
    hostStep_other hpsi h2 ring C e (p2 hn) (Ne.symm hsafe.1) h2r⟩

/-- One arbitrary allowed physical edge. Internal rows need only their actual
pre-cap test; outside rows have no endpoint assumptions at all. -/
theorem local3_one_step (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (hn : 4 ≤ n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n)
    (hline : LocalLine3 hpsi hn C) (hsafe : SafeLine3Edge hn e)
    (hpre : InternalLine3Edge hn e → RowPreCap2 hpsi h2 kappa ring C e) :
    LocalLine3 hpsi hn (hostStep hpsi h2 ring C e) ∧
      (InternalLine3Edge hn e → RowProjection2 hpsi h2 kappa tau ring C e) := by
  by_cases hin : InternalLine3Edge hn e
  · rcases hin with he | he
    · subst e
      have hs := step0 hpsi h2 hn kappa tau ring C hline (hpre (Or.inl rfl))
      exact ⟨hs.1, fun _ => hs.2⟩
    · subst e
      have hs := step1 hpsi h2 hn kappa tau ring C hline (hpre (Or.inr rfl))
      exact ⟨hs.1, fun _ => hs.2⟩
  · have st := outside_stutter hpsi h2 hn ring C e hsafe hin
    have hl : LocalLine3 hpsi hn (hostStep hpsi h2 ring C e) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [st.1]; exact hline.pass0
      · rw [st.2.1]; exact hline.pass1
      · rw [st.2.2]; exact hline.pass2
      · rw [st.1]; exact hline.lab0
      · rw [st.2.1]; exact hline.lab1
      · rw [st.2.2]; exact hline.lab2
    exact ⟨hl, fun hi => (hin hi).elim⟩

def SafePreCapWord (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn : 4 ≤ n)
    (kappa tau : Nat) (ring : DirectedRing n) (C : FC n psi kappa tau) :
    List (Fin n) → Prop
  | [] => True
  | e :: es =>
      SafeLine3Edge hn e ∧
      (InternalLine3Edge hn e → RowPreCap2 hpsi h2 kappa ring C e) ∧
      SafePreCapWord hpsi h2 hn kappa tau ring
        (hostStep hpsi h2 ring C e) es

def LineAlong3 (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn : 4 ≤ n)
    (kappa tau : Nat) (ring : DirectedRing n) (C : FC n psi kappa tau) :
    List (Fin n) → Prop
  | [] => LocalLine3 hpsi hn C
  | e :: es => LocalLine3 hpsi hn C ∧
      LineAlong3 hpsi h2 hn kappa tau ring (hostStep hpsi h2 ring C e) es

def InternalProjectionAlong3 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (hn : 4 ≤ n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) : List (Fin n) → Prop
  | [] => True
  | e :: es =>
      (InternalLine3Edge hn e → RowProjection2 hpsi h2 kappa tau ring C e) ∧
      InternalProjectionAlong3 hpsi h2 hn kappa tau ring
        (hostStep hpsi h2 ring C e) es

/-- Finite deterministic word, with exactly the two crossing edges excluded.
All internal and all disjoint outside letters may occur in any order. -/
theorem local3_word (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (hn : 4 ≤ n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (word : List (Fin n))
    (hline : LocalLine3 hpsi hn C)
    (hw : SafePreCapWord hpsi h2 hn kappa tau ring C word) :
    LineAlong3 hpsi h2 hn kappa tau ring C word ∧
      InternalProjectionAlong3 hpsi h2 hn kappa tau ring C word := by
  induction word generalizing C with
  | nil =>
      change LocalLine3 hpsi hn C ∧ True
      exact ⟨hline, trivial⟩
  | cons e rest ih =>
      change SafeLine3Edge hn e ∧
        (InternalLine3Edge hn e → RowPreCap2 hpsi h2 kappa ring C e) ∧
        SafePreCapWord hpsi h2 hn kappa tau ring
          (hostStep hpsi h2 ring C e) rest at hw
      have hs := local3_one_step hpsi h2 hn kappa tau ring C e
        hline hw.1 hw.2.1
      have ht := ih (C := hostStep hpsi h2 ring C e) hs.1 hw.2.2
      change
        (LocalLine3 hpsi hn C ∧
          LineAlong3 hpsi h2 hn kappa tau ring
            (hostStep hpsi h2 ring C e) rest) ∧
        ((InternalLine3Edge hn e → RowProjection2 hpsi h2 kappa tau ring C e) ∧
          InternalProjectionAlong3 hpsi h2 hn kappa tau ring
            (hostStep hpsi h2 ring C e) rest)
      exact ⟨⟨hline, ht.1⟩, ⟨hs.2, ht.2⟩⟩

#print axioms BirthShortDoneTerminalPassiveLocal3.local3_one_step
#print axioms BirthShortDoneTerminalPassiveLocal3.local3_word

end BirthShortDoneTerminalPassiveLocal3
