import Leader.L4.ShortAdmitReverse
import Leader.L4.ShortPreReadGrants

namespace L4.ShortAdmitForward
open AllSizeProtocol PhysicalCustody MISByteCodec ShortResetRow ShortResetFlow
open ShortResetMIS1Ring ShortResetCycle ShortResetChart ShortResetForwardH2
open ShortAdmitFlightSync ShortHelloAdmitCodec ShortAdmitGate ShortAdmitReturn
open ShortHelloForward ShortDirtyMIS1Ring ShortEmptyOwnership
set_option maxRecDepth 8192

variable {s n : Nat} {h : Fin n → Bool}

def gated (C : Chart h) (x : Raw s n) (i : Nat) : Bool :=
  atGate (header x (nextAt C.root i)) (x (nextAt C.root i)).mis1 (C.route.port i)

def ingressRace (r : Nat) : Nat := if r=1 then 2 else if r=3 then 5 else r

def ParkedRace (r : Nat) : Prop := r=1 ∨ r=2 ∨ r=3

/-- The three literal case lemmas that are not supplied by the HELLO
frames: ADMIT ingress, parked outbound race3 and old gated packet
normalization. The frame allows a foreign owner at every other lane. -/
structure WireFrames (s n : Nat) : Prop where
  ingress : ∀ (x : Raw s n) (e : Fin n) (j k : Fin 3) (won : Bool) (race : Nat),
    e≠rightNeighbor e → destination (header x (rightNeighbor e)) j=some k →
    oldK (header x e) (x e).mis1 j=T →
    (kField j).read (x e).mis1=encode T →
    (kField k).read (x (rightNeighbor e)).mis1=encode (admitForward won race) →
    oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=admitForward won race →
    (atGate (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=false → race=0) →
    (kField j).read (rawNext s x e e).mis1=encode T ∧
      (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
        encode (admitForward won (ingressRace race))
  out3 : ∀ (x : Raw s n) (e : Fin n) (j k : Fin 3),
    e≠rightNeighbor e → destination (header x (rightNeighbor e)) j=some k →
    oldK (header x e) (x e).mis1 j=admitForward false 3 →
    atGate (header x e) (x e).mis1 j=true →
    (kField j).read (x e).mis1=encode (admitForward false 3) →
    (kField k).read (x (rightNeighbor e)).mis1=encode E →
    (kField j).read (rawNext s x e e).mis1=encode (admitForward false 3) ∧
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField k).read (x (rightNeighbor e)).mis1
  parkedRight : ∀ (x : Raw s n) (e : Fin n) (j k : Fin 3) (r : Nat),
    e≠rightNeighbor e → destination (header x (rightNeighbor e)) j=some k →
    oldK (header x e) (x e).mis1 j=admitForward false r →
    atGate (header x e) (x e).mis1 j=true → ParkedRace r →
    oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=E →
    (kField k).read (x (rightNeighbor e)).mis1=encode E →
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=encode E

theorem decode_valid (C : Chart h) (x : Raw s n) (i : Nat) (won : Bool) (race : Nat)
    (F : bits C.route x i=encode (admitForward won race))
    (valid : if gated C x i then 1≤race ∧ race≤5 else race=0) :
    slot C.route x i=admitForward won race := by
  have bound : race<8 := by split at valid <;> omega
  change decode (gated C x i) (bits C.route x i) = _
  rw [F, decode_admit_forward _ _ _ bound]
  cases G : gated C x i
  · simp [G] at valid
    simp [valid]
  · simp [G] at valid
    simp [valid.1,valid.2]

private theorem root_forward_frame (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (H : header x (rightNeighbor e)=true) (W : Wait2 x (rightNeighbor e))
    (won : Bool) (F : (kField 0).read (x (rightNeighbor e)).mis1=encode (admitForward won 0)) :
    (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=encode (admitForward won 0) := by
  let b := (x (rightNeighbor e)).mis1
  have O : oldK true b 0=admitForward won 0 := by
    unfold oldK
    rw [show (kField 0).read b = _ from F, admit_gate_k0, decode_admit_forward false won 0 (by decide)]
    rfl
  have P := source_wait_holds b (oldK true b 0) W.1 (by rw [W.2]; decide)
    (.inr (by rw [O]; rfl))
  have Q := source_door_k0_raw x e sep H
  change (kField 0).read (rawNext s x e (rightNeighbor e)).mis1 =
    (match (source b (oldK true b 0)).2 with
    | none => normalizedNoForward true b 0 | some t => encode t) at Q
  rw [P] at Q
  exact (by simpa [normalizedNoForward,O,admitForward] using Q : _ = (kField 0).read b).trans F

theorem forward_no_ask (C : Chart h) (x : Raw s n) (heads : ∀ q,header x q=h q)
    (i : Nat) (won : Bool) (race : Nat) (F : Fwd C x i won race)
    (valid : if gated C x i then 1≤race ∧ race≤5 else race=0) :
    ShortPreReadGrants.NoAsk C.route x := by
  intro j J H
  have hd : header x (nextAt C.root j)=true := (heads _).trans H
  apply ShortPreReadGrants.pre_read_no_ask
  have B := F.2.2 j J
  by_cases A : j<i
  · rw [if_pos A] at B
    have B := slot_of_bits C.route x j T trail_decode B
    change oldK (header x (nextAt C.root j)) _ _ = _ at B
    rw [hd] at B
    exact .inr (.inl B)
  · by_cases E : j=i
    · subst j
      rw [if_neg A,if_pos rfl] at B
      have B := decode_valid C x i won race B valid
      change oldK (header x (nextAt C.root i)) _ _ = _ at B
      rw [hd] at B
      exact .inr (.inr (.inr (.inr (.inr ⟨won,race,B⟩))))
    · rw [if_neg A,if_neg E] at B
      have B := slot_of_bits C.route x j MISByteCodec.E empty_decode B
      change oldK (header x (nextAt C.root j)) _ _ = _ at B
      rw [hd] at B
      exact .inl B

private theorem changed_slots (C : Chart h) (x : Raw s n) (i : Nat) (oldWon : Bool) (oldRace : Nat)
    (I : i+1<C.L) (A : Fwd C x i oldWon oldRace) (won : Bool) (race : Nat)
    (left : bits C.route (rawNext s x (nextAt C.root i)) i=encode T)
    (right : bits C.route (rawNext s x (nextAt C.root i)) (i+1)=encode (admitForward won race))
    (wait : Wait2 (rawNext s x (nextAt C.root i)) C.root) :
    Fwd C (rawNext s x (nextAt C.root i)) (i+1) won race := by
  refine ⟨I,wait,?_⟩
  intro j J
  by_cases L : j=i
  · subst j
    simpa using left
  by_cases R : j=i+1
  · subst j
    simpa using right
  have B := C.length_lt
  change (kField (C.route.port j)).read (rawNext s x (nextAt C.root i) (nextAt C.root j)).mis1 = _
  rw [reset_remote_frame_raw _ _ _
    (fun P => L (nextAt_injective_under C.root _ _ (by omega) (by omega) P))
    (fun P => R (nextAt_injective_under C.root _ _ (by omega) (by omega) P))]
  change bits C.route x j = _
  exact (A.2.2 j J).trans (by by_cases W : j<i <;> simp [W,L,R,show j<i+1 ↔ j<i by omega])

private theorem turn_slots (C : Chart h) (x : Raw s n) (i : Nat) (won : Bool) (race : Nat)
    (I : i+1=C.L) (A : Fwd C x i won race)
    (left : bits C.route (rawNext s x (nextAt C.root i)) i=encode (admitReply won))
    (wait : Wait2 (rawNext s x (nextAt C.root i)) C.root) :
    Rev C (rawNext s x (nextAt C.root i)) i won := by
  refine ⟨A.1,wait,?_⟩
  intro j J
  by_cases L : j=i
  · subst j
    simpa using left
  have B := C.length_lt
  have Q : j<i := by omega
  change (kField (C.route.port j)).read (rawNext s x (nextAt C.root i) (nextAt C.root j)).mis1 = _
  rw [reset_remote_frame_raw _ _ _
    (fun P => L (nextAt_injective_under C.root _ _ (by omega) (by omega) P))
    (fun P => by have U := nextAt_injective_under C.root j (i+1) (by omega) (by omega) P; omega)]
  change bits C.route x j = _
  exact (A.2.2 j J).trans (by simp [Q])

/-- Prefix slots share neither race state nor payload: they retain T
until the unique reverse packet crosses them. -/
private theorem prefix_idle (Frames : WireFrames s n) (C : Chart h) (x : Raw s n)
    (heads : ∀ q, header x q=h q) (e : Fin n) (i j : Nat)
    (J : j<i) (won : Bool) (race : Nat) (F : Fwd C x i won race)
    (front : slot C.route x i=admitForward won race)
    (norace : gated C x i=false → race=0) :
    bits C.route (rawNext s x e) j=encode T := by
  let R := C.route
  have npos : 1<n := by have := C.positive; have := C.length_lt; omega
  have sep := edge_sep npos e
  have trail (k : Nat) (K : k<i) : bits R x k=encode T := by
    exact (F.2.2 k (by have := F.1; omega)).trans (if_pos K)
  have old (k : Nat) (K : k<i) : slot R x k=T := slot_of_bits R x k T trail_decode (trail k K)
  have dst (k : Nat) (K : k+1<C.L) :
      destination (header x (rightNeighbor (nextAt C.root k))) (R.port k)=some (R.port (k+1)) := by
    rw [heads]; exact R.live k K
  change (kField (R.port j)).read (rawNext s x e (nextAt C.root j)).mis1 = _
  by_cases L : nextAt C.root j=e
  · subst e
    have D := dst j (by have := F.1; omega)
    by_cases K : j+1=i
    · have O := old j J
      have H : slot R x (j+1)=admitForward won race := K ▸ front
      have B : bits R x (j+1)=encode (admitForward won race) := by
        rw [K]; simpa using F.2.2 i F.1
      exact (Frames.ingress x _ _ _ won race sep D O (trail j J) B H (by
        intro off
        apply norace
        unfold gated
        rw [←K]
        exact off)).1
    · have R0 : slot R x (j+1)=T := old _ (by omega)
      exact (reset_prefix_trail_frame_raw x _ sep _ _ D (old j J) (.inr R0)).trans (trail j J)
  · by_cases Q : nextAt C.root j=rightNeighbor e
    · cases j with
      | zero =>
        change C.root=rightNeighbor e at Q
        rw [C.route.rootPort,Q]
        have hd : header x (rightNeighbor e)=true := by rw [←Q,heads,C.rootHeader]
        exact ShortAdmitReverse.wait2_root_trail_holds x e sep hd
          (Q ▸ F.2.1) (by
          rw [←Q,←C.route.rootPort]; exact trail 0 J)
      | succ k =>
        have E : nextAt C.root k=e := by
          have U := congrArg RearTrace.predecessor Q
          change RearTrace.predecessor (rightNeighbor (nextAt C.root k)) = _ at U
          simpa only [RearTrace.predecessor_right] using U
        subst e
        have D := dst k (by have := F.1; omega)
        exact (reset_inbound_frame_raw x _ sep _ _ D (old k (by omega)) (.inr (old (k+1) J))).trans (trail _ J)
    · rw [reset_remote_frame_raw _ _ _ L Q]
      exact trail j J

private theorem front_idle (Frames : WireFrames s n) (C : Chart h) (x : Raw s n)
    (heads : ∀ q, header x q=h q) (e : Fin n) (i : Nat) (won : Bool) (race : Nat)
    (F : Fwd C x i won race) (O : slot C.route x i=admitForward won race)
    (notOut : e≠nextAt C.root i)
    (rootRace : i=0 → race=0)
    (norace : gated C x i=false → race=0) :
    bits C.route (rawNext s x e) i =
      encode (admitForward won (if rightNeighbor e=nextAt C.root i then ingressRace race else race)) := by
  have npos : 1<n := by have := C.positive; have := C.length_lt; omega
  have B : bits C.route x i=encode (admitForward won race) := by simpa using F.2.2 i F.1
  change (kField (C.route.port i)).read (rawNext s x e (nextAt C.root i)).mis1=_
  by_cases Q : rightNeighbor e=nextAt C.root i
  · rw [if_pos Q]
    cases i with
    | zero =>
      have Hd : header x (rightNeighbor e)=true := by rw [Q]; exact (heads _).trans C.rootHeader
      have r0 : race=0 := rootRace rfl
      subst race
      rw [←Q,C.route.rootPort]
      apply root_forward_frame x e (edge_sep npos e) Hd (Q ▸ F.2.1) won
      rw [Q,←C.route.rootPort]
      exact B
    | succ j =>
      have EJ : e=nextAt C.root j := by
        have K := congrArg RearTrace.predecessor Q
        change _ = RearTrace.predecessor (rightNeighbor (nextAt C.root j)) at K
        simpa only [RearTrace.predecessor_right] using K
      subst e
      have l : destination (header x (rightNeighbor (nextAt C.root j))) (C.route.port j)
          = some (C.route.port (j+1)) := by rw [heads]; exact C.route.live j F.1
      have T0 : bits C.route x j=encode T := by
        simpa [show j<j+1 by omega] using F.2.2 j (by have := F.1; omega)
      exact (Frames.ingress x _ _ _ won race (edge_sep npos _) l
        (slot_of_bits C.route x j T trail_decode T0) T0 B O norace).2
  · rw [if_neg Q,reset_remote_frame_raw _ _ _ (Ne.symm notOut) (Ne.symm Q)]
    exact B

def Valid (g i : Nat) (w : Bool) (r : Nat) : Prop :=
  (i≤g → w=false) ∧ (if i=g then 1≤r ∧ r≤5 else r=0)

inductive ForwardState
  | fwd (i : Nat) (won : Bool) (race : Nat)
  | rev (i : Nat) (won : Bool)

def nextForward {n : Nat} {h : Fin n → Bool} (C : Chart h)
    (g : Nat) (e : Fin n) (i : Nat) (w : Bool) (r : Nat) : ForwardState :=
  if e=nextAt C.root i then
    if i=g then
      if r=1 then .fwd i false 3 else
      if r=2 then .fwd i false 4 else
      if r=3 then .fwd i false 3 else .fwd (i+1) (r==5) 0
    else if i+1<C.L then
      .fwd (i+1) w (if i+1=g then 1 else 0)
    else .rev i w
  else .fwd i w (if rightNeighbor e=nextAt C.root i then ingressRace r else r)

theorem valid_decode (C : Chart h) (x : Raw s n) (g i : Nat) (won : Bool) (r : Nat)
    (G : gated C x i=true ↔ i=g) (V : Valid g i won r) :
    if gated C x i then 1≤r ∧ r≤5 else r=0 := by
  cases E : gated C x i
  · have K : i≠g := fun P => Bool.noConfusion (E.symm.trans (G.mpr P))
    simpa [E,K] using V.2
  · have K : i=g := G.mp E
    simpa [E,K] using V.2

def ValidState (C : Chart h) (x : Raw s n) (g : Nat) : ForwardState → Prop
  | .fwd i w r => Fwd C x i w r ∧ Valid g i w r
  | .rev i w => Rev C x i w

theorem forward_all_mark (Frames : WireFrames s n) (C : Chart h) (x : Raw s n)
    (heads : ∀ q, header x q=h q) (e : Fin n) (g : Nat) (gp : 0<g) (gL : g+1<C.L)
    (gates : ∀ j, j<C.L → (gated C x j=true ↔ j=g))
    (i : Nat) (w : Bool) (r : Nat) (F : Fwd C x i w r) (V : Valid g i w r) :
    ValidState C (rawNext s x e) g (nextForward C g e i w r) := by
  have npos : 1<n := by have := C.positive; have := C.length_lt; omega
  have sep := edge_sep npos e
  have I := F.1
  have B : bits C.route x i=encode (admitForward w r) := by simpa using F.2.2 i I
  have valid := valid_decode C x g i w r (gates _ I) V
  have Old := decode_valid C x i w r B valid
  have norace (off : gated C x i=false) : r=0 := by simpa [off] using valid
  have hd := (heads C.root).trans C.rootHeader
  have trail (j : Nat) (J : j<i) : bits C.route x j=encode T :=
    (F.2.2 j (by omega)).trans (if_pos J)
  have suffix : ClearSuffix C.route x i := by
    intro j J L
    exact (F.2.2 j L).trans (by simp [show ¬j<i by omega, show j≠i by omega])
  have wait : Wait2 (rawNext s x e) C.root := by
    apply wait2_holds x _ e sep hd F.2.1
    intro _
    by_cases z : i=0
    · subst i
      have F := Old
      change oldK (header x C.root) (x C.root).mis1 (C.route.port 0)=_ at F
      rw [hd,C.route.rootPort] at F
      exact .inr (by rw [F]; rfl)
    · have T0 := slot_of_bits C.route x 0 T trail_decode (trail 0 (by omega))
      change oldK (header x C.root) (x C.root).mis1 (C.route.port 0)=_ at T0
      rw [hd,C.route.rootPort] at T0
      exact .inl (by rw [T0]; rfl)
  have dst (J : i+1<C.L) :
      destination (header x (rightNeighbor (nextAt C.root i))) (C.route.port i)=some (C.route.port (i+1)) := by
    rw [heads]; exact C.route.live i J
  by_cases out : e=nextAt C.root i
  · subst e
    by_cases G : i=g
    · subst i
      have oldG := (gates g I).mpr rfl
      have W : w=false := V.1 (by omega)
      subst w
      have nextOff : gated C x (g+1)=false :=
        Bool.eq_false_iff.mpr (fun P => by have E := (gates _ gL).mp P; omega)
      have range : 1≤r ∧ r≤5 := by simpa using V.2
      have hold_parked (p : Nat) (R : ParkedRace r)
          (P : bits C.route (rawNext s x (nextAt C.root g)) g =
            encode (admitForward false p)) :
          Fwd C (rawNext s x (nextAt C.root g)) g false p := by
        refine ⟨I,wait,?_⟩
        intro j J
        by_cases A : j<g
        · simp only [if_pos A]
          exact prefix_idle Frames C x heads _ _ j A _ _ F Old norace
        by_cases K : j=g
        · subst j
          simpa using P
        · simp only [if_neg A,if_neg K]
          by_cases S : j=g+1
          · subst j
            have right := suffix (g+1) (by omega) gL
            exact Frames.parkedRight x _ _ _ r sep (dst gL) Old oldG R
              (slot_of_bits C.route x _ E empty_decode right) right
          · have SU := clear_suffix_step C.route x _ sep heads g suffix
            exact SU j (by
              change (if nextAt C.root g=nextAt C.root g then g+1 else g)<j
              rw [if_pos rfl]; omega) J
      have cases : r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 := by omega
      rcases cases with rfl|rfl|rfl|rfl|rfl <;> simp [nextForward,ValidState]
      · exact ⟨hold_parked 3 (.inl rfl) (parked_out C x g 1 (.inl rfl) ⟨oldG,B⟩),
          ⟨fun _ => rfl, by simp⟩⟩
      · exact ⟨hold_parked 4 (.inr (.inl rfl)) (parked_out C x g 2 (.inr rfl) ⟨oldG,B⟩),⟨fun _ => rfl, by simp⟩⟩
      · have right := suffix (g+1) (by omega) gL
        exact ⟨hold_parked 3 (.inr (.inr rfl)) (Frames.out3 x _ _ _ sep (dst gL) Old oldG B right).1,
          ⟨fun _ => rfl, by simp⟩⟩
      · have W := ready_exit C x heads g gL false nextOff ⟨oldG,B⟩
        exact ⟨changed_slots C x g false 4 gL F false 0 W.1 W.2 wait, ⟨fun _ => rfl, by simp⟩⟩
      · have W := ready_exit C x heads g gL true nextOff ⟨oldG,B⟩
        exact ⟨changed_slots C x g false 5 gL F true 0 W.1 W.2 wait, ⟨fun H => by omega, by simp⟩⟩
    · have r0 : r=0 := by simpa [G] using V.2
      subst r
      have off : gated C x i=false := Bool.eq_false_iff.mpr (fun P => G ((gates i I).mp P))
      by_cases J : i+1<C.L
      · by_cases K : i+1=g
        · have W : w=false := V.1 (by omega)
          subst w
          have outBits := arrive_gate C x heads i J off ((gates _ J).mpr K) B
          simpa [nextForward, G, J, K, show g<C.L by omega, ValidState] using
            (show Fwd C (rawNext s x (nextAt C.root i)) (i+1) false 1 ∧ Valid g (i+1) false 1 from
              ⟨changed_slots C x i false 0 J F false 1 outBits.1 outBits.2 wait,
                ⟨fun _ => rfl,by simp [K]⟩⟩)
        · have nextOff : gated C x (i+1)=false := Bool.eq_false_iff.mpr (fun P => K ((gates _ J).mp P))
          have outBits := admit_ungated_out_raw x (nextAt C.root i) sep _ _ _ (dst J) Old rfl rfl rfl off
          rw [show rightNeighbor (nextAt C.root i)=nextAt C.root (i+1) from rfl, show atGate (header x (nextAt C.root (i+1))) (x (nextAt C.root (i+1))).mis1 (C.route.port (i+1))=false from nextOff] at outBits
          simpa [nextForward, G, J, K, ValidState] using
            (show Fwd C (rawNext s x (nextAt C.root i)) (i+1) w 0 ∧ Valid g (i+1) w 0 from
              ⟨changed_slots C x i w 0 J F w 0 outBits.1 outBits.2 wait,
                ⟨fun P => V.1 (by omega), by simp [K]⟩⟩)
      · have K : i=C.L-1 := by omega
        have d : destination (header x (rightNeighbor (nextAt C.root i))) (C.route.port i)=none := by
          rw [heads,K]; exact C.route.turn
        have bits := admit_turn_raw x (nextAt C.root i) sep _ _ d Old rfl rfl rfl
        simpa [nextForward,G,J,ValidState] using
          turn_slots C x i w 0 (by omega) F bits wait
  · let r' := if rightNeighbor e=nextAt C.root i then ingressRace r else r
    have frontBits := front_idle Frames C x heads e i w r F Old out
      (fun Z => by
        have H : i≠g := by omega
        simpa [H] using V.2) norace
    have F' : Fwd C (rawNext s x e) i w r' := by
      refine ⟨I,wait,?_⟩
      intro j J
      by_cases A : j<i
      · simp only [if_pos A]
        exact prefix_idle Frames C x heads e i j A w r F Old norace
      by_cases K : j=i
      · subst j; simpa using frontBits
      · simp only [if_neg A,if_neg K]
        exact clear_suffix_step C.route x e sep heads i suffix j (by
          change (if e=nextAt C.root i then i+1 else i)<j
          rw [if_neg out]; omega) J
    have V' : Valid g i w r' := by
      refine ⟨V.1,?_⟩
      by_cases G : i=g
      · have D : 1≤r ∧ r≤5 := by simpa [G] using V.2
        simp only [G]
        dsimp [r',ingressRace]
        split <;> (repeat' split) <;> omega
      · have r0 : r=0 := by simpa [G] using V.2
        simp [G,r',r0,ingressRace]
    simpa only [nextForward,if_neg out,ValidState] using And.intro F' V'

end L4.ShortAdmitForward
