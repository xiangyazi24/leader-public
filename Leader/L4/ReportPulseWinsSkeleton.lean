import Leader.L4.ReportPulseRounds
import Leader.L4.ReportPulseWarmup

namespace L4.ReportPulseWinsSkeleton
open ReportPulseRecode ReportPulseRounds
universe u v
variable {G : Type u} [DecidableEq G] {n : Nat}

def physicalRun {Z : Type v} (s : Phase G) (w : List (Label G Z)) : Phase G :=
  w.foldl physicalStep s

theorem run_snoc {Z : Type v} (s : Phase G) (u : List (Label G Z)) (e : Label G Z) :
    physicalRun s (u++[e])=physicalStep (physicalRun s u) e := by
  simp only [physicalRun,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem events_append {Z : Type v} (s : Phase G) (u v : List (Label G Z)) :
    physicalEvents s (u++v)=physicalEvents s u++physicalEvents (physicalRun s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons e u IH => simp only [List.cons_append,physicalEvents,physicalRun,List.foldl_cons,IH]

theorem state_mix {Z : Type v} (s : Phase G) (w : List (Label G Z)) :
    skeletonState (armed s) (encode s w)=armed (physicalRun s w) := by
  induction w generalizing s with
  | nil => rfl
  | cons e w IH => simp only [skeletonState,encode,physicalRun,List.foldl_cons,step_fusion,IH]

private theorem other_mark (put : G × Bool → Fin n) (g : G) (s : Phase G) (e : Fin n)
    (A : e≠put (g,false)) (B : e≠put (g,true)) :
    physicalStep s (readLabel put e) g=s g ∧ Quiet g (physicalEvent s (readLabel put e)) := by
  cases E : readLabel put e with
  | inr z => simp [physicalStep,physicalEvent,Quiet]
  | inl ib =>
    obtain ⟨h,t⟩ := ib
    have Map := write_read put e
    rw [E] at Map
    change put (h,t)=e at Map
    have D : h≠g := by
      intro Eq
      subst h
      cases t
      · exact A Map.symm
      · exact B Map.symm
    refine ⟨by simp [physicalStep,Ne.symm D],?_⟩
    cases S : s h <;> cases t <;> simp [physicalEvent,Quiet,S,D] <;> split <;> simp [D]

def phaseOf : ReportPulseWait.Phase → Option Bool
  | .empty => none
  | .outgoing => some true
  | .incoming => some false

theorem pending_events (put : G × Bool → Fin n) (inj : Function.Injective put)
    (g : G) (s : Phase G) (S : s g=none)
    {ph : ReportPulseWait.Phase} {w : List (Fin n)}
    (P : ReportPulseWarmup.Pending (put (g,false)) (put (g,true)) ph w) :
    physicalRun s (w.map (readLabel put)) g=phaseOf ph ∧
      OpenRound g (physicalEvents s (w.map (readLabel put))) (phaseOf ph).isSome := by
  have E (t : Bool) : readLabel put (put (g,t))=.inl (g,t) := read_write put inj (.inl (g,t))
  induction P with
  | nil => exact ⟨S,.nil⟩
  | @quiet ph w e P A B IH =>
    let z := physicalRun s (w.map (readLabel put))
    have Q := other_mark put g z e A B
    rw [List.map_append,events_append]
    simp only [List.map_cons,List.map_nil,run_snoc]
    exact ⟨Q.1.trans IH.1,.quiet IH.2 Q.2⟩
  | @out w P IH =>
    rw [List.map_append,events_append]
    simp only [List.map_cons,List.map_nil,E]
    refine ⟨?_,?_⟩
    · rw [run_snoc]
      simp [physicalStep,phaseOf,phaseNext,IH.1]
    · simp only [physicalEvents,physicalEvent,IH.1,phaseOf]
      exact .start IH.2
  | @inc w P IH =>
    rw [List.map_append,events_append]
    simp only [List.map_cons,List.map_nil,E]
    refine ⟨?_,?_⟩
    · rw [run_snoc]
      simp [physicalStep,phaseOf,phaseNext,IH.1]
    · simp only [physicalEvents,physicalEvent,IH.1,phaseOf]
      exact .start IH.2
  | @outAgain w P IH =>
    rw [List.map_append,events_append]
    simp only [List.map_cons,List.map_nil,E]
    refine ⟨?_,?_⟩
    · rw [run_snoc]
      simp [physicalStep,phaseOf,phaseNext,IH.1]
    · simp only [physicalEvents,physicalEvent,IH.1,phaseOf,if_true]
      exact .quiet IH.2 ⟨by simp,by simp⟩
  | @inAgain w P IH =>
    rw [List.map_append,events_append]
    simp only [List.map_cons,List.map_nil,E]
    refine ⟨?_,?_⟩
    · rw [run_snoc]
      simp [physicalStep,phaseOf,phaseNext,IH.1]
    · simp only [physicalEvents,physicalEvent,IH.1,phaseOf,if_true]
      exact .quiet IH.2 ⟨by simp,by simp⟩

theorem wins_events (put : G × Bool → Fin n) (inj : Function.Injective put)
    (g : G) (s : Phase G) (S : s g=none) {J : Nat} {w : List (Fin n)}
    (P : ReportPulseWarmup.Wins (put (g,false)) (put (g,true)) J w) :
    physicalRun s (w.map (readLabel put)) g=none ∧
      ClosedRounds g J (physicalEvents s (w.map (readLabel put))) := by
  have E : readLabel put (put (g,false))=.inl (g,false) := read_write put inj (.inl (g,false))
  induction P with
  | zero => exact ⟨S,.zero⟩
  | @snoc k u v U V IH =>
    have P := pending_events put inj g (physicalRun s (u.map (readLabel put))) IH.1 V
    simp only [List.map_append,events_append,List.map_cons,List.map_nil,E]
    have Eq : physicalRun s (u.map (readLabel put)++v.map (readLabel put)) g=some true := by
      unfold physicalRun at P ⊢
      rw [List.foldl_append]
      exact P.1
    refine ⟨?_,?_⟩
    · rw [run_snoc]
      simp [physicalStep,Eq,phaseNext]
    · simp [physicalEvents,physicalEvent,Eq]
      simpa only [List.append_assoc] using (ClosedRounds.snoc IH.2 P.2)

#print axioms pending_events
#print axioms wins_events

theorem encode_append {Z : Type v} (s : Phase G) (u v : List (Label G Z)) :
    encode s (u++v)=encode s u++encode (physicalRun s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons e u IH => simp only [List.cons_append,encode,physicalRun,List.foldl_cons,IH]

/-- Given the clean boundary from WARMUP1 and its fresh Wins suffix,
the last J pairs up through the credited completion are determined by
the recoded skeleton. Every extracted start/complete index has its
literal event tag on the same prefix. -/
theorem wins_extract (put : G × Bool → Fin n) (inj : Function.Injective put)
    (g : G) (s : Phase G) (u v : List (Fin n)) (J : Nat)
    (Clean : physicalRun s (u.map (readLabel put)) g=none)
    (Win : ReportPulseWarmup.Wins (put (g,false)) (put (g,true)) J v) :
    let full := skeleton (armed s) ((encodeFin put s (u++v)).map (readLabel put))
    let z := physicalRun s (u.map (readLabel put))
    let pairs := extract g J full
    pairs.length=J ∧ ∀ pair∈pairs, PairAt g u.length
      (physicalEvents z (v.map (readLabel put))) pair := by
  dsimp only
  let z := physicalRun s (u.map (readLabel put))
  let left := encode s (u.map (readLabel put))
  let right := encode z (v.map (readLabel put))
  have E : skeletonState (armed s) left=armed z := state_mix s _
  have Empty : skeletonState (armed s) left g=false := by
    rw [E]
    simp [armed,z,Clean]
  have C := (wins_events put inj g z Clean Win).2
  rw [←skeleton_encode z] at C
  have C' : ClosedRounds g J (skeleton (skeletonState (armed s) left) right) := by
    rw [E]
    exact C
  have A := extract_closed_suffix g J (armed s) left right Empty C'
  dsimp only at A
  rw [E,skeleton_encode z,show left.length=u.length by simp [left,encode_length]] at A
  unfold encodeFin
  rw [read_write_word put inj,List.map_append,encode_append]
  exact A

/-- Suffix beyond the pinned completion does not change the extracted
list, because skeleton prefixes are chronological. -/
theorem skeleton_prefixFin (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Phase G) (pre post : List (Fin n)) :
    (skeleton (armed s) ((encodeFin put s (pre++post)).map (readLabel put))).take pre.length =
      skeleton (armed s) ((encodeFin put s pre).map (readLabel put)) := by
  rw [skeleton_encodeFin put inj,skeleton_encodeFin put inj,List.map_append,events_append]
  have L : (physicalEvents s (pre.map (readLabel put))).length=pre.length := by
    rw [←skeleton_encode,skeleton_length,encode_length,List.length_map]
  rw [←L]
  simp

#print axioms wins_extract
#print axioms skeleton_prefixFin

/-- The one-gate projection agrees with WARMUP1's normalized clock
on every mark and does not depend on its streak or paint latch. -/
theorem gate_step_agrees (put : G × Bool → Fin n) (inj : Function.Injective put)
    (g : G) (s : Phase G) (J : Nat) (c : ReportPulseWait.State) (e : Fin n)
    (H : s g=phaseOf c.phase) :
    physicalStep s (readLabel put e) g=phaseOf
      (ReportPulseWait.step J (put (g,false)) (put (g,true)) e c).phase := by
  have E (t : Bool) : readLabel put (put (g,t))=.inl (g,t) := read_write put inj (.inl (g,t))
  have D : put (g,true)≠put (g,false) := by
    intro Eq
    have B := congrArg Prod.snd (inj Eq)
    contradiction
  by_cases I : e=put (g,false)
  · subst e
    rw [E false]
    cases Hph : c.phase with
    | empty | incoming =>
      simp [physicalStep,phaseNext,H,Hph,phaseOf,ReportPulseWait.step,ReportPulseWait.side]
    | outgoing =>
      by_cases K : ReportPulseWait.effective J c.count+1=J <;>
        simp [physicalStep,phaseNext,H,Hph,phaseOf,ReportPulseWait.step,ReportPulseWait.side,K]
  · by_cases O : e=put (g,true)
    · subst e
      rw [E true]
      cases Hph : c.phase <;>
        simp [physicalStep,phaseNext,H,Hph,phaseOf,ReportPulseWait.step,ReportPulseWait.side,D]
    · rw [(other_mark put g s e I O).1,H]
      simp [ReportPulseWait.step,I,O]

theorem gate_run_agrees (put : G × Bool → Fin n) (inj : Function.Injective put)
    (g : G) (s : Phase G) (J : Nat) (c : ReportPulseWait.State) (w : List (Fin n))
    (H : s g=phaseOf c.phase) :
    physicalRun s (w.map (readLabel put)) g=phaseOf
      (w.foldl (fun x e=>ReportPulseWait.step J (put (g,false)) (put (g,true)) e x) c).phase := by
  induction w generalizing s c with
  | nil => exact H
  | cons e w IH => exact IH _ _ (gate_step_agrees put inj g s J c e H)

#print axioms gate_run_agrees

open AllSizeProtocol ReportByteRows ReportPulseRaw

/-- Literal clean cut from the existing all-mark raw clock equality.
The monitored paint bit is immaterial to the phase, but chronology
and the original physical tape are retained. -/
theorem raw_clean_empty {X : Type}
    (put : G × Bool → Fin n) (inj : Function.Injective put) (g : G)
    {raw : X → Fin n → X} {Q : X → Prop} {p : Params} {bytes : X → BitVec p.w}
    (Wire : Wire raw (put (g,true)) Q p bytes)
    (Adj : rightNeighbor (put (g,false))=put (g,true)) (J : 0<p.streak)
    (base : X) (Good : Q base) (s : Phase G)
    (Initial : s g=phaseOf (ReportPulseWarmup.readClock p bytes base).phase)
    (u : List (Fin n)) (Cut : ReportPulseWarmup.cleanAt raw p bytes base u) :
    physicalRun s (u.map (readLabel put)) g=none := by
  have Distinct : put (g,false)≠put (g,true) := by
    intro H
    have E := congrArg Prod.snd (inj H)
    contradiction
  have Run := gate_run_agrees put inj g s p.streak (ReportPulseWarmup.readClock p bytes base) u Initial
  have WireRun := ReportPulseWarmup.wire_run_eq Wire (put (g,false)) Adj Distinct J base u false Good
  dsimp only at WireRun
  unfold ReportPulseWarmup.readClock at Run
  rw [←WireRun] at Run
  rw [ReportPulseWarmup.monitor_base] at Run
  have End : (ReportPulseWarmup.readClock p bytes (u.foldl raw base)).phase=
      ReportPulseWait.Phase.empty := Cut.1
  change physicalRun s (u.map (readLabel put)) g=
    phaseOf (ReportPulseWarmup.readClock p bytes (u.foldl raw base)).phase at Run
  rw [End] at Run
  exact Run

/-- Actual WARMUP1 credit → deterministic last-J start/completion
coordinates in the recoded skeleton of that literal entire prefix. -/
theorem raw_credit_extract {X : Type}
    (put : G × Bool → Fin n) (inj : Function.Injective put) (g : G)
    {raw : X → Fin n → X} {Q : X → Prop} {p : Params} {bytes : X → BitVec p.w}
    (Wire : Wire raw (put (g,true)) Q p bytes)
    (Adj : rightNeighbor (put (g,false))=put (g,true)) (J : 0<p.streak)
    (base : X) (Good : Q base) (s : Phase G)
    (Initial : s g=phaseOf (ReportPulseWarmup.readClock p bytes base).phase)
    (w : List (Fin n))
    (Credit : ReportPulseWarmup.Credit (put (g,false)) (put (g,true)) p.streak
      (ReportPulseWarmup.cleanAt raw p bytes base) w) :
    let pairs := extract g p.streak (skeleton (armed s) ((encodeFin put s w).map (readLabel put)))
    ∃ u v, w=u++v ∧ pairs.length=p.streak ∧
      ∀ pair∈pairs, PairAt g u.length
        (physicalEvents (physicalRun s (u.map (readLabel put))) (v.map (readLabel put))) pair := by
  obtain ⟨u,v,E,C,W⟩ := Credit
  subst w
  have H := raw_clean_empty put inj g Wire Adj J base Good s Initial u C
  have P := wins_extract put inj g s u v p.streak H W
  exact ⟨u,v,rfl,P.1,P.2⟩

#print axioms raw_clean_empty
#print axioms raw_credit_extract

def StartsOutgoing (put : G × Bool → Fin n) (g : G) (s : Phase G) (w : List (Fin n)) : Prop :=
  ∀ i : Nat, (physicalEvents s (w.map (readLabel put)))[i]?=some (some (.start g)) →
    w[i]?=some (put (g,true))

theorem events_length {Z : Type v} (s : Phase G) (w : List (Label G Z)) :
    (physicalEvents s w).length=w.length := by
  induction w generalizing s with
  | nil => rfl
  | cons e w IH => simp only [physicalEvents,List.length_cons,IH]

theorem StartsOutgoing.append (put : G × Bool → Fin n) (g : G) (s : Phase G)
    (u v : List (Fin n)) (A : StartsOutgoing put g s u)
    (B : StartsOutgoing put g (physicalRun s (u.map (readLabel put))) v) :
    StartsOutgoing put g s (u++v) := by
  intro i E
  rw [List.map_append,events_append] at E
  have L : (physicalEvents s (u.map (readLabel put))).length=u.length := by
    rw [events_length,List.length_map]
  by_cases H : i<u.length
  · rw [List.getElem?_append_left (by rw [L]; exact H)] at E
    rw [List.getElem?_append_left H]
    exact A i E
  · have J : u.length≤i := by omega
    rw [List.getElem?_append_right (by rw [L]; exact J),L] at E
    rw [List.getElem?_append_right J]
    exact B _ E

theorem singleton_outgoing (put : G × Bool → Fin n) (g : G) (s : Phase G)
    (e : Fin n) (L : physicalEvent s (readLabel put e)=some (.start g) → e=put (g,true)) :
    StartsOutgoing put g s [e] := by
  intro i H
  cases i with
  | zero => exact congrArg some (L (Option.some.inj H))
  | succ i => simp [physicalEvents] at H

theorem pending_outgoing (put : G × Bool → Fin n) (inj : Function.Injective put)
    (g : G) (s : Phase G) (S : s g=none)
    {ph : ReportPulseWait.Phase} {w : List (Fin n)}
    (P : ReportPulseWarmup.Pending (put (g,false)) (put (g,true)) ph w)
    (N : ph≠ReportPulseWait.Phase.incoming) : StartsOutgoing put g s w := by
  induction P with
  | nil => simp [StartsOutgoing,physicalEvents]
  | @quiet ph w e P A B IH =>
    exact StartsOutgoing.append put g s w [e] (IH N)
      (singleton_outgoing put g _ e fun H => ((other_mark put g _ e A B).2.1 H).elim)
  | @out w P IH =>
    exact StartsOutgoing.append put g s w _ (IH (by decide))
      (singleton_outgoing put g _ _ (fun _=>rfl))
  | inc => exact (N rfl).elim
  | @outAgain w P IH =>
    have E : readLabel put (put (g,true))=.inl (g,true) := read_write put inj (.inl (g,true))
    have H := (pending_events put inj g s S P).1
    exact StartsOutgoing.append put g s w _ (IH (by decide))
      (singleton_outgoing put g _ _ (by rw [E]; simp [physicalEvent,H,phaseOf]))
  | inAgain => exact (N rfl).elim

theorem wins_outgoing (put : G × Bool → Fin n) (inj : Function.Injective put)
    (g : G) (s : Phase G) (S : s g=none) {J : Nat} {w : List (Fin n)}
    (W : ReportPulseWarmup.Wins (put (g,false)) (put (g,true)) J w) :
    StartsOutgoing put g s w := by
  induction W with
  | zero => simp [StartsOutgoing,physicalEvents]
  | @snoc k u v U V IH =>
    have H := (wins_events put inj g s S U).1
    have P := pending_outgoing put inj g _ H V (by decide)
    have E : readLabel put (put (g,false))=.inl (g,false) := read_write put inj (.inl (g,false))
    have PV := (pending_events put inj g (physicalRun s (u.map (readLabel put))) H V).1
    have T : physicalRun s ((u++v).map (readLabel put)) g=some true := by
      rw [List.map_append]
      unfold physicalRun at PV ⊢
      rw [List.foldl_append]
      exact PV
    rw [List.map_append] at T
    exact StartsOutgoing.append put g s (u++v) _ (StartsOutgoing.append put g s u v IH P)
      (singleton_outgoing put g _ _ (by rw [E]; simp [physicalEvent,T]))

/-- A matched suffix start keeps the original outgoing orientation
through recoding, since recoding fixes either letter in an empty pair. -/
theorem credit_origin_outgoing (put : G × Bool → Fin n) (inj : Function.Injective put)
    (g : G) (s : Phase G) (u v : List (Fin n)) (J : Nat)
    (Clean : physicalRun s (u.map (readLabel put)) g=none)
    (Win : ReportPulseWarmup.Wins (put (g,false)) (put (g,true)) J v)
    (pair : Nat × Nat)
    (Mem : pair ∈ extract g J (skeleton (armed s) ((encodeFin put s (u++v)).map (readLabel put)))) :
    (u++v)[pair.1]?=some (put (g,true)) := by
  obtain ⟨j,k,H,_,_,Start,_⟩ := (wins_extract put inj g s u v J Clean Win).2 pair Mem
  rw [H]
  simp only
  rw [List.getElem?_append_right (by omega),show u.length+j-u.length=j by omega]
  exact wins_outgoing put inj g _ Clean Win j Start

#print axioms wins_outgoing
#print axioms credit_origin_outgoing

theorem encode_keeps_starts {Z : Type v} (g : G) (s : Phase G)
    (w : List (Label G Z)) (i : Nat)
    (H : (physicalEvents s w)[i]?=some (some (.start g))) :
    (encode s w)[i]?=w[i]? := by
  induction w generalizing s i with
  | nil => simp [encode]
  | cons e w IH =>
    cases i with
    | succ i =>
      simp only [encode,List.getElem?_cons_succ]
      exact IH _ _ H
    | zero =>
      have E : physicalEvent s e=some (.start g) := Option.some.inj H
      suffices T : relabel s e=e by simp [encode,T]
      cases e with
      | inr z => rfl
      | inl ab =>
        obtain ⟨a,b⟩ := ab
        cases K : s a with
        | none => simp [relabel,K,ReportPulseRecode.flip]
        | some t => simp [physicalEvent,K] at E

theorem encodeFin_keeps_starts (put : G × Bool → Fin n) (inj : Function.Injective put)
    (g : G) (s : Phase G) (w : List (Fin n)) (i : Nat)
    (H : (skeleton (armed s) ((encodeFin put s w).map (readLabel put)))[i]?=
      some (some (.start g))) :
    (encodeFin put s w)[i]?=w[i]? := by
  rw [skeleton_encodeFin put inj] at H
  unfold encodeFin
  rw [List.getElem?_map,encode_keeps_starts g s _ i H,←List.getElem?_map,
    write_read_word]

#print axioms encodeFin_keeps_starts
end L4.ReportPulseWinsSkeleton
