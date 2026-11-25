import Leader.L4.ShortHelloAdmitCodec
import Leader.L4.ShortHelloForward
import Leader.L4.ShortClearLaunch
import Leader.L4.ShortPhaseRank

namespace L4.ShortPreReadGrants
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetChart ShortResetCycle ShortResetForwardH2 ShortControllerEntrance
open ShortHelloAdmitCodec ShortResetRow

/-- A slot distribution rules out a fresh ask on any header of this
owner chart. -/
def NoAsk {s n : Nat} {h : Fin n → Bool} (R : Route h) (x : Raw s n) : Prop :=
  ∀ j, j<R.length → h (nextAt R.root j)=true →
    (headerGrantView (x (nextAt R.root j)).mis1).ask (R.port j)=false

/-- The exact old K formats used by the whole pre-READ tour.
The proof can use this decoder test without assuming exterior owners quiet. -/
theorem pre_read_no_ask (u : BitVec 96) (j : Fin 3)
    (P : oldK true u j=E ∨ oldK true u j=T ∨ oldK true u j=helloForward ∨
      oldK true u j=helloReply ∨ (∃ won, oldK true u j=admitReply won) ∨
      ∃ won race, oldK true u j=admitForward won race) :
    (headerGrantView u).ask j=false := by
  change ((oldK true u j).tag==2 && !(oldK true u j).fault &&
    (oldK true u j).opcode==3)=false
  rcases P with H|H|H|H|⟨won,H⟩|⟨won,race,H⟩ <;> rw [H] <;> rfl

theorem no_ask_keeps_grants_absent {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (heads : ∀ j,header x j=h j) (G : ShortHelloForward.NoGrants R x)
    (A : NoAsk R x) :
    ShortHelloForward.NoGrants R (rawNext s x e) := by
  intro j J H
  exact ShortGrantPersistence.absent_until_ask x e (nextAt R.root j) (R.port j)
    sep ((heads _).trans H) (G j J H) (fun _=>A j J H)

theorem no_ask_tape_keeps_grants_absent {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (N : 5≤n) (x : Raw s n) (I : H2Ready x) (heads : ∀ j,header x j=h j)
    (w : List (Fin n)) (G : ShortHelloForward.NoGrants R x)
    (A : ∀ (p : List (Fin n)) e q, w=p++e::q → NoAsk R (rawRun x p)) :
    ShortHelloForward.NoGrants R (rawRun x w) := by
  induction w generalizing x with
  | nil => exact G
  | cons e w ih =>
    change ShortHelloForward.NoGrants R (rawRun (rawNext s x e) w)
    have h' : ∀ j,header (rawNext s x e) j=h j :=
      fun j=>(H1.raw_h1_selected_frozen N x e j I.1).trans (heads j)
    refine ih (rawNext s x e) (h2_ready_closed N x e I) h'
      (no_ask_keeps_grants_absent R x e (edge_sep (by omega) e) heads G (A [] e w rfl)) ?_
    intro p m q W
    exact A (e::p) m q (congrArg (List.cons e) W)

/-- Decode the combined PC only after the actual row, then feed the
canonical-empty chart directly into the already checked launch theorem. -/
theorem clear_issue_of_pc {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (op : Nat) (P : op<7) (clear : ShortEmptyOwnership.Clear C x)
    (phase : pc (x C.root).mis1=8+op) : ShortClearLaunch.ClearIssue C x op := by
  rw [ShortPhaseRank.pc_fields] at phase
  have B : get (x C.root).mis1 78 3 (by decide)<8 :=
    ((lane 78 3 (by decide)).read (x C.root).mis1).isLt
  exact ⟨P,clear,by omega,by omega⟩

/-- The successful and denied ADMIT exits have the precise launch
interface for the next tour, once the reverse invariant supplies the
cleared nonroot slots. Only the actual source consume clears K0. -/
theorem admit_exit_clear_issue {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (heads : ∀ j,header x j=h j)
    (phase : get (x C.root).mis1 81 2 (by decide)=2)
    (cmd : get (x C.root).mis1 78 3 (by decide)=2)
    (won : Bool) (D : bits C.route x 0=encode (admitReply won))
    (rest : ∀ j, 0<j → j<C.L →
      bits C.route (rawNext s x (RearTrace.predecessor C.root)) j=encode E) :
    ShortClearLaunch.ClearIssue C (rawNext s x (RearTrace.predecessor C.root))
      (if won then 3 else 0) := by
  let e := RearTrace.predecessor C.root
  let y := rawNext s x e
  have E : rightNeighbor e=C.root := RearTrace.right_predecessor C.root
  have H : header x (rightNeighbor e)=true := by rw [E,heads,C.rootHeader]
  have N := C.length_lt
  have P := C.positive
  have D' : (kField 0).read (x C.root).mis1=encode (admitReply won) := by
    change (kField (ShortResetChart.lane C.a C.b 0)).read (x C.root).mis1=_ at D
    rwa [C.rootPort] at D
  obtain ⟨K,PC⟩ := consume_admit x e (edge_sep (by omega) e) H
    (by simpa only [E] using phase) (by simpa only [E] using cmd) won
    (by simpa only [E] using D')
  rw [E] at K PC
  have Clear : ShortEmptyOwnership.Clear C y := by
    intro j J
    by_cases Z : j=0
    · subst j
      change (kField (ShortResetChart.lane C.a C.b 0)).read (y C.root).mis1=_
      rwa [C.rootPort]
    · exact rest j (by omega) J
  apply clear_issue_of_pc C y _ (by cases won <;> decide) Clear
  cases won <;> exact PC

#print axioms pre_read_no_ask
#print axioms no_ask_keeps_grants_absent
#print axioms no_ask_tape_keeps_grants_absent
#print axioms clear_issue_of_pc
#print axioms admit_exit_clear_issue
end L4.ShortPreReadGrants
