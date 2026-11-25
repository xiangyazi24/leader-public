import Leader.L4.ShortReadForward
import Leader.L4.ShortReadReverseChart

namespace L4.ShortReadFlight
set_option maxRecDepth 8192
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetCycle ShortResetChart ShortResetForwardH2
open ShortReadForward ShortReadReturnHop

inductive Flight where
  | forward (i data : Nat)
  | returning (i : Nat) (ok : Bool) (data : Fin 64)
  | consumed (ok : Bool) (data : Fin 64)

def Active {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n) : Flight → Prop
  | .forward i data => Forward C.route x i data
  | .returning i ok data => ShortReadReverseChart.Returning C x i ok data
  | .consumed ok data => ShortReadReverseChart.Consumed C x ok data

def live : Flight → Prop
  | .forward .. | .returning .. => True
  | .consumed .. => False

def datum (t : Token) : Fin 64 := ⟨t.payload%64,Nat.mod_lt _ (by decide)⟩

private theorem canonical_coordinates (t : Token) (ok : Bool) (d : Fin 64)
    (P : t=readReply ok d) : (t.outcome==0)=ok ∧ (ok=true → datum t=d) := by
  rw [P]
  constructor
  · cases ok <;> rfl
  · intro E
    subst ok
    apply Fin.ext
    exact Nat.mod_eq_of_lt d.isLt

def next {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (e : Fin n) : Flight → Flight
  | .forward i d =>
    if e=nextAt C.root i then
      if i+1<C.L then .forward (i+1) (hopPacket x e (C.route.port i) (C.route.port (i+1))).payload
      else
        let t := replyPacket x e (C.route.port i)
        .returning i (t.outcome==0) (datum t)
    else .forward i d
  | .returning i ok d =>
    match nextStage C e (.rev i) with
    | .rev j => .returning j ok d
    | _ => .consumed ok d
  | .consumed ok d => .consumed ok d

private theorem entered_reverse {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (ok : Bool) (d : Fin 64) (A : Turned C.route x ok d) :
    ShortReadReverseChart.Returning C x (C.L-1) ok d := by
  have L := C.positive
  refine ⟨by omega,A.1,?_⟩
  intro i I
  change bits C.route x i=encode (ShortReadReverseChart.trailAt ok d (C.L-1) i)
  by_cases H : i<C.L-1
  · simpa [ShortReadReverseChart.trailAt,H] using A.2.1 i H
  · have G : i=C.L-1 := by omega
    subst i
    have T := A.2.2
    change bits C.route x (C.L-1)=encode (readReply ok d) at T
    simpa [ShortReadReverseChart.trailAt] using T

theorem read_flight_active_step {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (e : Fin n) (N : 1<n) (heads : ∀ j, header x j=h j)
    (f : Flight) (L : live f) (A : Active C x f) :
    Active C (rawNext s x e) (next C x e f) := by
  cases f with
  | consumed => exact False.elim L
  | returning i ok d =>
    have S := ShortReadReverseChart.returning_step C x N heads e i A
    dsimp only [next] at S ⊢
    split at S <;> rename_i E <;> simp only [E,Active] <;> first | exact S | contradiction
  | forward i d =>
    have U := forward_all_mark C.route x e (edge_sep N e) heads i d A
    change (if e=nextAt C.root i then
      if i+1<C.L then
        Forward C.route (rawNext s x e) (i+1) (hopPacket x e (C.route.port i) (C.route.port (i+1))).payload
      else ∃ ok p, Turned C.route (rawNext s x e) ok p ∧ replyPacket x e (C.route.port i)=readReply ok p
      else Forward C.route (rawNext s x e) i d) at U
    by_cases E : e=nextAt C.root i
    · by_cases H : i+1<C.L
      · simpa only [next,if_pos E,if_pos H,Active] using U
      · have B : i=C.L-1 := by
          have I : i<C.L := A.1
          omega
        simp only [if_pos E,if_neg H] at U
        obtain ⟨ok,p,S,Eq⟩ := U
        let t := replyPacket x e (C.route.port i)
        have K := canonical_coordinates t ok p Eq
        simp only [next,if_pos E,if_neg H,Active]
        change ShortReadReverseChart.Returning C (rawNext s x e) i (t.outcome==0) (datum t)
        rw [K.1,B]
        cases ok
        · have Q : readReply false p=readReply false (datum t) := rfl
          have T : Turned C.route (rawNext s x e) false (datum t) :=
            ⟨S.1,S.2.1,S.2.2.trans (congrArg encode Q)⟩
          exact entered_reverse C _ _ _ T
        · rw [K.2 rfl]
          exact entered_reverse C _ _ _ S
    · simpa only [next,if_neg E,Active] using U

/-- Chronological raw replay with an explicit proof-only flight cursor. -/
def trace {s n : Nat} {h : Fin n → Bool} (C : Chart h) :
    Raw s n → Flight → List (Fin n) → Flight
  | _, f, [] => f
  | x, f, e::w => trace C (rawNext s x e) (next C x e f) w

def beforeConsume {s n : Nat} {h : Fin n → Bool} (C : Chart h) :
    Raw s n → Flight → List (Fin n) → Prop
  | _, _, [] => True
  | x, f, e::w => live f ∧ beforeConsume C (rawNext s x e) (next C x e f) w

theorem active_through_run {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (w : List (Fin n)) (x : Raw s n) (f : Flight)
    (H : H2Ready x) (heads : ∀ j,header x j=h j) (A : Active C x f)
    (B : beforeConsume C x f w) :
    Active C (rawRun x w) (trace C x f w) := by
  induction w generalizing x f with
  | nil => exact A
  | cons e w ih =>
    have B' : live f ∧ beforeConsume C (rawNext s x e) (next C x e f) w := B
    exact ih (rawNext s x e) (next C x e f) (h2_ready_closed N x e H)
      (fun j=>(H1.raw_h1_selected_frozen N x e j H.1).trans (heads j))
      (read_flight_active_step C x e (by omega) heads f B'.1 A) B'.2

theorem active_from_clean_issue3 {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (w : List (Fin n)) (x : Raw s n) (H : H2Ready x)
    (heads : ∀ j,header x j=h j) (I : ShortClearLaunch.ClearIssue C x 3)
    (B : beforeConsume C (rawNext s x (RearTrace.predecessor C.root)) (.forward 0 64) w) :
    let d := RearTrace.predecessor C.root
    Active C (rawRun x (d::w)) (trace C (rawNext s x d) (.forward 0 64) w) := by
  let d := RearTrace.predecessor C.root
  exact active_through_run C N w (rawNext s x d) _ (h2_ready_closed N x d H)
    (fun j=>(H1.raw_h1_selected_frozen N x d j H.1).trans (heads j))
    (forward_from_actual_issue3 C x heads I) B

#print axioms read_flight_active_step
#print axioms active_through_run
#print axioms active_from_clean_issue3
end L4.ShortReadFlight
