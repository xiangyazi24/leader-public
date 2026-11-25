import Leader.L4.BStarNeedQuietRead
import Leader.L4.BStarNativeOffsetTrace
import Leader.L4.BStarBitOneObservation
import Leader.L4.BStarFirstDoorService

namespace L4.BStarNeedOneRead
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail BStarNeedTrace BStarNeedQuietRead
open BStarClearanceRaceMark BStarOwnerControlHistory BStarSeparatorControl
open BStarH6Ordinal BStarClearanceOffset BStarClearanceForward BStarSeparatorRing BStarBitOneObservation BStarFirstDoorService BStarAcquireForwardTrace

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

def AtMostOne (base : X) (addr : Nat→Pos n) (len g : Nat) (x : X) (w : List (Fin n)) : Prop :=
  ∀ u e v u' e' v', w=u++e::v → w=u'++e'::v' → u.length<u'.length →
    FirstRead hp base addr len g (play x u) e → ¬FirstRead hp base addr len g (play x u') e'

private theorem split_busy {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {w : List (Fin n)} {z endC : Cursor} (T : BusyOnly hp base addr len op x z w endC) :
    ∀ u v,w=u++v → ∃ t, BusyOnly hp base addr len op x z u t ∧
      BusyOnly hp base addr len op (play x u) t v endC := by
  induction T with
  | nil I =>
    intro u v S
    obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp S.symm
    exact ⟨_,.nil I,.nil I⟩
  | @cons x z t endC e w I E T ih =>
    intro u v S
    cases u with
    | nil =>
      change e::w=v at S
      subst v
      exact ⟨_,.nil I,.cons I E T⟩
    | cons a u =>
      obtain ⟨rfl,P⟩ := List.cons.inj S
      obtain ⟨m,U,V⟩ := ih u v P
      exact ⟨m,.cons I E U,V⟩

private theorem observation {base x : X} {addr : Nat→Pos n} {len g : Nat}
    {e i : Fin n} {z : Cursor} (idx : addr g=(i,1))
    (I : Current hp base addr len x (.busy bitOp z))
    (read : FirstRead hp base addr len g x e) :
    Observes i g x z e := by
  have Eq := (Mode.busy.inj (first_read_mode hp I read)).2
  obtain ⟨p,P,F,O,R,U,A,incidentMark⟩ := read.2
  change atCursor x (addr g)=.forward p at P
  rw [idx] at P incidentMark
  exact ⟨Eq,incidentMark,p,P,F,O,U,A,R⟩

/-- The actual BIT tour cannot contain two fresh observations, even
on a prefix that has not returned or even left the gate yet. -/
theorem flight_at_most_one {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (g : Nat) (G : g<len) (idx : S.getD g fall=(i,1))
    (ord : oldOrdinal B base hh i=4) (qx : Q x) (offset : correct (oldH6 B base) hh 5 x)
    {w : List (Fin n)} {a b : Cursor} (T : BusyOnly hp base (fun j=>S.getD j fall) len bitOp x a w b) :
    AtMostOne hp base (fun j=>S.getD j fall) len g x w := by
  intro u e v u' e' v' L R ordered first second
  have P : u<+:u' := List.prefix_of_prefix_length_le ⟨e::v,L.symm⟩ ⟨e'::v',R.symm⟩ (Nat.le_of_lt ordered)
  obtain ⟨mid,E⟩ := P
  cases mid with
  | nil =>
    have eq : u=u' := by simpa using E
    have LL := congrArg List.length eq
    omega
  | cons f mid =>
    have truth : e::v=(f::mid)++e'::v' := by
      apply List.append_cancel_left (as:=u)
      rw [←List.append_assoc,E]
      exact L.symm.trans R
    obtain ⟨rfl,remaining⟩ := List.cons.inj truth
    obtain ⟨z,front,after⟩ := split_busy hp T u (e::v) L
    have middle : e::v=(e::mid)++e'::v' := congrArg (List.cons e) remaining
    obtain ⟨z',M,finish⟩ := split_busy hp after (e::mid) (e'::v') middle
    have align : play x u'=play (play x u) (e::mid) := by
      rw [←E,BStarResetSchedule.run_append]
    have read₁ := observation hp idx (busy_start hp after) first
    have read₂ := observation hp idx (busy_start hp finish) (align ▸ second)
    have stableOffsets (z : X) (w : List (Fin n)) (H : Q z)
        (offset : correct (oldH6 B base) hh 5 z) : correct (oldH6 B base) hh 5 (play z w) := by
      induction w generalizing z with
      | nil => exact offset
      | cons edge rest ih =>
        exact ih (step z edge) (closed _ H edge) (BStarClearanceOffset.stable hp _ hh z edge (sep edge)
          (fun j=>(congrArg Prod.fst (fiber z H j)).symm) (BStarClearanceOffsetMask.leftFrame hp z edge) offset)
    have q := stable_word hp Q closed x u qx
    have off := stableOffsets x u qx offset
    have scope : ∀ pre f post,e::mid=pre++f::post →
        let z := play (play x u) pre
        (∀ j,oldH6 B z j=oldH6 B base j) ∧ correct (oldH6 B base) hh 5 z := by
      intro pre _ _ _
      exact ⟨fun j=>(congrArg Prod.fst (fiber _ (stable_word hp Q closed _ pre q) j)).symm,
        stableOffsets _ pre q off⟩
    exact BStarBitOneObservation.no_second_observation hp C sep i g G idx ord M scope read₁ read₂

private theorem locate_mark {α : Type} (a b u : List α) (e : α) (v : List α)
    (split : a++b=u++e::v) :
    (∃ q,a=u++e::q) ∨ ∃ p,u=a++p ∧ b=p++e::v := by
  induction a generalizing u with
  | nil => exact .inr ⟨u,rfl,split⟩
  | cons t a ih =>
    cases u with
    | nil =>
      have Eq := (List.cons.inj (show t::(a++b)=e::v from split)).1
      subst e
      exact .inl ⟨a,rfl⟩
    | cons f u =>
      obtain ⟨rfl,M⟩ := List.cons.inj split
      rcases ih u M with ⟨q,N⟩|⟨p,N,R⟩
      · exact .inl ⟨q,congrArg (List.cons t) N⟩
      · exact .inr ⟨p,congrArg (List.cons t) N,R⟩

private theorem locate_read {base x : X} {addr : Nat→Pos n} {len g : Nat}
    (pre bit post : List (Fin n)) {sz u v : List (Fin n)} {e : Fin n}
    (A : ∀ u e v,pre=u++e::v → ¬FirstRead hp base addr len g (play x u) e)
    (Z : ∀ u e v,post=u++e::v → ¬FirstRead hp base addr len g (play (play x (pre++bit)) u) e)
    (W : sz=pre++(bit++post)) (split : sz=u++e::v)
    (read : FirstRead hp base addr len g (play x u) e) :
    ∃ uBit vBit,u=pre++uBit ∧ bit=uBit++e::vBit ∧
      FirstRead hp base addr len g (play (play x pre) uBit) e := by
  rcases locate_mark pre (bit++post) u e v (W.symm.trans split) with ⟨q,R⟩|⟨p,E,R⟩
  · exact (A u e q R read).elim
  · rcases locate_mark bit post p e v R with ⟨q,BSplit⟩|⟨t,S,D⟩
    · refine ⟨p,q,E,BSplit,?_⟩
      rwa [E,BStarResetSchedule.run_append] at read
    · have eq : play x u=play (play x (pre++bit)) t := by
        rw [E,S,←List.append_assoc,BStarResetSchedule.run_append]
      exact (Z t e v D (eq ▸ read)).elim

/-- Full matched pre-publication itinerary: only its unique real BIT
flight can contain a first observation, and that flight cannot
observe twice. This is independent of any required coverage inside
the observed finite prefix. -/
theorem matched_at_most_one {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (g : Nat) (G : g<len) (idx : S.getD g fall=(i,1))
    (ord : oldOrdinal B base hh i=4) (qx : Q x) (offset : correct (oldH6 B base) hh 5 x)
    (k : Nat) (w : List (Fin n))
    (T : Matched hp base (fun j=>S.getD j fall) len k x w) :
    AtMostOne hp base (fun j=>S.getD j fall) len g x w := by
  obtain ⟨sf,w₁,bit,w₂,com,word,phase⟩ := T
  let door := RearTrace.predecessor (S.getD 0 fall).1
  let pre := sf++door::(w₁++[door])
  let post := door::(w₂++door::com)
  have ⟨align,quiet1,flight,quiet2⟩ := isolate_bit hp (g:=g) phase
  have W : w=pre++(bit++post) := word.trans align
  have skip1 := silent_span hp quiet1
  have skip2 : ∀ u e v,post=u++e::v →
      ¬FirstRead hp base (fun j=>S.getD j fall) len g (play (play x (pre++bit)) u) e := by
    rw [BStarResetSchedule.run_append]
    exact silent_span hp quiet2
  have q := stable_word hp Q closed x pre qx
  have offset' : correct (oldH6 B base) hh 5 (play x pre) := by
    apply BStarNativeOffsetTrace.closed_word hp _ hh sep x pre offset
    intro u v _
    exact funext (fun j=>(congrArg Prod.fst (fiber _ (stable_word hp Q closed x u qx) j)).symm)
  have middle := flight_at_most_one hp C Q fiber closed sep i g G idx ord q offset' flight
  intro u e v u' e' v' E F order first second
  obtain ⟨a,b,A,Z,read⟩ := locate_read hp pre bit post skip1 skip2 W E first
  obtain ⟨a',b',A',Z',read'⟩ := locate_read hp pre bit post skip1 skip2 W F second
  have L : u.length=pre.length+a.length := (congrArg List.length A).trans (List.length_append ..)
  have L' : u'.length=pre.length+a'.length := (congrArg List.length A').trans (List.length_append ..)
  have H : a.length<a'.length := by rw [L,L'] at order; omega
  exact middle a e b a' e' b' Z Z' H read read'

#print axioms flight_at_most_one
#print axioms matched_at_most_one
end L4.BStarNeedOneRead
