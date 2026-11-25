import Leader.L4.BStarBitReplay
import Leader.L4.BStarOwnerLaunchOrigin
import Leader.L4.BStarClearanceObserveJoined
import Leader.L4.BStarLongKOne
import Leader.L4.BStarResetQuietTable

namespace L4.BStarBitSegment
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongRouting BStarLongWork BStarLongEvents
open BStarClearanceObserveJoined BStarResetQuiet BStarResetQuietTable BStarLongLiteral BStarLongKOne
open BStarBitParity
set_option maxRecDepth 4096

private theorem norm_frame (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : Side) (p : Payload) (B : bound g (readK raw) ⟨s,1⟩=.forward p)
    (F : p.fault=0) : avoids ⟨s,1⟩ (normalization g (readK raw)) := by
  intro w hw E
  rcases List.mem_append.mp hw with hw|hw
  · obtain ⟨a,_,h⟩ := List.mem_filterMap.mp hw
    dsimp only at h
    split at h
    · rename_i guard
      have eq : a=(⟨s,1⟩ : AtK) := (congrArg Prod.fst (Option.some.inj h)).trans E
      subst a
      simp [B,isFault,F] at guard
    · contradiction
  · obtain ⟨a,ha,h⟩ := List.mem_map.mp hw
    have eq : a=(⟨s,1⟩ : AtK) := (congrArg Prod.fst h).trans E
    subst a
    cases s <;> cases X : g.1.inside <;> cases Y : g.2.inside <;>
      simp [discarded,X,Y,L,R] at ha

private theorem fold_hold (a : AtK) (ws : List KWrite) (raw : BitVec 52)
    (H : avoids a ws) : ws.foldl (fun k w => putRaw k a w) raw=raw := by
  induction ws generalizing raw with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldl_cons,ih _ (fun q hm => H q (List.mem_cons_of_mem _ hm))]
    simp [putRaw,Ne.symm (H w List.mem_cons_self)]

private theorem silent_avoids (g : Pair LongGeometry) (old : ReadK) (pre : List KWrite)
    (a : AtK) (p : Payload) (B : bound g old a=.forward p)
    (S : observe a (geometry g a.side) p=none) :
    avoids a (observations g old pre) := by
  intro w hw E
  obtain ⟨j,_,J⟩ := List.mem_filterMap.mp hw
  split at J
  · contradiction
  · split at J <;> try contradiction
    rename_i P _
    cases Z : observe j (geometry g j.side) P with
    | none => simp [Z] at J
    | some Q =>
      have H := (congrArg Prod.fst (Option.some.inj (by simpa [Z] using J))).trans E
      change j=a at H
      subst j
      simp_all

theorem joined_complete_incoming (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (first : Side)
    (v : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let a : AtK := R 1
    bound g (readK raw) a=.forward v →
    v.fault=0 → v.opcode.toNat=bitOp → v.race=finalCode first →
    gate bitOp 1 (g.2)=true →
    (g.2.axes.h6=false ∧ bound g (readK raw) (L 1)=.trail) →
    readRaw (Pair.map LargeSite.long (largePair b x)) a=
      readRaw raw a := by
  dsimp only
  intro B F P K G incoming
  obtain ⟨body,trail⟩ := incoming
  have hc : advance∈orderedCommands (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x) := by
    apply (one_mem _ advance (by decide)).mpr
    simp [body]
  have M := (link_avoids _ (Pair.map LargeSite.long x) advance (R 1) hc rfl rfl (show LinkHold _ _ by
    change LinkHold (bound _ _ (L 1)) (bound _ _ (R 1))
    rw [trail,B]; exact .tf v)).2
  have H : avoids (R 1) (_ ++ _) := fun w hw E => (List.mem_append.mp hw).elim
    (fun N => norm_frame _ _ .right v B F w N E) (fun N => M w N E)
  have O : observe (R 1) (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x).2 v=none := by
    cases first <;> simp [observe,F,P,K,finalCode]
  rw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x (R 1)
      (fun ea _ => (by have T := congrArg (fun z : AtK => z.occurrence.val) ea; change (1 : Nat) = 0 at T; omega)),
      raw_transit _ _ _ (by change (1:Nat)≠0; decide),routing_parts,List.foldl_append,
      fold_hold _ _ _ H]
  exact fold_hold _ _ _ (silent_avoids _ _ _ _ v B O)
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarResetChartTouch BStarResetChartIndex BStarAcquireLiteralChain
open BStarAcquireAnchors BStarLongFiberOwner BStarLongKOne BStarClearanceRaceMark
open BStarResetMarkAdapter BStarGeneratedOwner BStarSeparatingRail BStarAcquireForwardTrace
open BStarClearanceOffset BStarBitGateGeometry BStarBitParity BStarBitFirstRing BStarBitFollowRing BStarBitDepart BStarBitReplay BStarOwnerLaunchOrigin
open BStarBankTrace (sideFlag)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

private theorem complete_incoming {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i) (ready : correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (idx : S.getD k fall=(i,1)) (O : oldOrdinal B base hh i=4)
    (now : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out k)))
    (s : Side) (v : Payload) (old : bind (longGeometry B (x i)) 1 (atSite (x i).long 1)=.forward v)
    (F : v.fault=0) (op : v.opcode.toNat=bitOp) (done : v.race=finalCode s) :
    atSite (step x (incident i .right) i).long 1=atSite (x i).long 1 := by
  let e := incident i .right
  have I : rightNeighbor e=i := RearTrace.right_predecessor _
  have G := (bit_gate_iff hp hh fixed ready i 1).mpr ⟨rfl,O⟩
  have bd : oldH6 B base i=false := Bool.eq_false_iff.mpr (fun H => by
    have Z := (ordinal_zero _ hh i).mpr H
    change ordinal _ hh i=4 at O
    omega)
  have body : oldH6 B x (rightNeighbor e)=false := by rw [I,fixed,bd]
  have T := predecessor_trail hp C i k idx O now
  let pair := (x e,x (rightNeighbor e))
  have out := joined_complete_incoming k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair s v
    (show bind (longGeometry B (x (rightNeighbor e))) 1 (atSite (x (rightNeighbor e)).long 1)=.forward v by rwa [I])
    F op done (show gate bitOp 1 (longGeometry B (x (rightNeighbor e)))=true by rwa [I])
    ⟨body,show bind (longGeometry B (x e)) 1 (atSite (x e).long 1)=.trail by
      change bind _ _ (atSite (x (RearTrace.predecessor i)).long 1)=_
      rw [T]; rfl⟩
  have pst : step x e i=(largePair B pair).2 := by
    rw [←I]
    simp [AllSizeS1Geometry.step,Ne.symm (sep e),pair]
  change atSite (step x e i).long 1=_
  rw [pst,←I]
  exact congrArg BStarLongToken.decode out

inductive Phase where
  | fresh
  | first (s : Side)
  | complete (s : Side)
deriving DecidableEq

def cycleCode : Phase → BitVec 3
  | .fresh => 1
  | .first s => firstCode s
  | .complete s => finalCode s

def nextPhase {n} (i : Fin n) (phase : Phase) (e : Fin n) : Option Phase :=
  if e=incident i .left then
    match phase with
    | .fresh => some (.first .left)
    | .first .left => some phase
    | .first .right => some (.complete .right)
    | .complete _ => none
  else if e=incident i .right then
    match phase with
    | .fresh => some (.first .right)
    | .first .right => some phase
    | .first .left => some (.complete .left)
    | .complete _ => some phase
  else some phase

/-- Exact finite-mark scanner. No success on an empty tape or if
there are extra marks after the completing outgoing mark. -/
def readSegment {n} (i : Fin n) (phase : Phase) : List (Fin n) → Option Side
  | [] => none
  | e::es => match nextPhase i phase e with
    | some q => readSegment i q es
    | none => match phase, es with
      | .complete s, [] => some s
      | _,_ => none

private theorem bind_gate (g : LongGeometry) (v : Payload)
    (G : gate bitOp 1 g=true)
    (F : v.fault=0) (P : v.opcode.toNat=bitOp) (O : v.outcome=0) (A : v.argument=0)
    (R : 1≤v.race.toNat ∧ v.race.toNat≤5) :
    bind g 1 (.forward v)=.forward v := by
  cases v
  simp_all [BStarLongCommand.bind,bitOp,forwardWidth,admit,cropped,low]

private theorem code_bounds (p : Phase) : 1≤(cycleCode p).toNat ∧ (cycleCode p).toNat≤5 := by
  cases p with
  | fresh => decide
  | first s => cases s <;> decide
  | complete s => cases s <;> decide

def slot (x : X) (i : Fin n) : Fin 11 :=
  if oldH6 B x (rightNeighbor i) then 2 else 1

theorem next_not_gate {base x : X} {hh : ∃ i,oldH6 B base i=true}
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i) (ready : correct (oldH6 B base) hh 5 x)
    (i : Fin n) (O : oldOrdinal B base hh i=4) :
    gate bitOp (slot hp x i) (longGeometry B (x (rightNeighbor i)))=false := by
  apply Bool.eq_false_iff.mpr
  intro H
  have K := (bit_gate_iff hp hh fixed ready (rightNeighbor i) _).mp H
  have J := ordinal_right (oldH6 B base) hh i
  change oldOrdinal B base hh (rightNeighbor i)=_ at J
  rw [K.2] at J
  change ordinal (oldH6 B base) hh i=4 at O
  rw [O] at J
  split at J <;> omega

private theorem phase_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i) (ready : correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (idx : S.getD k fall=(i,1)) (O : oldOrdinal B base hh i=4)
    (now : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out k)))
    (v : Payload) (F : v.fault=0) (op : v.opcode.toNat=bitOp)
    (zero : v.outcome=0) (arg : v.argument=0)
    (phase : Phase) (old : atSite (x i).long 1=.forward {v with race:=cycleCode phase})
    (off : gate bitOp (slot hp x i) (longGeometry B (x (rightNeighbor i)))=false)
    (e : Fin n) :
    match nextPhase i phase e with
    | some phase' => atSite (step x e i).long 1=.forward {v with race:=cycleCode phase'}
    | none => ∃ s, phase=.complete s ∧ e=i ∧ atSite (step x e i).long 1=.trail ∧
        atSite (step x e (rightNeighbor i)).long (slot hp x i)=.forward (cleanBit v s) := by
  let f := {v with race:=cycleCode phase}
  have G := (bit_gate_iff hp hh fixed ready i 1).mpr ⟨rfl,O⟩
  have bd : bind (longGeometry B (x i)) 1 (atSite (x i).long 1)=.forward f := by
    rw [old]
    exact bind_gate _ f G F op zero arg (code_bounds phase)
  have diff : incident i .left≠incident i .right := by
    intro E
    have Q := congrArg rightNeighbor E
    exact sep i (by rw [show rightNeighbor (incident i .right)=i from RearTrace.right_predecessor i] at Q; exact Q.symm)
  have outside (L : e≠incident i .left) (R : e≠incident i .right) :
      atSite (step x e i).long 1=.forward f := by
    have U : i≠rightNeighbor e := fun E => R (by
      change e=RearTrace.predecessor i
      rw [E,RearTrace.predecessor_right])
    have V : i≠e := Ne.symm L
    simp [AllSizeS1Geometry.step,V,U,old,f]
  by_cases L : e=incident i .left
  · subst e
    simp only [nextPhase,if_true]
    cases phase with
    | fresh => exact (first_mark hp C fixed ready sep i k idx O now f bd F op rfl).1 .left
    | first s =>
      have H := (follow_mark hp C fixed ready sep i k idx O now f bd F op s rfl).1 .left
      cases s
      · simpa only [if_pos rfl] using H.trans (by exact old)
      · rw [if_neg (show Side.left≠Side.right by decide)] at H; rw [H]; rfl
    | complete s =>
      have H := BStarBitReplay.leave hp (base:=base) i O [] [] s f old F op zero arg rfl
        (by simp) fixed ready (sep i) off
      exact ⟨s,rfl,rfl,H.1,H.2⟩
  · by_cases R : e=incident i .right
    · subst e
      simp only [nextPhase,if_neg diff.symm,if_true]
      cases phase with
      | fresh => exact (first_mark hp C fixed ready sep i k idx O now f bd F op rfl).1 .right
      | first s =>
        have H := (follow_mark hp C fixed ready sep i k idx O now f bd F op s rfl).1 .right
        cases s
        · rw [if_neg (show Side.right≠Side.left by decide)] at H; rw [H]; rfl
        · simpa only [if_pos rfl] using H.trans (by exact old)
      | complete s => exact (complete_incoming hp C fixed ready sep i k idx O now s f bd F op rfl).trans old
    · simpa only [nextPhase,if_neg L,if_neg R] using outside L R

/-- Every actual first departure from this outward cursor follows the
finite handshake scanner, allowing arbitrary intervening spectators and
any repetitions of the first side. The suffix is not replayed or edited.
Scope supplies settled correct geometry on proper prefixes, not proposed
actions or a hypothesized departure mark. -/
theorem busy_segment {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (idx : S.getD k fall=(i,1)) (O : oldOrdinal B base hh i=4)
    (inner : k<len) (v : Payload) (F : v.fault=0) (op : v.opcode.toNat=bitOp)
    (zero : v.outcome=0) (arg : v.argument=0)
    {w : List (Fin n)} {z d : Cursor}
    (H : BusyOnly hp base (fun j=>S.getD j fall) len bitOp x z w d) :
    z=.out k → d≠.out k → ∀ phase,
    atSite (x i).long 1=.forward {v with race:=cycleCode phase} →
    (∀ pre e post, w=pre++e::post →
      let y := play hp x pre
      (∀ j,oldH6 B y j=oldH6 B base j) ∧
      correct (oldH6 B base) hh 5 y) →
    ∃ pre post s, w=(pre++[i])++post ∧ readSegment i phase (pre++[i])=some s ∧
      let y := play hp x pre
      atSite (y i).long 1=.forward {v with race:=finalCode s} ∧
      atSite (step y i i).long 1=.trail ∧
      atSite (step y i (rightNeighbor i)).long (slot hp y i)=.forward (cleanBit v s) ∧
      BusyOnly hp base (fun j=>S.getD j fall) len bitOp (step y i) (.out (k+1)) post d := by
  induction H with
  | nil _ => intro eq ne; exact (ne eq).elim
  | @cons x z b dest e w I E tail ih =>
    intro eq ne phase old scope
    subst z
    obtain ⟨fixed,ready⟩ := scope [] e w rfl
    have off := next_not_gate hp fixed ready i O
    have localStep := phase_step hp C fixed ready sep i k idx O I v F op zero arg phase old off e
    have nextGood := (busy_start hp tail).2.1
    have adv : Advance len (.out k) b := by
      cases E with
      | transit _ _ _ _ seen =>
        cases seen with
        | cons _ _ A _ rest => cases rest; exact A
    cases NX : nextPhase i phase e with
    | some q =>
      rw [NX] at localStep
      have Bk : b=.out k := by
        cases adv with
        | stay => rfl
        | forward =>
          have trail := nextGood.2.2 k (by omega)
          change atCursor (step x e) (S.getD k fall)=.trail at trail
          rw [idx] at trail
          exact False.elim (Token.noConfusion (localStep.symm.trans trail))
        | turn => omega
      subst b
      obtain ⟨pre,post,s,W,R,t⟩ := ih rfl ne q localStep
        (fun u a b E => scope (e::u) a b (congrArg (List.cons e) E))
      refine ⟨e::pre,post,s,congrArg (List.cons e) W,?_,t⟩
      change (match nextPhase i phase e with
        | some a => readSegment i a (pre++[i])
        | none => _) = _
      rwa [NX]
    | none =>
      rw [NX] at localStep
      obtain ⟨s,P,eq,T,V⟩ := localStep
      subst e
      subst phase
      have Bk : b=.out (k+1) := by
        cases adv with
        | stay =>
          obtain ⟨pay,H⟩ := nextGood.2.1
          change atCursor (step x i) (S.getD k fall)=.forward pay at H
          rw [idx] at H
          exact False.elim (Token.noConfusion (T.symm.trans H))
        | forward => rfl
        | turn => omega
      subst b
      refine ⟨[],w,s,rfl,?_,old,T,V,tail⟩
      change (match nextPhase i (.complete s) i with
        | some a => readSegment i a []
        | none => _) = _
      rw [NX]

/-- Mark-by-mark certificate that a successful scanner saw exactly the
first, opposite and departure hits, with all holds classified. -/
inductive Labels {n : Nat} (i : Fin n) : Phase → List (Fin n) → Side → Prop
  | outside {p e es s} (l : e≠incident i .left) (r : e≠incident i .right)
      (tail : Labels i p es s) : Labels i p (e::es) s
  | firstHit {u es s} (tail : Labels i (.first u) es s) :
      Labels i .fresh (incident i u::es) s
  | repeatFirst {u es s} (tail : Labels i (.first u) es s) :
      Labels i (.first u) (incident i u::es) s
  | oppositeHit {u t es s} (ne : t≠u) (tail : Labels i (.complete u) es s) :
      Labels i (.first u) (incident i t::es) s
  | repeatIncoming {u es s} (tail : Labels i (.complete u) es s) :
      Labels i (.complete u) (incident i .right::es) s
  | departure (u : Side) : Labels i (.complete u) [incident i .left] u

theorem scanner_labels {n : Nat} (i : Fin n)
    (D : incident i .left≠incident i .right) (w : List (Fin n))
    (p : Phase) (s : Side) (R : readSegment i p w=some s) : Labels i p w s := by
  induction w generalizing p with
  | nil => cases R
  | cons e es ih =>
    by_cases l : e=incident i .left
    · subst e
      cases p with
      | fresh =>
        exact .firstHit (ih (.first .left) (by simpa only [readSegment,nextPhase,if_true] using R))
      | first u =>
        cases u
        · exact .repeatFirst (ih (.first .left) (by simpa only [readSegment,nextPhase,if_true] using R))
        · exact .oppositeHit (by decide) (ih (.complete .right) (by simpa only [readSegment,nextPhase,if_true] using R))
      | complete u =>
        cases es with
        | nil =>
          have eq : u=s := Option.some.inj (by simpa only [readSegment,nextPhase,if_true] using R)
          subst s
          exact .departure u
        | cons a as => simp [readSegment,nextPhase] at R
    · by_cases r : e=incident i .right
      · subst e
        cases p with
        | fresh =>
          exact .firstHit (ih (.first .right) (by simpa only [readSegment,nextPhase,if_neg D.symm,if_true] using R))
        | first u =>
          cases u
          · exact .oppositeHit (by decide) (ih (.complete .left) (by simpa only [readSegment,nextPhase,if_neg D.symm,if_true] using R))
          · exact .repeatFirst (ih (.first .right) (by simpa only [readSegment,nextPhase,if_neg D.symm,if_true] using R))
        | complete u =>
          exact .repeatIncoming (ih (.complete u) (by simpa only [readSegment,nextPhase,if_neg D.symm,if_true] using R))
      · exact .outside l r (ih p (by simpa only [readSegment,nextPhase,if_neg l,if_neg r] using R))

theorem labels_bit {n : Nat} {i : Fin n} {w : List (Fin n)} {s : Side}
    (H : Labels i .fresh w s) :
    ∃ pre post, w=pre++incident i s::post ∧
      ∀ e∈pre, e≠incident i .left ∧ e≠incident i .right := by
  have chosen {t q : Side} {z : List (Fin n)} (J : Labels i (.first t) z q) : q=t := by
    have A {p : Phase} {w : List (Fin n)} {s : Side} (J : Labels i p w s) :
        (∀ t,p=.first t → s=t) ∧ (∀ t,p=.complete t → s=t) := by
      induction J with
      | outside _ _ _ ih => exact ih
      | firstHit _ _ => constructor <;> intro t E <;> cases E
      | repeatFirst _ ih =>
        exact ⟨fun t E => ih.1 t E,fun _ E => by cases E⟩
      | oppositeHit _ _ ih =>
        constructor
        · intro t E
          cases E
          exact ih.2 _ rfl
        · intro _ E
          cases E
      | repeatIncoming _ ih =>
        constructor
        · intro _ E
          cases E
        · exact ih.2
      | departure u =>
        constructor
        · intro _ E
          cases E
        · exact fun _ E => Phase.complete.inj E
    exact (A J).1 _ rfl
  generalize E : Phase.fresh=p at H
  induction H with
  | outside l r _ ih =>
    obtain ⟨pre,post,W,S⟩ := ih E
    refine ⟨_::pre,post,congrArg (List.cons _) W,?_⟩
    intro e hm
    rcases List.mem_cons.mp hm with rfl|h
    · exact ⟨l,r⟩
    · exact S e h
  | firstHit J =>
    have T := chosen J
    rw [T]
    exact ⟨[],_,rfl,by simp⟩
  | repeatFirst _ _ | oppositeHit _ _ _ | repeatIncoming _ _ | departure _ => cases E

/-- Public positive interface to the same literal one-mark scanner. -/
theorem literal_phase_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i) (ready : correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (idx : S.getD k fall=(i,1)) (O : oldOrdinal B base hh i=4)
    (now : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out k)))
    (v : Payload) (F : v.fault=0) (op : v.opcode.toNat=bitOp)
    (zero : v.outcome=0) (arg : v.argument=0)
    (phase : Phase) (old : atSite (x i).long 1=.forward {v with race:=cycleCode phase})
    (off : gate bitOp (slot hp x i) (longGeometry B (x (rightNeighbor i)))=false)
    (e : Fin n) :
    match nextPhase i phase e with
    | some phase' => atSite (step x e i).long 1=.forward {v with race:=cycleCode phase'}
    | none => ∃ s, phase=.complete s ∧ e=i ∧ atSite (step x e i).long 1=.trail ∧
        atSite (step x e (rightNeighbor i)).long (slot hp x i)=.forward (cleanBit v s) :=
  phase_step hp C fixed ready sep i k idx O now v F op zero arg phase old off e

end L4.BStarBitSegment
