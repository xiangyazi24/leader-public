import Leader.L4.BStarBitSegment

namespace L4.BStarBitOneObservation
open AllSizeProtocol BStarLongClaims BStarLongWork BStarResetChartTouch BStarAcquireForwardTrace BStarAcquireVisitOrder BStarAcquireLiteralChain BStarBitGateGeometry BStarTrace BStarLongToken BStarLongCommand
open BStarH6WordChart BStarH6Ordinal BStarResetChartIndex
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarClearanceOffset BStarClearanceRaceMark BStarBitParity BStarBitSegment

def Past (k : Nat) : Cursor → Prop
  | .out j => k < j
  | .back _ => True

theorem past_advance {k len : Nat} {a b : Cursor}
    (A : Advance len a b) (P : Past k a) : Past k b := by
  cases A with
  | forward j => simp only [Past] at P ⊢; omega
  | stay => exact P
  | turn | reverse => trivial

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

theorem event_advance {addr : Nat → Pos n} {len op : Nat} {x : X} {e : Fin n}
    {a b : Cursor} (E : @Event k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp addr len x e (.busy op a) (.busy op b)) :
    Advance len a b := by
  cases E with
  | arrived_hold => exact .stay _
  | transit _ _ _ _ S =>
    cases S with
    | cons _ _ A _ R => cases R; exact A

/-- A gate observation is identified by the genuine owner cursor, the old
raw healthy fresh packet, and an incident physical mark. -/
def Observes (i : Fin n) (k : Nat) (x : X) (z : Cursor) (e : Fin n) : Prop :=
  z=.out k ∧ (e=incident i .left ∨ e=incident i .right) ∧
    ∃ v, atSite (x i).long 1=.forward v ∧ v.fault=0 ∧
      v.opcode.toNat=bitOp ∧ v.outcome=0 ∧ v.argument=0 ∧ v.race=1

private theorem nonfresh_code (q : Phase) (Q : q≠.fresh) : cycleCode q≠1 := by
  cases q with
  | fresh => contradiction
  | first s | complete s => cases s <;> decide

private theorem no_fresh_next {i : Fin n} {e : Fin n} {a b : Phase}
    (H : nextPhase i a e=some b) (A : a≠.fresh ∨ e=incident i .left ∨ e=incident i .right) :
    b≠.fresh := by
  intro E; subst b
  unfold nextPhase at H
  split at H
  · cases a with
    | fresh => simp at H
    | first s | complete s => cases s <;> simp at H
  · split at H
    · cases a with
      | fresh => simp at H
      | first s | complete s => cases s <;> simp at H
    · cases Option.some.inj H
      rename_i L R
      exact A.elim (fun h => h rfl) (fun h => h.elim L R)


private theorem track_step {base : X} {hh : ∃ i,@oldH6 _ n B base i=true}

    {o : BStarAcquireLiteralChain.Owners (@oldH6 _ n B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : @Chart k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1))
    (O : @oldOrdinal _ n B base hh i=4)
    (v : Payload) (F : v.fault=0) (op : v.opcode.toNat=bitOp)
    (outcome : v.outcome=0) (arg : v.argument=0)
    {x : X} {e : Fin n} {b : Cursor}
    (I : @Current k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp base (fun t=>S.getD t fall) len x (.busy bitOp (.out k)))
    (E : @Event k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp (fun t=>S.getD t fall) len x e (.busy bitOp (.out k)) (.busy bitOp b))
    (I' : @Current k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp base (fun t=>S.getD t fall) len (step x e) (.busy bitOp b))
    (fixed : ∀ j,@oldH6 _ n B x j=@oldH6 _ n B base j)
    (ready : @correct k₁ k₂ t₂ J₁ J₂ r c p c₁ n (@oldH6 _ n B base) hh 5 x)
    (q : Phase) (old : atSite (x i).long 1=.forward {v with race:=cycleCode q})
    (A : q≠.fresh ∨ e=incident i .left ∨ e=incident i .right) :
    Past k b ∨ (b=.out k ∧ ∃ z, z≠.fresh ∧
      atSite (step x e i).long 1=.forward {v with race:=cycleCode z}) := by
  have H := @BStarBitSegment.literal_phase_step k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp _ _ _ _ _ _ _ C fixed ready sep i k idx O I v F op
    outcome arg q old (@next_not_gate k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp _ _ _ fixed ready i O) e
  have adv := event_advance hp E
  cases P : nextPhase i q e with
  | some z =>
    rw [P] at H
    cases adv with
    | stay => exact .inr ⟨rfl,z,no_fresh_next P A,H⟩
    | forward => exact .inl (by simp [Past])
    | turn => exact .inl trivial
  | none =>
    rw [P] at H
    obtain ⟨_,_,_,T,_⟩ := H
    cases adv with
    | stay =>
      obtain ⟨pay, L⟩ := I'.2.1.2.1
      change atCursor (step x e) (S.getD k fall)=.forward pay at L
      rw [idx] at L
      change atSite (step x e i).long 1=.forward pay at L
      rw [T] at L
      cases L
    | forward => exact .inl (by simp [Past])
    | turn => exact .inl trivial

private theorem track_word {base : X} {hh : ∃ i,@oldH6 _ n B base i=true}

    {o : BStarAcquireLiteralChain.Owners (@oldH6 _ n B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : @Chart k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1))
    (O : @oldOrdinal _ n B base hh i=4)
    (v : Payload) (F : v.fault=0) (op : v.opcode.toNat=bitOp)
    (outcome : v.outcome=0) (arg : v.argument=0)
    {x : X} {a b : Cursor} {w : List (Fin n)}
    (H : @BusyOnly k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp base (fun t=>S.getD t fall) len bitOp x a w b)
    (scope : ∀ pre e post, w=pre++e::post →
      let y := play x pre
      (∀ j,@oldH6 _ n B y j=@oldH6 _ n B base j) ∧ @correct k₁ k₂ t₂ J₁ J₂ r c p c₁ n (@oldH6 _ n B base) hh 5 y) :
    (Past k a ∨ (a=.out k ∧ ∃ q, q≠.fresh ∧
      atSite (x i).long 1=.forward {v with race:=cycleCode q})) →
    Past k b ∨ (b=.out k ∧ ∃ q, q≠.fresh ∧
      atSite (play x w i).long 1=.forward {v with race:=cycleCode q}) := by
  induction H with
  | nil => exact id
  | @cons x a next dest e w I E tail ih =>
    intro init
    apply ih (fun pre f post eq => scope (e::pre) f post (congrArg (List.cons e) eq))
    rcases init with P|⟨eq,q,Hq,V⟩
    · exact .inl (past_advance (event_advance hp E) P)
    · subst a
      obtain ⟨fixed,ready⟩ := scope [] e w rfl
      exact track_step hp C sep i k K idx O v F op outcome arg I E
        (@busy_start k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp _ _ _ _ _ _ _ _ tail) fixed ready q V (.inl Hq)

/-- An observed first side on the first mark cannot be observed again at
the endpoint of the same uninterrupted busy prefix, for any next mark.
Apply this to the slice between any two proposed first observations. -/
theorem no_second_observation {base : X} {hh : ∃ i,@oldH6 _ n B base i=true}

    {o : BStarAcquireLiteralChain.Owners (@oldH6 _ n B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : @Chart k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1))
    (O : @oldOrdinal _ n B base hh i=4)
    {x : X} {a b : Cursor} {e f : Fin n} {w : List (Fin n)}
    (H : @BusyOnly k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp base (fun t=>S.getD t fall) len bitOp x a (e::w) b)
    (scope : ∀ pre g post, e::w=pre++g::post →
      let y := play x pre
      (∀ j,@oldH6 _ n B y j=@oldH6 _ n B base j) ∧ @correct k₁ k₂ t₂ J₁ J₂ r c p c₁ n (@oldH6 _ n B base) hh 5 y)
    (first : Observes i k x a e) :
    ¬ Observes i k (play x (e::w)) b f := by
  obtain ⟨eq,incidentMark,v,V,F,op,O₀,A₀,R⟩ := first
  subst a
  cases H with
  | @cons _ _ next _ _ _ I E tail =>
    obtain ⟨fixed,ready⟩ := scope [] e w rfl
    have old : atSite (x i).long 1=.forward {v with race:=cycleCode .fresh} := by
      rw [V]
      cases v
      rename_i opcode fault race outcome argument
      change race = 1 at R
      cases R
      rfl
    have init := track_step hp C sep i k K idx O v F op O₀ A₀ I E
      (@busy_start k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp _ _ _ _ _ _ _ _ tail) fixed ready .fresh old (.inr incidentMark)
    have endState := track_word hp C sep i k K idx O v F op O₀ A₀ tail
      (fun pre g post eq => scope (e::pre) g post (congrArg (List.cons e) eq)) init
    rintro ⟨rfl,_,v',V',_,_,_,_,R'⟩
    rcases endState with P|⟨_,q,Q,U⟩
    · exact (Nat.lt_irrefl _ P)
    · have eq := Token.forward.inj (U.symm.trans V')
      have qr : cycleCode q=1 := (congrArg Payload.race eq).trans R'
      exact nonfresh_code q Q qr

#print axioms no_second_observation
end L4.BStarBitOneObservation
