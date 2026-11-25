import Leader.L4.BStarGateIncoming

namespace L4.BStarGateStutter
open AllSizeProtocol BStarTrace BStarLongWork BStarLongCommand BStarLongToken
open BStarLongLayout BStarResetMarkAdapter BStarSeparatingRail BStarSeparatorControl
open BStarGeneratedOwner BStarResetSchedule BStarAcquireVisitOrder BStarH6WordChart
open BStarResetChartTouch BStarAcquireLiteralChain BStarAdmitIncidentGeometry
open BStarGateIncoming BStarGateUnmask BStarBitParity

theorem forward_stutter {len k : Nat} {u : BStarSeparatingRail.Rail} {d : Cursor}
    (a : Advance len (.out k) d) (g : Good anyTag len u d)
    {p : Payload} (f : u k=.forward p) : d=.out k := by
  cases a with
  | stay => rfl
  | forward =>
    have T := g.2.2 k (Nat.lt_succ_self k)
    rw [f] at T
    contradiction
  | turn =>
    obtain ⟨q,Q⟩ := g.2.1
    rw [f] at Q
    contradiction

theorem event_forward_stutter {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    {x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)}
    {addr : Nat → Pos n} {len op k : Nat} {e : Fin n} {d : Mode} {v : Payload}
    (ev : Event hp addr len x e (.busy op (.out k)) d)
    (f : project addr (AllSizeS1Geometry.step (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x e) k
        =.forward v) :
    d=.busy op (.out k) := by
  cases ev with
  | transit _ _ d _ seen =>
    cases seen with
    | cons _ _ advance good tail =>
      cases tail
      rw [forward_stutter advance good f]

private theorem width_gate (bit : Bool) (a : Nat) :
    forwardWidth (gateOpcode bit) a = some 1 := by
  cases bit <;> rfl

private theorem opcode_lt (bit : Bool) : gateOpcode bit < 413 := by
  cases bit <;> decide

/-- Cropping an already one-bit argument changes no live or padding byte. -/
theorem crop_idem (v : Payload) : cropped (cropped v 1) 1 = cropped v 1 := by
  have T : v.argument.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  have U : v.argument.toNat % 2 < 2^34 := by omega
  simp only [cropped,low, Nat.reducePow, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt U, Nat.mod_eq_of_lt T]

/-- An old healthy bound gated payload already has zero outcome and
canonical one-bit argument. In particular the next binding cannot erase
the race just because it has changed from 1 to FIRST or OTHER. -/
theorem old_canonical (g : LongGeometry) (bit : Bool) (t : Token) (v : Payload)
    (V : bind g 1 t=.forward v) (F : v.fault=0) (O : v.opcode.toNat=gateOpcode bit) :
    v.outcome=0 ∧ cropped v 1=v := by
  cases t with
  | empty => contradiction
  | trail => contradiction
  | reply q =>
    simp only [BStarLongCommand.bind] at V
    repeat first | contradiction | split at V
  | forward q =>
    simp only [BStarLongCommand.bind] at V
    have handle (guard : Bool) (bad : ¬(q.fault != 0 || decide (q.opcode.toNat≥413) ||
          q.outcome != 0 || !guard)=true)
        (H : (match forwardWidth q.opcode.toNat q.argument.toNat with
          | none => fault false
          | some w => .forward (cropped q w)) = .forward v) : v.outcome=0 ∧ cropped v 1=v := by
      split at H
      · have e := Token.forward.inj H
        rw [←e] at F
        contradiction
      · rename_i w E
        obtain rfl := Token.forward.inj H
        change q.opcode.toNat=gateOpcode bit at O
        rw [O,width_gate] at E
        cases E
        simp at bad
        have U : q.outcome=0 := bad.1.2
        exact ⟨U,crop_idem q⟩
    split at V <;> split at V
    · have e := Token.forward.inj V
      rw [←e] at F
      contradiction
    · exact handle _ (by assumption) V
    · have e := Token.forward.inj V
      rw [←e] at F
      contradiction
    · exact handle _ (by assumption) V

theorem rebind_gate_race (g : LongGeometry) (bit : Bool) (v : Payload) (z : BitVec 3)
    (F : v.fault=0) (O : v.opcode.toNat=gateOpcode bit) (U : v.outcome=0)
    (A : cropped v 1=v) (G : gate (gateOpcode bit) 1 g=true)
    (R : 1≤z.toNat ∧ z.toNat≤5) :
    bind g 1 (.forward {v with race:=z}) = .forward {v with race:=z} := by
  have C : cropped {v with race:=z} 1 = {v with race:=z} :=
    congrArg (fun p : Payload => {p with race:=z}) A
  simp [BStarLongCommand.bind,F,O,U,G,R,width_gate,show ¬ 413≤gateOpcode bit by have := opcode_lt bit; omega]
  rw [F,U] at C
  exact C

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- A physical encoded forward at the old gate supplies both the literal
stutter and exact rebinding of the changed race under the new settled gate. -/
theorem encoded_race_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop)
    (fiber : ∀ x, Q x → ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e))
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (i e : Fin n) (bit : Bool) (k : Nat) (q : Q x)
    (atGate : S.getD k fall=(i,1))
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy (gateOpcode bit) (.out k)))
    (v : Payload) (z : BitVec 3)
    (read : BStarLongCommand.bind (longGeometry B (x i)) 1 (atSite (x i).long 1)=.forward v)
    (op : v.opcode.toNat=gateOpcode bit) (fault : v.fault=0)
    (race : 1≤z.toNat ∧ z.toNat≤5)
    (newGate : gate (gateOpcode bit) 1 (longGeometry B (step x e i))=true)
    (raw : (kField 1).read (step x e i).long=encode (.forward {v with race:=z})) :
    Event hp (fun j => S.getD j fall) len x e
        (.busy (gateOpcode bit) (.out k)) (.busy (gateOpcode bit) (.out k)) ∧
    Current hp base (fun j => S.getD j fall) len (step x e) (.busy (gateOpcode bit) (.out k)) ∧
    BStarLongCommand.bind (longGeometry B (step x e i)) 1 (atSite (step x e i).long 1)
      =.forward {v with race:=z} := by
  have D : atSite (step x e i).long 1=.forward {v with race:=z} := by
    unfold atSite
    rw [raw,decode_encode]
  have P : project (fun j => S.getD j fall) (step x e) k=.forward {v with race:=z} := by
    change atSite (step x e (S.getD k fall).1).long (S.getD k fall).2=_
    rw [atGate]
    exact D
  obtain ⟨m,M,H⟩ := current_step hp C Q fiber closed distinct q e _ cur
  have E := event_forward_stutter hp M P
  subst m
  obtain ⟨U,A⟩ := old_canonical _ bit _ v read fault op
  refine ⟨M,H,?_⟩
  rw [D]
  exact rebind_gate_race _ bit v z fault op U A newGate race

/-- The literal FIRST or OTHER observer gives an actual stuttering
owner event, and the updated payload binds unchanged at the next mark. -/
theorem observed_race_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop)
    (fiber : ∀ x, Q x → ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e))
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (i e : Fin n) (bit : Bool) (k : Nat) (q : Q x)
    (atGate : S.getD k fall=(i,1))
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy (gateOpcode bit) (.out k)))
    (v : Payload)
    (read : BStarLongCommand.bind (longGeometry B (x i)) 1 (atSite (x i).long 1)=.forward v)
    (op : v.opcode.toNat=gateOpcode bit) (fault : v.fault=0)
    (ready : BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (nextReady : BStarClearanceOffset.correct (oldH6 B base) hh 5 (step x e))
    (oldGate : gate (gateOpcode bit) 1 (longGeometry B (x i))=true)
    (s : BStarLongClaims.Side) (hit : BStarAcquireDoorHistory.siteOf e s=i)
    (z : BitVec 3)
    (race : (v.race=1 ∧ z=firstCode s) ∨
      ∃ t, t≠s ∧ v.race=firstCode t ∧ z=finalCode t) :
    (kField 1).read (step x e i).long=encode (.forward {v with race:=z}) ∧
    Event hp (fun j => S.getD j fall) len x e
        (.busy (gateOpcode bit) (.out k)) (.busy (gateOpcode bit) (.out k)) ∧
    Current hp base (fun j => S.getD j fall) len (step x e) (.busy (gateOpcode bit) (.out k)) ∧
    BStarLongCommand.bind (longGeometry B (step x e i)) 1 (atSite (step x e i).long 1)
      =.forward {v with race:=z} := by
  have oldFixed : ∀ i,oldH6 B x i=oldH6 B base i :=
    fun i => (congrArg Prod.fst (fiber x q i)).symm
  have nextFixed : ∀ i,oldH6 B (step x e) i=oldH6 B base i :=
    fun i => (congrArg Prod.fst (fiber _ (closed x q e) i)).symm
  have nextGate := (selected_gate_iff hp hh nextFixed nextReady i 1 bit).mpr
    ((selected_gate_iff hp hh oldFixed ready i 1 bit).mp oldGate)
  have G : gate v.opcode.toNat 1 (longGeometry B (x i))=true := by rwa [op]
  have ⟨oldRace,obs,range⟩ :
      (v.race=1 ∨ ∃ old, v.race=firstCode old) ∧
        observe ⟨s,1⟩ (longGeometry B (x i)) v=some {v with race:=z} ∧
        1≤z.toNat ∧ z.toNat≤5 := by
    rcases race with ⟨H,rfl⟩ | ⟨t,diff,H,rfl⟩
    · exact ⟨.inl H,observe_first_any _ _ _ G fault H,by cases s <;> decide⟩
    · have obs := observe_other_any _ v t s G fault H
      rw [if_neg (Ne.symm diff)] at obs
      exact ⟨.inr ⟨t,H⟩,obs,by cases t <;> decide⟩
  have raw := physical_mark_of_current hp C i e (distinct e) bit k ready atGate oldGate cur
      v read op fault oldRace
  dsimp only at raw
  have exactRaw : (kField 1).read (step x e i).long=encode (.forward {v with race:=z}) := by
    rw [raw]
    cases s
    · change e=i at hit
      rw [if_pos hit.symm,obs]
      rfl
    · change rightNeighbor e=i at hit
      have N : i≠e := fun E => distinct e (E.symm.trans hit.symm)
      rw [if_neg N,if_pos hit.symm,obs]
      rfl
  exact ⟨exactRaw, encoded_race_step hp C Q fiber closed distinct i e bit k q atGate cur v z
    read op fault range nextGate exactRaw⟩

/-- After FIRST, every mark except the opposite incidence preserves
the actual K1 bytes (even noncanonical padding). -/
theorem first_wait_raw {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (i e : Fin n) (sep : e≠rightNeighbor e) (bit : Bool) (k : Nat)
    (ready : BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (atGate : S.getD k fall=(i,1))
    (G : gate (gateOpcode bit) 1 (longGeometry B (x i))=true)
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy (gateOpcode bit) (.out k)))
    (v : Payload)
    (read : BStarLongCommand.bind (longGeometry B (x i)) 1 (atSite (x i).long 1)=.forward v)
    (op : v.opcode.toNat=gateOpcode bit) (fault : v.fault=0)
    (s : BStarLongClaims.Side) (race : v.race=firstCode s)
    (avoid : ∀ t, BStarAcquireDoorHistory.siteOf e t=i → t=s) :
    (kField 1).read (step x e i).long=(kField 1).read (x i).long := by
  have raw := physical_mark_of_current hp C i e sep bit k ready atGate G cur
      v read op fault (.inr ⟨s,race⟩)
  have G' : gate v.opcode.toNat 1 (longGeometry B (x i))=true := by rwa [op]
  dsimp only at raw
  rw [raw]
  by_cases L : i=e
  · have E := avoid .left L.symm
    subst s
    rw [if_pos L,observe_other_any _ v .left .left G' fault race,if_pos rfl]
    rfl
  · rw [if_neg L]
    by_cases R : i=rightNeighbor e
    · have E := avoid .right R.symm
      subst s
      rw [if_pos R,observe_other_any _ v .right .right G' fault race,if_pos rfl]
      rfl
    · rw [if_neg R]

/-- A suffix after an observed FIRST stays at exactly that owner cursor
with unchanged raw/bound payload until the nominated opposite incidence. -/
theorem first_wait_word {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop)
    (fiber : ∀ x, Q x → ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e))
    (ready : ∀ x, Q x → BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (bit : Bool) (k : Nat)
    (atGate : S.getD k fall=(i,1))
    (ordinal : BStarH6Ordinal.oldOrdinal B base hh i=gateOrdinal bit)
    (v : Payload) (op : v.opcode.toNat=gateOpcode bit) (fault : v.fault=0)
    (s : BStarLongClaims.Side) (race : v.race=firstCode s)
    (w : List (Fin n)) (x : X) (q : Q x)
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy (gateOpcode bit) (.out k)))
    (read : BStarLongCommand.bind (longGeometry B (x i)) 1 (atSite (x i).long 1)=.forward v)
    (encoded : (kField 1).read (x i).long=encode (.forward v))
    (avoid : ∀ e∈w, ∀ t, BStarAcquireDoorHistory.siteOf e t=i → t=s) :
    let y := BStarResetSchedule.run step x w
    Current hp base (fun j => S.getD j fall) len y (.busy (gateOpcode bit) (.out k)) ∧
      BStarLongCommand.bind (longGeometry B (y i)) 1 (atSite (y i).long 1)=.forward v ∧
      (kField 1).read (y i).long=encode (.forward v) := by
  have gateAt (y : X) (qy : Q y) : gate (gateOpcode bit) 1 (longGeometry B (y i))=true :=
    (selected_gate_iff hp hh (fun j => (congrArg Prod.fst (fiber y qy j)).symm)
      (ready y qy) i 1 bit).mpr ⟨rfl,ordinal⟩
  induction w generalizing x with
  | nil => exact ⟨cur,read,encoded⟩
  | cons e w ih =>
    have raw := (first_wait_raw hp C i e (distinct e) bit k (ready x q) atGate
      (gateAt x q) cur v read op fault s race (avoid e (List.mem_cons_self))).trans encoded
    have range : 1≤v.race.toNat ∧ v.race.toNat≤5 := by rw [race]; cases s <;> decide
    have id : {v with race:=v.race} = v := by cases v; rfl
    have one := encoded_race_step hp C Q fiber closed distinct i e bit k q atGate cur v v.race
      read op fault range (gateAt _ (closed x q e)) (by rwa [id])
    rw [id] at one
    exact ih _ (closed x q e) one.2.1 one.2.2 raw
      (fun a ha => avoid a (List.mem_cons_of_mem _ ha))

end L4.BStarGateStutter
