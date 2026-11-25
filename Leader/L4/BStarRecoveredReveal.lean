import Leader.L4.BStarPhysicalPairLaw
import Leader.L4.BStarRecoveredHistory

namespace L4.BStarRecoveredReveal
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarPhysicalPairLaw BStarPhysicalIncrementLedger BStarIncrementLedger
open BStarH6Ordinal BStarAcquireLiteralChain BStarAcquireAnchors BStarAcquireVisitOrder
open BStarOwnerRecoveryPass BStarBitLabelSwap BStarClearanceRaceMark BStarBitParity
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Admission is certified entirely by the old physical history. A
reset that finishes on the currently chosen label cannot admit that label. -/
def Admitted (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (past : List (Fin n)) (gate : Fin n) : Prop :=
  ∃ lead middle rest, past=lead++middle++rest ∧
    Recovered hp base hh (own (oldH6 B base) hh (gate,1)) (run x lead) middle

theorem admitted_append {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {past : List (Fin n)} (w : List (Fin n)) {gate : Fin n}
    (H : Admitted hp base x hh past gate) : Admitted hp base x hh (past++w) gate := by
  obtain ⟨a,b,c,E,R⟩ := H
  exact ⟨a,b,c++w,by rw [E,List.append_assoc],R⟩

def Ready (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (past : List (Fin n)) (gate : Fin n) : Prop :=
  Fresh hp base hh (run x past) gate ∧ Admitted hp base x hh past gate

noncomputable def mate (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (past : List (Fin n)) (e : Fin n) : Fin n :=
  swap (Ready hp base x hh past) e

noncomputable def reveal (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (past : List (Fin n)) (e : Fin n) : Option (Key n × Bool) := by
  classical
  exact if H : ∃ z, Witness (Ready hp base x hh past) e z then
    let z := Classical.choose H
    let i := ownerAt hp base hh z.1
    some ((i,count start (tapeInc hp base hh x past) i past.length),firstBit z.2)
  else none

theorem mate_twice (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (past : List (Fin n)) (e : Fin n) :
    mate hp base x hh past (mate hp base x hh past e)=e :=
  swap_twice hh _ (fun _ H=>H.1.1) e

theorem reveal_incident (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (past : List (Fin n)) (i : Fin n) (s : Side)
    (H : Ready hp base x hh past i) :
    reveal hp base x hh start past (incident i s)=
      some ((ownerAt hp base hh i,
        count start (tapeInc hp base hh x past) (ownerAt hp base hh i) past.length),firstBit s) := by
  classical
  have J : Witness (Ready hp base x hh past) (incident i s) (i,s) := ⟨H,rfl⟩
  have E := Exists.intro (i,s) J
  unfold reveal
  rw [dif_pos E]
  rw [witness_unique hh _ (fun _ A=>A.1.1) (Classical.choose_spec E) J]

/-- The recovery gate is tested on the same old tape for both alternatives. -/
theorem reveal_mate (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (past : List (Fin n)) (e : Fin n) (k : Key n) (bit : Bool)
    (H : reveal hp base x hh start past e=some (k,bit)) :
    reveal hp base x hh start past (mate hp base x hh past e)=some (k,!bit) := by
  classical
  by_cases E : ∃ z,Witness (Ready hp base x hh past) e z
  · obtain ⟨⟨i,s⟩,R,Z⟩ := E
    change incident i s=e at Z
    subst e
    have M : mate hp base x hh past (incident i s)=incident i (other s) :=
      swap_incident hh _ (fun _ A=>A.1.1) R s
    rw [reveal_incident hp base x hh start past i s R] at H
    have eq := Option.some.inj H
    have one : _=k := congrArg Prod.fst eq
    have two : firstBit s=bit := congrArg Prod.snd eq
    rw [←one,←two,M,reveal_incident hp base x hh start past i (other s) R]
    cases s <;> rfl
  · rw [show reveal hp base x hh start past e=none from dif_neg E] at H
    cases H

/-- After all raw-fresh gates are admitted, the observer agrees exactly
with the ordinary literal observer. Before that cut it suppresses,
rather than reserves, any inherited ready flag. -/
theorem agrees_if_admitted (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (past : List (Fin n)) (e : Fin n)
    (H : ∀ i,Fresh hp base hh (run x past) i → Admitted hp base x hh past i) :
    reveal hp base x hh start past e=
      BStarPhysicalPairLaw.reveal hp base hh x (ownerAt hp base hh) start past e := by
  classical
  by_cases E : ∃ z,Witness (Fresh hp base hh (run x past)) e z
  · obtain ⟨⟨i,s⟩,J,Z⟩ := E
    change incident i s=e at Z
    subst e
    rw [reveal_incident hp base x hh start past i s ⟨J,H i J⟩,
      BStarPhysicalPairLaw.reveal_incident hp base hh x (ownerAt hp base hh) start past i s J]
  · have F : ¬∃ z,Witness (Ready hp base x hh past) e z := by
      rintro ⟨z,J,K⟩
      exact E ⟨z,J.1,K⟩
    unfold reveal BStarPhysicalPairLaw.reveal
    rw [dif_neg F]
    simp only [dif_neg E]

open BStarCustodyCuts BStarResetChartTouch BStarRecoveredHistory BStarOwnerLaunchOrigin
open BStarLongFixedRouting BStarGeneratedOwner BStarAcquireForwardTrace BStarResetMarkAdapter

/-- The common custody certificate admits every owner by the stop,
including a raw-fresh gate that has not yet completed its BIT flight. -/
theorem common_admission {base x : X} (hh : ∃ i,oldH6 B base i=true)
    (u v : List (Fin n)) (C : CutFacts hp base x u v) (gate : Fin n) :
    Admitted hp base x hh (u++v) gate := by
  obtain ⟨o,_,_,ownEq,_,_,credit⟩ := C.recovery hh gate 1
  change commandOwner (oldH6 B base) gate 1=o.val at ownEq
  have eq : own (oldH6 B base) hh (gate,1)=o := Subtype.ext ownEq
  obtain ⟨a,b,c,E,_,_,R⟩ := credit
  exact ⟨a,b,c,E,eq.symm ▸ R⟩

private theorem run_ready (Q : X→Prop) (closed : ∀ x e,Q x→Q (step x e))
    {x : X} (I : Q x) (w : List (Fin n)) : Q (run x w) := by
  induction w generalizing x with
  | nil => exact I
  | cons e w ih => exact ih (closed x e I)

/-- Any admitted raw-first flag has a genuine same-owner BIT launch
after the chosen recovery completion. The flag itself is not treated as
an origin certificate, and no later ACK or COMMIT is assumed. -/
theorem admitted_origin {base x : X} {hh : ∃ i,oldH6 B base i=true}
    (Q : X→Prop) (I : Q x) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x e,Q x→Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (past : List (Fin n)) (gate : Fin n) (H : Ready hp base x hh past gate) :
    ∃ (lead mid rest : List (Fin n)) (S : List (Pos n)) (len : Nat) (fall : Pos n) (k : Nat),
      past=lead++mid++rest ∧
      Chart hp base hh (own (oldH6 B base) hh (gate,1)) S len fall ∧
      k≤len ∧ S.getD k fall=(gate,1) ∧
      Found hp base (fun j=>S.getD j fall) len BStarLongCommand.bitOp
        (run (run x lead) mid) rest (.out k) := by
  obtain ⟨F,a,b,c,E,R⟩ := H
  obtain ⟨S,len,fall,C,_,_,m,G,_,J⟩ :=
    recovered_suffix hp R sep Q (run_ready hp Q closed I a) fiber closed c
  have mem : (gate, (1 : Fin 11))∈S := C.cover _ rfl rfl
  obtain ⟨k,K,L⟩ := List.mem_iff_getElem.mp mem
  have lenS := C.length
  have loc : S.getD k fall=(gate,1) := (List.getElem_eq_getD fall).symm.trans L
  have eq : run x past=run (run x a) (b++c) := by
    rw [E,List.append_assoc,BStarResetSchedule.run_append]
  obtain ⟨_,p,raw,hf,op,_,_,_⟩ := F
  have current : Current hp base (fun j=>S.getD j fall) len
      (run (run (run x a) b) c) m := by
    rw [←BStarResetSchedule.run_append]
    exact J
  have projected : project (fun j=>S.getD j fall) (run (run (run x a) b) c) k=.forward p := by
    change atCursor (run (run (run x a) b) c) (S.getD k fall)=_
    rw [loc,←BStarResetSchedule.run_append,←eq]
    exact raw
  have h := healthy_forward_origin hp C sep G current k (by omega) p projected
    BStarLongCommand.bitOp hf op
  exact ⟨a,b,c,S,len,fall,k,E,C,by omega,loc,h.2⟩

open L4.Height.Couple

/-- The admitted old-state observer is a paired source on the doubled
raw alphabet. It keeps the actual raw trace as the state. -/
noncomputable def source (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) : PairedSource (List (Fin n)) (Key n) (n+n) where
  next past e := past++[rawLabel e]
  bitOf past e := reveal hp base x hh start past (rawLabel e)
  flip past := doubleMate (mate hp base x hh past)
  half := n
  alphabet_even := by omega
  flip_invol past := doubleMate_twice _ (mate_twice hp base x hh past)
  flip_reveal past e k b H := by
    rw [raw_doubleMate]
    exact reveal_mate hp base x hh start past (rawLabel e) k b H

end L4.BStarRecoveredReveal
