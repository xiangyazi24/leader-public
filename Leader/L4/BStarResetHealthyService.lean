import Leader.L4.BStarResetChartService
import Leader.L4.BStarResetNoFault

namespace L4.BStarResetHealthyService
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace
open BStarResetRailRing BStarSeparatingRail BStarSeparatingProgress

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

open BStarResetMarkAdapter BStarResetTaggedRows BStarResetNoFault
open BStarResetChartService BStarResetChartTouch BStarResetQuietAdapter
open BStarResetSchedule BStarLongDoor BStarLongCommand

def healthyTag (op : Nat) : Tag where
  F t := t=.forward (resetPayload op)
  D t := t=finish (resetPayload op)

theorem weakF (op : Nat) (t : Token) (h : (healthyTag op).F t) : (resetTag op).F t :=
  ⟨resetPayload op,.inl rfl,h⟩

theorem weakD (op : Nat) (t : Token) (h : (healthyTag op).D t) : (resetTag op).D t :=
  ⟨resetPayload op,.inl rfl,h⟩

theorem weak_good (op len : Nat) (u : BStarSeparatingRail.Rail) (z : Cursor)
    (h : Good (healthyTag op) len u z) : Good (resetTag op) len u z := by
  cases z with
  | out k => exact ⟨h.1,weakF _ _ h.2.1,h.2.2⟩
  | back k => exact ⟨h.1,weakD _ _ h.2.1,h.2.2⟩

theorem healthy_sane (op : Nat) (ho : op<3) : Sane (healthyTag op) := by
  obtain ⟨A,D,T⟩ := sane op ho
  exact ⟨fun h => A (weakF _ _ h),fun h => D (weakD _ _ h),
    fun t d f => T t (weakD _ _ d) (weakF _ _ f)⟩

noncomputable def actualHealthyService (x : X) (e : Fin n) (he : e≠rightNeighbor e)
    (adr : Nat → Pos n) (len op : Nat) (ho : op<3)
    (quiet : Quiet (healthyTag op) len (project adr x) (project adr (AllSizeS1Geometry.step B x e))
      (linkAt hp x e adr len) (onTerminal hp x e adr len)) :
    Service (healthyTag op) len (project adr x) (project adr (AllSizeS1Geometry.step B x e)) := by
  have fx (j : Nat) (L : linkAt hp x e adr len j) (F : (healthyTag op).F (project adr x j)) :
      project adr (AllSizeS1Geometry.step B x e) j=.trail ∧
      (healthyTag op).F (project adr (AllSizeS1Geometry.step B x e) (j+1)) := by
    obtain ⟨_,C,d,hc,hd,S,D⟩ := L
    unfold project at F ⊢
    rw [S] at F ⊢
    rw [D]
    have src := (old_read x e C.source).trans F
    have small : op=0 ∨ op=1 ∨ op=2 := by omega
    obtain ⟨A,D⟩ := joined_link_no_fault k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) C d op small hc hd src
    exact ⟨(new_read B x e he C.source).symm.trans A,(new_read B x e he d).symm.trans D⟩
  refine
    { mark :=
        { link := linkAt hp x e adr len
          terminal := onTerminal hp x e adr len
          bound := fun _ H => H.1
          disjoint := link_disjoint hp x e he adr len
          terminal_disjoint := terminal_disjoint hp x e he adr len
          idle := quiet.idle
          tt := quiet.tt
          ee := quiet.ee
          tf := quiet.tf
          fx := fun j L F => .inr (fx j L F)
          td := ?_
          de := quiet.de
          termF := ?_
          termD := quiet.termD
          termE := quiet.termE }
      labels := labels hp x e adr len
      links := fun j => (mem_link hp x e adr len j).mp
      terminal := (mem_terminal hp x e adr len).mp
      forced := fx }
  · intro j L T D
    obtain ⟨_,C,d,hc,hd,S,Z⟩ := L
    unfold project at T D ⊢
    rw [S] at T ⊢
    rw [Z] at D ⊢
    have small : op=0 ∨ op=1 ∨ op=2 := by omega
    obtain ⟨A,K⟩ := reset_reverse_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) C d (resetPayload op) hc hd
      ((old_read x e C.source).trans T) ((old_read x e d).trans D) (healthy op small)
    exact ⟨(new_read B x e he C.source).symm.trans A,(new_read B x e he d).symm.trans K⟩
  · rintro ⟨C,hC,hk,hd,k,S⟩ F
    unfold project at F ⊢
    rw [S] at F ⊢
    have small : op=0 ∨ op=1 ∨ op=2 := by omega
    have A := joined_terminal_no_fault k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) C op small hC hk hd k ((old_read x e C.source).trans F)
    have B' : finish (resetPayload op)=.reply (resetPayload op) := by
      rcases small with rfl|rfl|rfl <;> rfl
    exact (new_read B x e he C.source).symm.trans (A.trans B'.symm)

open BStarH6WordChart BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarAcquireVisitOrder BStarAcquireAnchors BStarLongFixedRouting

noncomputable def healthyService {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i) (e : Fin n) (he : e≠rightNeighbor e)
    (op : Nat) (ho : op<3) (z : Cursor) (live : z≠.back 0)
    (G : Good (healthyTag op) len (project (fun j => S.getD j fallback) x) z)
    (waitV : LongDoorGuard.valid manifest (x (S.getD 0 fallback).1).long=true)
    (waitP : (ctrlPhase.read (x (S.getD 0 fallback).1).long).toNat=2) :
    Service (healthyTag op) len
      (project (fun j => S.getD j fallback) x)
      (project (fun j => S.getD j fallback) (AllSizeS1Geometry.step B x e)) :=
  actualHealthyService hp x e he _ len op ho
    (quiet_of_frames_for hp x e he _ len op ho
      (frames hp C same e op ho z live (weak_good _ _ _ _ G) waitV waitP)
      (healthyTag op) (weakF op) (weakD op))

theorem healthy_adapter_on {base : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (Q : X → Prop)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (AllSizeS1Geometry.step B x e))
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (op : Nat) (ho : op<3) (edgeOf : Label → Fin n)
    (linkN : ∀ x : X, (∀ i, Layout B base i=Layout B x i) → ∀ j<len,
      onLink hp x (edgeOf (.link j)) (fun j => S.getD j fallback) j)
    (termN : ∀ x : X, (∀ i, Layout B base i=Layout B x i) →
      onTerminal hp x (edgeOf .terminal) (fun j => S.getD j fallback) len) :
    Adapter (AllSizeS1Geometry.step B) (project (fun j => S.getD j fallback))
      (healthyTag op) len (fun x => Q x ∧ Waiting hp base (S.getD 0 fallback).1 op x) edgeOf := by
  refine ⟨healthy_sane op ho,?_,?_⟩
  · intro x e z ⟨Qx,W⟩ L G
    have yQ := closed x Qx e
    exact ⟨yQ,waiting_closed_at hp C e op ho (fiber _ yQ) z L (weak_good _ _ _ _ G) W⟩
  intro x e z ⟨_,W⟩ L G
  refine ⟨healthyService hp C W.1 e (distinct _) op ho z L G W.2.1 W.2.2.1,?_⟩
  intro H
  subst e
  change nomination len z ∈ labels hp x (edgeOf (nomination len z)) _ len
  cases z with
  | out j =>
    by_cases T : j=len
    · have P := (mem_terminal hp x (edgeOf .terminal) _ len).mpr (termN x W.1)
      simpa [nomination,T] using P
    · have J : j≤len := G.1
      have J' : j<len := by omega
      have P := (mem_link hp x (edgeOf (.link j)) _ len j).mpr ⟨J',linkN x W.1 j J'⟩
      simpa [nomination,T] using P
  | back j =>
    cases j with
    | zero => exact (L rfl).elim
    | succ j =>
      have J : j+1≤len := G.1
      have J' : j<len := by omega
      exact (mem_link hp x (edgeOf (.link j)) _ len j).mpr ⟨J',linkN x W.1 j J'⟩

end L4.BStarResetHealthyService
