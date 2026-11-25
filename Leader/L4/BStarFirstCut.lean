import Leader.L4.BStarOwnerRecoveryPass
import Leader.L4.BStarResetEndpointZero

namespace L4.BStarFirstCut
open AllSizeProtocol BStarTrace BStarLongWork BStarLongTransport BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarResetMarkAdapter BStarResetSchedule BStarSeparatingRail
open BStarOwnerRecoveryPass BStarGrantBirth BStarResetNoAcquire

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- The certified RREL belongs to the later reset chain and follows a
real RCLEAR. Each owned grant is therefore zero at completion of the
credited segment, not merely touched at some intermediate mark. -/
theorem recovered_zero {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {w : List (Fin n)}
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (R : Recovered hp base hh o x w)
    (i : Fin n) (j : Fin 3)
    (own : commandOwner (oldH6 B base) i (slot j)=o.val) :
    bit (run x w) i j=0 := by
  obtain ⟨S,len,fall,C,u,v,residual,w₀,w₁,w₂,y₁,y₂,_,_,_,_,A,D,F⟩ := R
  let door := RearTrace.predecessor (S.getD 0 fall).1
  have preserved (t : List (Fin n)) (z : X) (K : Q z) : Q (run z t) := by
    induction t generalizing z with
    | nil => exact K
    | cons e t ih => exact ih _ (closed z e K)
  let zero := run (step (run (step (run x u) door) v) door) residual
  have Q0 : Q zero := preserved _ _ (closed _ _ (preserved _ _ (closed _ _ (preserved _ _ I))))
  have Q1 : Q y₁ := A.choose_spec.2.1.symm ▸ preserved w₀ zero Q0
  have Q2 : Q y₂ := D.choose_spec.2.1.symm ▸ preserved w₁ y₁ Q1
  have E := BStarResetIssueClean.stage_endpoint_clean hp C sep Q Q1 fiber closed 1 (by decide) w₁ D
  exact BStarResetEndpointZero.stage_grant_zero hp C sep Q Q2 fiber closed E w₂ F i j own

/-- Bit provenance at the first cut: a live owned incidence has a
winning old ACQUIRE at that incidence after its own recovered segment,
on this very prefix, with uninterrupted grant until the cut. -/
theorem cut_grant {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {u v : List (Fin n)} {a b : Nat}
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (credit : BStarRecoveryPass.Credit step (Recovered hp base hh) o x (u++v) a b)
    (before : b≤u.length)
    (i : Fin n) (j : Fin 3) (own : commandOwner (oldH6 B base) i (slot j)=o.val)
    (live : bit (run x u) i j≠0) :
    ∃ lead e tail, u=lead++e::tail ∧ b≤lead.length ∧
      let z := run x lead
      bit z i j=0 ∧ WonAt hp z e i j ∧ Continuous hp (step z e) i j tail := by
  exact credit_grant hp sep (BStarRecoveryPass.credit_prefix step credit before) i j Q closed I
    (fun _ _ Iz recovered => recovered_zero hp sep Q Iz fiber closed recovered i j own) live

open BStarClearanceOffset

/-- A physical record of the most recent zero-to-one change of an
incidence on the common word, no sooner than the given cut index. -/
def BirthAfter (x : X) (w : List (Fin n)) (i : Fin n) (j : Fin 3) (t : Nat) : Prop :=
  ∃ lead e tail, w=lead++e::tail ∧ t≤lead.length ∧
    let z := run x lead
    bit z i j=0 ∧ WonAt hp z e i j ∧ Continuous hp (step z e) i j tail

/-- On a single common word, both recovery passes establish the stated
physical grant-bit provenance. Every grant live at the second cut or
any later prefix was won strictly after the first cut. This conclusion
does not yet identify the held file or a captured bank with that win. -/
theorem two_pass_births {base x : X} (hh : ∃ i,oldH6 B base i=true)
    (charts : ∀ o : Owners (oldH6 B base), ∃ S len fall, Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (Q : X → Prop) (closed : ∀ y e, Q y → Q (step y e))
    (fiber : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (heads : ∀ y, Q y → ∀ i, let g := longGeometry B (y i); (!g.axes.h6 || g.inside)=true)
    (conts : ∀ y, Q y → ∀ i, let g := oldPair B y i; continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base)
    (owners : List (Owners (oldH6 B base)))
    (cover : ∀ i : Fin n, ∀ j : Fin 3,
      ∃ o∈owners, commandOwner (oldH6 B base) i (slot j)=o.val)
    (I : Q x) (cx : correct (oldH6 B base) hh 5 x) :
    ∃ u v, Q (run x u) ∧ Q (run x (u++v)) ∧
      (∀ i j, bit (run x u) i j≠0 →
        ∃ o∈owners, ∃ a b, b≤u.length ∧
          BStarRecoveryPass.Credit step (Recovered hp base hh) o x u a b ∧
          commandOwner (oldH6 B base) i (slot j)=o.val ∧ BirthAfter hp x u i j b) ∧
      (∀ tail i j, bit (run x ((u++v)++tail)) i j≠0 →
        BirthAfter hp x ((u++v)++tail) i j (u.length+1)) := by
  obtain ⟨u,v,U,V,A,F⟩ := two_recoveries hp hh charts sep head cont Q closed fiber heads conts cb owners I cx
  refine ⟨u,v,U.1,V.1,?_,?_⟩
  · intro i j live
    obtain ⟨o,M,own⟩ := cover i j
    obtain ⟨a,b,_,N,C⟩ := A o M
    exact ⟨o,M,a,b,N,BStarRecoveryPass.credit_prefix step C N,own,
      cut_grant hp sep Q I fiber closed C N i j own live⟩
  · intro tail i j live
    obtain ⟨o,M,own⟩ := cover i j
    obtain ⟨a,b,N,L,C⟩ := F o M
    obtain ⟨lead,e,t,T,H,W⟩ := credit_grant hp sep (BStarRecoveryPass.credit_append step C tail)
      i j Q closed I (fun _ _ Iz Rh => recovered_zero hp sep Q Iz fiber closed Rh i j own) live
    exact ⟨lead,e,t,T,by omega,W⟩

end L4.BStarFirstCut
