import Leader.L4.BStarResetRailRing
import Leader.L4.BStarSeparatingProgress
import Leader.L4.BStarAcquireLiteralChain

/-! Literal service labels and actual obligatory transit. The quiet
cases are factored out to permit different packed framing arguments. -/
namespace L4.BStarResetMarkAdapter
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace
open BStarResetRailRing BStarSeparatingRail BStarSeparatingProgress

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

abbrev address {n : Nat} (e : Fin n) (a : At (Fin 11)) : Pos n :=
  (site e a.side,a.occurrence)

def project (addr : Nat → Pos n) (x : X) : BStarSeparatingRail.Rail :=
  fun j => atCursor x (addr j)

def onLink (x : X) (e : Fin n) (addr : Nat → Pos n) (j : Nat) : Prop :=
  ∃ C d, C∈orderedCommands (oldPair B x e) ∧ C.destination=some d ∧
    addr j=address e C.source ∧ addr (j+1)=address e d

def onTerminal (x : X) (e : Fin n) (addr : Nat → Pos n) (len : Nat) : Prop :=
  ∃ C, C∈orderedCommands (oldPair B x e) ∧ C.kind=.terminal ∧ C.destination=none ∧
    C.source.occurrence.val=10 ∧ addr len=address e C.source

structure Quiet (tag : Tag) (len : Nat) (u v : BStarSeparatingRail.Rail)
    (link : Nat → Prop) (term : Prop) : Prop where
  idle : ∀ j≤len, ¬link j → (∀ i, i+1=j → ¬link i) → (j=len → ¬term) →
    (u j=.trail → v j=.trail) ∧ (u j=.empty → v j=.empty) ∧
      (tag.F (u j) → tag.F (v j)) ∧ (tag.D (u j) → tag.D (v j))
  tt : ∀ j, link j → u j=.trail → u (j+1)=.trail → v j=.trail ∧ v (j+1)=.trail
  ee : ∀ j, link j → u j=.empty → u (j+1)=.empty → v j=.empty ∧ v (j+1)=.empty
  tf : ∀ j, link j → u j=.trail → tag.F (u (j+1)) → v j=.trail ∧ tag.F (v (j+1))
  de : ∀ j, link j → tag.D (u j) → u (j+1)=.empty → tag.D (v j) ∧ v (j+1)=.empty
  termD : term → tag.D (u len) → tag.D (v len)
  termE : term → u len=.empty → v len=.empty

/-- Bound the physical mark's link indices at creation, so there is no
dependence on how the address function is padded beyond the rail. -/
def linkAt (x : X) (e : Fin n) (addr : Nat → Pos n) (len j : Nat) : Prop :=
  j<len ∧ onLink hp x e addr j

noncomputable def labels (x : X) (e : Fin n) (addr : Nat → Pos n) (len : Nat) : List Label := by
  classical
  exact ((List.range len).filter fun j => decide (onLink hp x e addr j)).map Label.link ++
    if onTerminal hp x e addr len then [.terminal] else []

theorem mem_link (x : X) (e : Fin n) (addr : Nat → Pos n) (len j : Nat) :
    Label.link j∈labels hp x e addr len ↔ linkAt hp x e addr len j := by
  classical
  unfold labels linkAt
  split <;> simp [and_comm]

theorem mem_terminal (x : X) (e : Fin n) (addr : Nat → Pos n) (len : Nat) :
    Label.terminal∈labels hp x e addr len ↔ onTerminal hp x e addr len := by
  classical
  unfold labels
  split <;> simp_all

theorem address_inj (e : Fin n) (he : e≠rightNeighbor e)
    {a d : At (Fin 11)} (h : address e a=address e d) : a=d := by
  rcases a with ⟨a,k⟩
  rcases d with ⟨d,j⟩
  cases a <;> cases d <;> simp_all [address,site,Ne.symm he]

theorem link_disjoint (x : X) (e : Fin n) (he : e≠rightNeighbor e)
    (addr : Nat → Pos n) (len j : Nat)
    (A : linkAt hp x e addr len j) (D : linkAt hp x e addr len (j+1)) : False := by
  obtain ⟨_,C,d,hC,dC,_,hit⟩ := A
  obtain ⟨_,K,t,hK,dK,Y,_⟩ := D
  have E := address_inj e he (hit.symm.trans Y)
  have same := BStarAcquireIncidence.same_claim _ C K d hC hK
    (by simp [Claim.slots,dC]) (by simp [Claim.slots,E])
  subst K
  exact ((BStarAcquireReturn.link_shape _ C d hC dC).1 E).elim

theorem terminal_disjoint (x : X) (e : Fin n) (he : e≠rightNeighbor e)
    (addr : Nat → Pos n) (len j : Nat)
    (A : linkAt hp x e addr len j) (h : j+1=len)
    (D : onTerminal hp x e addr len) : False := by
  obtain ⟨_,C,d,hC,dC,_,hit⟩ := A
  obtain ⟨K,hK,_,dK,_,Y⟩ := D
  have E := address_inj e he (hit.symm.trans (h.symm ▸ Y))
  have same := BStarAcquireIncidence.same_claim _ C K d hC hK
    (by simp [Claim.slots,dC]) (by simp [Claim.slots,E])
  subst K
  rw [dC] at dK
  cases dK

/-- The active transition fields of Service are not assumptions:
they are the actual old-pair selected rows, with canonical fault
remaining a carrier of the original tagged operation. -/
noncomputable def actualService (x : X) (e : Fin n) (he : e≠rightNeighbor e)
    (adr : Nat → Pos n) (len op : Nat) (ho : op<3)
    (quiet : Quiet (resetTag op) len (project adr x) (project adr (AllSizeS1Geometry.step B x e))
      (linkAt hp x e adr len) (onTerminal hp x e adr len)) :
    Service (resetTag op) len (project adr x) (project adr (AllSizeS1Geometry.step B x e)) := by
  have fx (j : Nat) (L : linkAt hp x e adr len j) (F : (resetTag op).F (project adr x j)) :
      project adr (AllSizeS1Geometry.step B x e) j=.trail ∧
      (resetTag op).F (project adr (AllSizeS1Geometry.step B x e) (j+1)) := by
    obtain ⟨_,C,d,hc,hd,S,D⟩ := L
    unfold project at F ⊢
    rw [S] at F ⊢
    rw [D]
    exact forward_service hp x e he C d op ho hc hd F
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
    exact backward_service hp x e he C d op ho hc hd T D
  · rintro ⟨C,hC,hk,hd,k,S⟩ F
    unfold project at F ⊢
    rw [S] at F ⊢
    exact terminal_service hp x e he C op ho hC hk hd k F

#print axioms mem_link
#print axioms mem_terminal
#print axioms actualService
end L4.BStarResetMarkAdapter
