import Leader.L4.BStarAcquireAnchors
import Leader.L4.BStarAcquireChainEndpoints
import Leader.L4.BStarAcquireIncidence
import Leader.L4.RearGeometry

namespace L4.BStarAcquireLiteralChain
open AllSizeProtocol BStarLongClaims BStarH6WordChart BStarH6Ordinal
open BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireGlobalChain BStarCommandChronology

variable {a : LargeParams} {n : Nat}

abbrev Owners {n : Nat} (h : Fin n → Bool) := {o : Int // 0≤o ∧ o<(total h : Int)}

noncomputable def endpoint {n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (o : Owners h) (k : Fin 11) : Pos n :=
  ((Classical.choose (unique_command_header h hh o.val o.property.1 o.property.2 k)).val,k)

theorem endpoint_spec {n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (o : Owners h) (k : Fin 11) :
    h (endpoint h hh o k).1=true ∧
    commandOwner h (endpoint h hh o k).1 k=o.val ∧
    ∀ i, h i=true → commandOwner h i k=o.val → (i,k)=endpoint h hh o k := by
  let H := unique_command_header h hh o.val o.property.1 o.property.2 k
  refine ⟨(Classical.choose H).property,(Classical.choose_spec H).1,?_⟩
  intro i hi eq
  have E := (Classical.choose_spec H).2 ⟨i,hi⟩ eq
  exact congrArg (fun j : Header h => (j.val,k)) E

def own {n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (v : Pos n) : Owners h :=
  ⟨commandOwner h v.1 v.2,commandOwner_range h hh v.1 v.2⟩

private theorem local_geo {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (e : Fin n) (s : Side) :
    BStarLongCommand.geometry (oldPair b x e) s=longGeometry b (x (site e s)) := by
  cases s <;> rfl

/-- Literal full fixed rail. The assumption is the ordinal IN/LAST
condition, with enough significant sites before the next H6 seam. -/
noncomputable def literal (b : LargeRows a) (x : Fin n → LargeSite a)
    (hh : ∃ i,oldH6 b x i=true) (r : Nat) (hr : 0<r)
    (flags : ∀ i, let g := longGeometry b (x i)
      g.inside=decide (oldOrdinal b x hh i<r) ∧
      g.last=decide (oldOrdinal b x hh i+1=r))
    (notShort : ∀ i, oldH6 b x (rightNeighbor i)=true → r≤oldOrdinal b x hh i+1) :
    BStarAcquireGlobalChain.Rail (Pos n) (Owners (oldH6 b x)) := by
  let h := oldH6 b x
  let G (i : Fin n) := longGeometry b (x i)
  let O := own h hh
  have geo := geometry_ports b x hh hr flags notShort
  refine {
    active := fun u => active (G u.1) u.2=true
    owner := O
    rank := fun u => rank h hh u.1 u.2
    root := fun o => endpoint h hh o 0
    terminal := fun o => endpoint h hh o 10
    edge := Edge b x
    fuel := 11*n
    root_active := ?_
    root_owner := ?_
    terminal_owner := ?_
    edge_active := ?_
    edge_owner := ?_
    edge_rank := ?_
    rank_bound := ?_
    pred := ?_
    succ := ?_
    succ_unique := fun {u v w} => BStarAcquireIncidence.successor_unique b x u v w
    no_terminal_exit := ?_ }
  · intro o
    rfl
  · intro o
    exact Subtype.ext (endpoint_spec h hh o 0).2.1
  · intro o
    exact Subtype.ext (endpoint_spec h hh o 10).2.1
  · rintro u v ⟨e,C,D,hC,hD,rfl,rfl⟩
    have T := BStarAcquireChainEndpoints.link_endpoints (oldPair b x e) C D hC hD
    rw [local_geo,local_geo] at T
    exact ⟨T.1,T.2.1⟩
  · rintro u v ⟨e,C,D,hC,hD,rfl,rfl⟩
    exact Subtype.ext (actual_link b x hh e C D hC hD).2
  · rintro u v ⟨e,C,D,hC,hD,rfl,rfl⟩
    exact (actual_link b x hh e C D hC hD).1
  · intro u _
    unfold rank
    have H := (ordinal_spec h hh u.1).1
    have M := Nat.mul_le_mul_right n (show u.2.val≤10 by have := u.2.isLt; omega)
    split <;> omega
  · rintro ⟨i,k⟩ hi ne
    let j := RearTrace.predecessor i
    have J : rightNeighbor j=i := RearTrace.right_predecessor i
    have L : continuation (G j) (G i)=true := by
      have T := geo.2 j
      change continuation (G j) (G (rightNeighbor j))=true at T
      rwa [J] at T
    have exc : ¬ ((G i).axes.h6=true ∧ k.val=0) := by
      rintro ⟨H,K⟩
      have eq : k=0 := Fin.ext K
      subst k
      exact ne ((endpoint_spec h hh (O (i,0)) 0).2.2 i H rfl)
    rcases predecessor (G j) (G i) (G (rightNeighbor i)) (geo.1 i)
        (geo.1 (rightNeighbor i)) L (geo.2 i) k hi exc with ⟨C,hC,hD⟩|⟨C,hC,hD⟩
    · refine ⟨_,j,C,R k,?_,hD,rfl,?_⟩
      · change C∈orderedCommands (G j,G (rightNeighbor j))
        rwa [J]
      · simp [J,site,R]
    · exact ⟨_,i,C,BStarLongClaims.L k,hC,hD,rfl,rfl⟩
  · rintro ⟨i,k⟩ hi ne
    let j := RearTrace.predecessor i
    have J : rightNeighbor j=i := RearTrace.right_predecessor i
    have L : continuation (G j) (G i)=true := by
      have T := geo.2 j
      change continuation (G j) (G (rightNeighbor j))=true at T
      rwa [J] at T
    have go (e : Fin n) (C : CommandClaim) (hc : C∈orderedCommands (oldPair b x e))
        (hs : (i,k)=(site e C.source.side,C.source.occurrence)) (hn : C.kind≠.door) :
        ∃ u, Edge b x (i,k) u := by
      cases d : C.destination with
      | some D => exact ⟨_,e,C,D,hc,d,hs,rfl⟩
      | none =>
        have T := BStarAcquireChainEndpoints.terminal _ C hc d hn
        have P : i=rightNeighbor e := by simpa [site,T.2.1] using congrArg Prod.fst hs
        have K : k=10 := Fin.ext ((congrArg (fun v : Pos n => v.2.val) hs).trans T.2.2.2)
        subst k
        have I : h i=true := by rw [P]; exact T.2.2.1
        exact (ne ((endpoint_spec h hh (O (i,10)) 10).2.2 i I rfl)).elim
    rcases departure (G j) (G i) (G (rightNeighbor i)) (geo.1 i)
        (geo.1 (rightNeighbor i)) L (geo.2 i) k hi with ⟨C,hC,hs,hn⟩|⟨C,hC,hs,hn⟩
    · apply go j C _ _ hn
      · change C∈orderedCommands (G j,G (rightNeighbor j))
        rwa [J]
      · simp [hs,R,site,J]
    · exact go i C hC (by simp [hs,BStarLongClaims.L,site]) hn
  · rintro u v ⟨e,C,D,hC,hD,rfl,rfl⟩ E
    have T := (BStarAcquireChainEndpoints.link_endpoints (oldPair b x e) C D hC hD).2.2.1
    rw [local_geo] at T
    apply T
    have ep := (endpoint_spec h hh (O (site e C.source.side,C.source.occurrence)) 10).1
    have H := congrArg Prod.fst E
    have K := congrArg (fun z : Pos n => z.2.val) E
    refine ⟨?_,K⟩
    change h (site e C.source.side)=true
    exact (congrArg h H).trans ep

#print axioms literal
end L4.BStarAcquireLiteralChain
