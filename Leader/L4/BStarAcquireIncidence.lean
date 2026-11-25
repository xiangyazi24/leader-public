import Leader.L4.BStarAcquireRailUniqueness
import Leader.L4.FreshSeparation
import Leader.L4.BStarAcquireVisitOrder

namespace L4.BStarAcquireIncidence
open AllSizeProtocol BStarLongClaims BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireRailUniqueness

theorem same_claim (g : Pair LongGeometry) (C D : CommandClaim) (k : At (Fin 11))
    (hc : C∈orderedCommands g) (hd : D∈orderedCommands g)
    (h1 : k∈C.slots) (h2 : k∈D.slots) : C=D := by
  obtain ⟨l,r,E⟩ := List.mem_iff_append.mp hc
  have P : (orderedCommands g).Pairwise (fun u v => ∀ s∈v.slots,s∉u.slots) :=
    select_pairwise Claim.slots [] (offers commandKey (commandClaims g))
  rw [E] at P hd
  rcases List.mem_append.mp hd with L|R
  · exact (P.rel_of_mem_append L List.mem_cons_self k h1 h2).elim
  · rcases List.mem_cons.mp R with R|R
    · exact R.symm
    · exact (((List.pairwise_cons.mp (List.pairwise_append.mp P).2.1).1 D R) k h2 h1).elim

private theorem address_ext {u v : At (Fin 11)} (S : u.side=v.side)
    (O : u.occurrence=v.occurrence) : u=v := by
  rcases u with ⟨u,j⟩
  rcases v with ⟨v,k⟩
  cases S
  cases O
  rfl

private theorem physical_occurrence {n : Nat} {i j : Fin n} {a b : At (Fin 11)}
    (h : (site i a.side,a.occurrence)=(site j b.side,b.occurrence)) :
    a.occurrence=b.occurrence := congrArg Prod.snd h

theorem successor_unique {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (u v w : Pos n)
    (A : Edge b x u v) (B : Edge b x u w) : v=w := by
  obtain ⟨e,C,d,hC,hD,rfl,rfl⟩ := A
  obtain ⟨f,K,t,hK,hT,src,rfl⟩ := B
  have isLinkC : C.kind=.link := (BStarAcquireReturn.link_shape _ C d hC hD).2.1
  have isLinkK : K.kind=.link := (BStarAcquireReturn.link_shape _ K t hK hT).2.1
  have H := congrArg Prod.fst src
  have P := physical_occurrence src
  have same (E : e=f) (side : C.source.side=K.source.side) :
      (site e d.side,d.occurrence)=(site f t.side,t.occurrence) := by
    subst f
    have J : C.source=K.source := address_ext side P
    have W := same_claim _ C K C.source hC hK (by simp [Claim.slots]) (by simp [Claim.slots,J])
    subst K
    rw [hD] at hT
    cases hT
    rfl
  cases U : C.source.side <;> cases V : K.source.side
  · exact same (by simpa [site,U,V] using H) (U.trans V.symm)
  · have E : e=rightNeighbor f := by simpa [site,U,V] using H
    have Q1 : C.source=L C.source.occurrence := address_ext U rfl
    have Q2 : K.source=R C.source.occurrence := address_ext V P.symm
    have r1 : C.kind≠.door := by rw [isLinkC]; decide
    have r2 : K.kind≠.door := by rw [isLinkK]; decide
    subst e
    exact (one_departure_port _ _ _ K C _ hK hC Q2 Q1 r2 r1).elim
  · have E : f=rightNeighbor e := by simpa [site,U,V] using H.symm
    have Q1 : C.source=R C.source.occurrence := address_ext U rfl
    have Q2 : K.source=L C.source.occurrence := address_ext V P.symm
    have r1 : C.kind≠.door := by rw [isLinkC]; decide
    have r2 : K.kind≠.door := by rw [isLinkK]; decide
    subst f
    exact (one_departure_port _ _ _ C K _ hC hK Q1 Q2 r1 r2).elim
  · exact same (FreshSeparation.succ_inj (by simpa [site,U,V] using H)) (U.trans V.symm)

theorem predecessor_unique {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (u v w : Pos n)
    (A : Edge b x v u) (B : Edge b x w u) : v=w := by
  obtain ⟨e,C,d,hC,hD,rfl,rfl⟩ := A
  obtain ⟨f,K,t,hK,hT,rfl,src⟩ := B
  have H := congrArg Prod.fst src
  have P := physical_occurrence src
  have same (E : e=f) (side : d.side=t.side) :
      (site e C.source.side,C.source.occurrence)=(site f K.source.side,K.source.occurrence) := by
    subst f
    have J : d=t := address_ext side P
    have W := same_claim _ C K d hC hK (by simp [Claim.slots,hD]) (by simp [Claim.slots,hT,J])
    subst K
    rfl
  cases U : d.side <;> cases V : t.side
  · exact same (by simpa [site,U,V] using H) (U.trans V.symm)
  · have E : e=rightNeighbor f := by simpa [site,U,V] using H
    have Q1 : d=L d.occurrence := address_ext U rfl
    have Q2 : t=R d.occurrence := address_ext V P.symm
    subst e
    exact (one_predecessor_port _ _ _ K C _ hK hC (hT.trans (congrArg some Q2))
      (hD.trans (congrArg some Q1))).elim
  · have E : f=rightNeighbor e := by simpa [site,U,V] using H.symm
    have Q1 : d=R d.occurrence := address_ext U rfl
    have Q2 : t=L d.occurrence := address_ext V P.symm
    subst f
    exact (one_predecessor_port _ _ _ C K _ hC hK (hD.trans (congrArg some Q1))
      (hT.trans (congrArg some Q2))).elim
  · exact same (FreshSeparation.succ_inj (by simpa [site,U,V] using H)) (U.trans V.symm)

end L4.BStarAcquireIncidence
