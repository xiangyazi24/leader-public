import Leader.L4.BStarFenceLineGeometry

namespace L4.BStarFenceFootprint
open AllSizeProtocol BStarTrace BStarLongClaims BStarH6WordChart BStarLongWork
open BStarFenceLineGeometry
open BStarCopyRightStrip (addr addr_next)
open BStarLongFixedRouting

def leftClaim (d r j : Nat) (s : Side) : Option DataClaim :=
  match s with
  | .left => if j+1<d+r then
      some (hop (L (BStarCopyLeftStrip.rail d j)) (R (BStarCopyLeftStrip.rail d (j+1))))
    else some (ending (L .ld))
  | .right => if 0<j then
      some (hop (L (BStarCopyLeftStrip.rail d (j-1))) (R (BStarCopyLeftStrip.rail d j)))
    else none

def rightClaim (d r j : Nat) (s : Side) : Option DataClaim :=
  match s with
  | .left => if j+1<d+r then
      some (hop (R (rightRail d (j+1))) (L (rightRail d j)))
    else none
  | .right => if 0<j then
      some (hop (R (rightRail d j)) (L (rightRail d (j-1))))
    else some (ending (R .rd))

private theorem pairwise_unique {α γ : Type} (slots : γ → List α)
    {l : List γ} (H : l.Pairwise (fun c d => ∀ s∈slots d,s∉slots c))
    {a : α} {c d : γ} (C : c∈l) (D : d∈l) (A : a∈slots c) (B : a∈slots d) : c=d := by
  induction H with
  | nil => contradiction
  | @cons h t J _ ih =>
    rcases List.mem_cons.mp C with E|C'
    · subst c
      rcases List.mem_cons.mp D with E|D'
      · exact E.symm
      · exact (J _ D' _ B A).elim
    · rcases List.mem_cons.mp D with E|D'
      · subst h
        exact (J _ C' _ A B).elim
      · exact ih C' D' 

theorem nominal_unique (g : Pair LongGeometry) (a : At Sheet) (c d : DataClaim)
    (C : c∈orderedData g []) (D : d∈orderedData g []) (A : a∈c.slots) (B : a∈d.slots) :
    c=d :=
  pairwise_unique Claim.slots (select_pairwise Claim.slots [] (offers dataKey (dataClaims g))) C D A B

private theorem exact_of_present (g : Pair LongGeometry) (a : At Sheet) (c d : DataClaim)
    (M : d∈orderedData g []) (A : a∈d.slots) :
    (c∈orderedData g [] ∧ a∈c.slots) ↔ some d=some c := by
  constructor
  · rintro ⟨C,H⟩
    exact congrArg some (nominal_unique g a d c M C A H)
  · rintro H
    have E := Option.some.inj H
    exact E ▸ ⟨M,A⟩

private theorem incoming_edge {n : Nat} {root e : Fin n} {j : Nat}
    (pos : 0<j) (H : rightNeighbor e=addr root j) : e=addr root (j-1) := by
  have N : rightNeighbor (addr root (j-1))=addr root j := by
    rw [←addr_next,show j-1+1=j by omega]
  exact (RearTrace.predecessor_right e).symm.trans
    ((congrArg RearTrace.predecessor (H.trans N.symm)).trans
      (RearTrace.predecessor_right _))

private theorem finZero {n : Nat} (a : Fin n) : addr a 0=a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

theorem left_footprint {p : LargeParams} {n : Nat} {b : LargeRows p}
    {x : Fin n → LargeSite p} {root e : Fin n} {d r j : Nat} (s : Side)
    (F : BStarCopyLeftStrip.Strip b x root d r) (J : j<d+r)
    (P : site e s=addr root j) (c : DataClaim) :
    (c∈orderedData (oldPair b x e) [] ∧ (⟨s,BStarCopyLeftStrip.rail d j⟩ : At Sheet)∈c.slots) ↔
      leftClaim d r j s=some c := by
  cases s with
  | left =>
    change e=addr root j at P
    subst e
    by_cases H : j+1<d+r
    · simp only [leftClaim,if_pos H]
      exact exact_of_present _ _ _ _ (left_adjacent F j H) (by simp [Claim.slots,hop,L])
    · have E : j=d+r-1 := by omega
      have lane : BStarCopyLeftStrip.rail d j=.ld := if_neg (by have := F.width_pos; omega)
      rw [lane]
      simp only [leftClaim,if_neg H]
      exact exact_of_present _ _ _ _ (E.symm ▸ left_terminal F) (by simp [Claim.slots,ending,L])
  | right =>
    change rightNeighbor e=addr root j at P
    by_cases H : 0<j
    · obtain rfl := incoming_edge H P
      simp only [leftClaim,if_pos H]
      have W := left_adjacent F (j-1) (by omega)
      rw [show j-1+1=j by omega] at W
      exact exact_of_present _ _ _ _ W (by simp [Claim.slots,hop,R])
    · have E : j=0 := by omega
      subst j
      have lane : BStarCopyLeftStrip.rail d 0=.ls := if_pos F.seam_pos
      simp only [leftClaim,if_neg H,(fun c => (Option.eq_none_iff_forall_ne_some.mp rfl c) : ∀ c : DataClaim, (none : Option DataClaim) ≠ some c),iff_false,lane]
      rintro ⟨M,T⟩
      have nv := BStarCopyLeftStrip.source_no_ingress F e [] c M .right
        (P.trans (finZero root))
      rcases List.mem_cons.mp T with S|T
      · have raw := (nominal_iff_raw _ _).mp M
        have S' : c.source=R .ls := S.symm
        -- Left-going LS/LD source slots never lie on the right.
        unfold dataClaims at raw
        generalize h : (oldPair b x e).2.axes.h6=hh at raw
        generalize i : (oldPair b x e).2.inside=ii at raw
        generalize l : (oldPair b x e).1.inside=ll at raw
        generalize k : ends (oldPair b x e).1=kk at raw
        cases hh <;> cases ii <;> cases ll <;> cases kk <;>
          simp [h,i,l,k,hop,ending] at raw <;> grind [L,R]
      · exact nv (by
          cases D : c.destination with
          | none => simp [D] at T
          | some a =>
            have A : (⟨Side.right,.ls⟩ : At Sheet)=a := by simpa [D] using T
            subst a
            rfl)

theorem right_footprint {p : LargeParams} {n : Nat} {b : LargeRows p}
    {x : Fin n → LargeSite p} {root e : Fin n} {d r j : Nat} (s : Side)
    (F : RightFrame b x root d r) (D : 0<d)
    (tail : ends (longGeometry b (x (addr root (d+r-1))))=true)
    (J : j<d+r) (P : site e s=addr root j) (c : DataClaim) :
    (c∈orderedData (oldPair b x e) [] ∧ (⟨s,rightRail d j⟩ : At Sheet)∈c.slots) ↔
      rightClaim d r j s=some c := by
  cases s with
  | left =>
    change e=addr root j at P
    subst e
    by_cases H : j+1<d+r
    · simp only [rightClaim,if_pos H]
      exact exact_of_present _ _ _ _ (F.adjacent j H) (by simp [Claim.slots,hop,L])
    · simp only [rightClaim,if_neg H,(fun c => (Option.eq_none_iff_forall_ne_some.mp rfl c) : ∀ c : DataClaim, (none : Option DataClaim) ≠ some c),iff_false]
      rintro ⟨M,T⟩
      have E : j=d+r-1 := by omega
      have lane : rightRail d j=.rs := if_neg (by have := F.width_pos; omega)
      rw [lane] at T
      have raw := (nominal_iff_raw _ _).mp M
      rcases List.mem_cons.mp T with S|S
      · exact (BStarCopyRightStrip.no_left_send _ _ raw).2 S.symm
      · have dest : c.destination=some (L .rs) := by
          cases U : c.destination with
          | none => simp [U] at S
          | some a =>
            have A : (⟨Side.left,.rs⟩ : At Sheet)=a := by simpa [U] using S
            subst a
            rfl
        have X := (BStarCopyRightStrip.raw_rs_receive _ _ dest).mp raw
        have Z : ends (oldPair b x (addr root j)).1=true := E.symm ▸ tail
        rw [Z] at X
        exact Bool.noConfusion X.2.2.2.1
  | right =>
    change rightNeighbor e=addr root j at P
    by_cases H : 0<j
    · obtain rfl := incoming_edge H P
      simp only [rightClaim,if_pos H]
      have W := F.adjacent (j-1) (by omega)
      rw [show j-1+1=j by omega] at W
      exact exact_of_present _ _ _ _ W (by simp [Claim.slots,hop,R])
    · have E : j=0 := by omega
      subst j
      rw [finZero] at P
      have Q := (RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor P)
      subst e
      have lane : rightRail d 0=.rd := if_pos D
      simp only [rightClaim,if_neg H,lane]
      exact exact_of_present _ _ _ _ (right_terminal F) (by simp [Claim.slots,ending,R])

theorem quiet_outside_mark {p : LargeParams} {n : Nat} (b : LargeRows p)
    (x : Fin n → LargeSite p) (e i : Fin n) (L' : i≠e) (R' : i≠rightNeighbor e) :
    AllSizeS1Geometry.step b x e i=x i := by
  simp [AllSizeS1Geometry.step,L',R']

#print axioms left_footprint
#print axioms right_footprint
#print axioms quiet_outside_mark

theorem left_footprint_layout {p : LargeParams} {n : Nat} {b : LargeRows p}
    {x y : Fin n → LargeSite p} {root e : Fin n} {d r j : Nat} (s : Side)
    (F : BStarCopyLeftStrip.Strip b x root d r) (J : j<d+r)
    (same : ∀ i,Layout b x i=Layout b y i)
    (P : site e s=addr root j) (c : DataClaim) :
    (c∈orderedData (oldPair b y e) [] ∧ (⟨s,BStarCopyLeftStrip.rail d j⟩ : At Sheet)∈c.slots) ↔
      leftClaim d r j s=some c := by
  rw [←data_eq b x y same e]
  exact left_footprint s F J P c

theorem right_footprint_layout {p : LargeParams} {n : Nat} {b : LargeRows p}
    {x y : Fin n → LargeSite p} {root e : Fin n} {d r j : Nat} (s : Side)
    (F : RightFrame b x root d r) (D : 0<d)
    (tail : ends (longGeometry b (x (addr root (d+r-1))))=true)
    (J : j<d+r) (same : ∀ i,Layout b x i=Layout b y i)
    (P : site e s=addr root j) (c : DataClaim) :
    (c∈orderedData (oldPair b y e) [] ∧ (⟨s,rightRail d j⟩ : At Sheet)∈c.slots) ↔
      rightClaim d r j s=some c := by
  rw [←data_eq b x y same e]
  exact right_footprint s F D tail J P c

private theorem left_rail_kind (d j : Nat) :
    BStarCopyLeftStrip.rail d j=.ls ∨ BStarCopyLeftStrip.rail d j=.ld := by
  unfold BStarCopyLeftStrip.rail
  split
  · exact .inl rfl
  · exact .inr rfl

private theorem right_rail_kind (d j : Nat) : rightRail d j=.rs ∨ rightRail d j=.rd := by
  unfold rightRail
  split
  · exact .inr rfl
  · exact .inl rfl

private theorem left_slots {d r j : Nat} {s : Side} {c : DataClaim}
    (C : leftClaim d r j s=some c) (a : At Sheet) (A : a∈c.slots) :
    a.occurrence=.ls ∨ a.occurrence=.ld := by
  cases s <;> simp only [leftClaim] at C <;> split at C
  · obtain rfl := Option.some.inj C
    simp only [Claim.slots,hop,Option.toList_some,List.mem_cons,List.not_mem_nil,or_false] at A
    rcases A with rfl|rfl <;> exact left_rail_kind _ _
  · obtain rfl := Option.some.inj C
    simp only [Claim.slots,ending,Option.toList_none,List.mem_singleton] at A
    subst a
    exact .inr rfl
  · obtain rfl := Option.some.inj C
    simp only [Claim.slots,hop,Option.toList_some,List.mem_cons,List.not_mem_nil,or_false] at A
    rcases A with rfl|rfl <;> exact left_rail_kind _ _
  · contradiction

private theorem right_slots {d r j : Nat} {s : Side} {c : DataClaim}
    (C : rightClaim d r j s=some c) (a : At Sheet) (A : a∈c.slots) :
    a.occurrence=.rs ∨ a.occurrence=.rd := by
  cases s <;> simp only [rightClaim] at C <;> split at C
  · obtain rfl := Option.some.inj C
    simp only [Claim.slots,hop,Option.toList_some,List.mem_cons,List.not_mem_nil,or_false] at A
    rcases A with rfl|rfl <;> exact right_rail_kind _ _
  · contradiction
  · obtain rfl := Option.some.inj C
    simp only [Claim.slots,hop,Option.toList_some,List.mem_cons,List.not_mem_nil,or_false] at A
    rcases A with rfl|rfl <;> exact right_rail_kind _ _
  · obtain rfl := Option.some.inj C
    simp only [Claim.slots,ending,Option.toList_none,List.mem_singleton] at A
    subst a
    exact .inr rfl

/-- Same physical mark may service both lines, but their complete
typed claim footprints are disjoint, including genuine terminals. -/
theorem same_mark_disjoint {d r j D R k : Nat} {s t : Side} {c f : DataClaim}
    (L : leftClaim d r j s=some c) (H : rightClaim D R k t=some f) :
    ∀ a∈c.slots, a∉f.slots := by
  intro a A B
  have x := left_slots L a A
  have y := right_slots H a B
  rcases x with x|x <;> rw [x] at y <;> rcases y with y|y <;> contradiction

/-- Arbitrary reservations cannot manufacture a claim absent from the
nominal footprint. Conversely an unreserved nomination is selected. -/
theorem selected_iff_nominal_free (g : Pair LongGeometry) (rv : List (At Sheet)) (c : DataClaim) :
    c∈orderedData g rv ↔ c∈orderedData g [] ∧ ∀ a∈c.slots, a∉rv := by
  rw [BStarClearancePrepOwner.orderedData_filter]
  exact List.mem_filter.trans (and_congr_right fun _ => free_iff _ _)

#print axioms left_footprint_layout
#print axioms right_footprint_layout
#print axioms same_mark_disjoint
#print axioms selected_iff_nominal_free
end L4.BStarFenceFootprint
