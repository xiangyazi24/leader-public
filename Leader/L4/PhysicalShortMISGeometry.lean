import Leader.L4.PhysicalCustody

namespace L4.PhysicalCustody
open AllSizeProtocol AllSizeS1Geometry BStarH6Ordinal

def ShortPrecision {s n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (k : Nat) (x : Raw s n) : Prop :=
  ∀ i, min k (off (x i))=min k (ordinal h hh i)

theorem short_offset_mark {s n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (x : Raw s n) (e : Fin n) (sep : rightNeighbor e≠e)
    (same : ∀ i,header (x i)=h i)
    (k : Nat) (hk : k<3) (P : ShortPrecision h hh k x) :
    ShortPrecision h hh k (rawNext s x e) ∧
    ∀ i, (i=rightNeighbor e ∨ min (k+1) (off (x i))=min (k+1) (ordinal h hh i)) →
      min (k+1) (off (rawNext s x e i))=min (k+1) (ordinal h hh i) := by
  obtain ⟨_,R,L,_⟩ := refresh (rows s) x e sep
  change off (rawNext s x e (rightNeighbor e))=_ at R
  change off (rawNext s x e e)=_ at L
  have keep (i : Fin n) (ne : i≠rightNeighbor e) :
      off (rawNext s x e i)=off (x i) := by
    by_cases E : i=e
    · subst i; exact L
    · simp [rawNext,AllSizeS1Geometry.step,E,ne]
  simp only [same] at R
  have R' : min (k+1) (off (rawNext s x e (rightNeighbor e)))=
      min (k+1) (ordinal h hh (rightNeighbor e)) := by
    rw [R,ordinal_right]
    by_cases q : h (rightNeighbor e)=true
    · simp [q]
    ·   rw [if_neg q,if_neg q]
        by_cases a : h e=true
        · rw [if_pos a,(ordinal_zero h hh e).mpr a]
          omega
        · rw [if_neg a]
          have z := P e
          omega
  refine ⟨?_,?_⟩
  · intro i
    by_cases E : i=rightNeighbor e
    · subst i; omega
    · rw [keep i E]
      exact P i
  · intro i H
    rcases H with E|prior
    · subst i; exact R'
    · by_cases E : i=rightNeighbor e
      · subst i; exact R'
      · rwa [keep i E]

theorem short_offset_cover {s n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (sep : ∀ e : Fin n,rightNeighbor e≠e)
    (Q : Raw s n→Prop) (closed : ∀ x e,Q x→Q (rawNext s x e))
    (same : ∀ x,Q x→∀ i,header (x i)=h i)
    (x : Raw s n) (qx : Q x) (w : List (Fin n)) (k : Nat) (hk : k<3)
    (P : ShortPrecision h hh k x) :
    Q (rawRun x w) ∧ ShortPrecision h hh k (rawRun x w) ∧
    ∀ i, ((∃ e∈w,rightNeighbor e=i) ∨ min (k+1) (off (x i))=min (k+1) (ordinal h hh i)) →
      min (k+1) (off (rawRun x w i))=min (k+1) (ordinal h hh i) := by
  induction w generalizing x with
  | nil =>
    refine ⟨qx,P,?_⟩
    rintro i (⟨e,he,_⟩|prior)
    · cases he
    · exact prior
  | cons e w ih =>
    obtain ⟨prior,raise⟩ := short_offset_mark h hh x e (sep e) (same x qx) k hk P
    obtain ⟨qn,pn,F⟩ := ih (rawNext s x e) (closed x e qx) prior
    refine ⟨qn,pn,?_⟩
    intro i I
    apply F
    rcases I with ⟨f,hf,eq⟩|already
    · rcases List.mem_cons.mp hf with E|J
      · subst f; exact .inr (raise i (.inl eq.symm))
      · exact .inl ⟨f,J,eq⟩
    · exact .inr (raise i (.inr already))

theorem short_successor_word {s n : Nat} (h : Fin n→Bool)
    (sep : ∀ e : Fin n,rightNeighbor e≠e)
    (Q : Raw s n→Prop) (closed : ∀ x e,Q x→Q (rawNext s x e))
    (same : ∀ x,Q x→∀ i,header (x i)=h i)
    (x : Raw s n) (qx : Q x) (w : List (Fin n)) (i : Fin n)
    (P : i∈w ∨ successor (x i)=BitVec.ofNat 1 (h (rightNeighbor i)).toNat) :
    successor (rawRun x w i)=BitVec.ofNat 1 (h (rightNeighbor i)).toNat := by
  induction w generalizing x with
  | nil => exact P.resolve_left List.not_mem_nil
  | cons e w ih =>
    obtain ⟨A,_,_,B⟩ := refresh (rows s) x e (sep e)
    apply ih (rawNext s x e) (closed x e qx)
    by_cases E : i=e
    · subst i
      exact .inr (A.trans (congrArg (fun v : Bool=>BitVec.ofNat 1 v.toNat) (same x qx _)))
    rcases P with mem|prior
    · exact .inl ((List.mem_cons.mp mem).resolve_left E)
    · right
      by_cases F : i=rightNeighbor e
      · subst i; exact B.trans prior
      · simpa only [rawNext,AllSizeS1Geometry.step,if_neg E,if_neg F] using prior

theorem short_geometry_three_covers {s n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (sep : ∀ e : Fin n,rightNeighbor e≠e)
    (Q : Raw s n→Prop) (closed : ∀ x e,Q x→Q (rawNext s x e))
    (same : ∀ x,Q x→∀ i,header (x i)=h i)
    (x : Raw s n) (qx : Q x) (u v w : List (Fin n))
    (U : ∀ e,e∈u) (V : ∀ e,e∈v) (W : ∀ e,e∈w) :
    let z := rawRun (rawRun (rawRun x u) v) w
    Q z ∧ ∀ i,off (z i)=min 3 (ordinal h hh i) ∧
      successor (z i)=BitVec.ofNat 1 (h (rightNeighbor i)).toNat := by
  have advance (x : Raw s n) (qx : Q x) (w : List (Fin n)) (W : ∀ e,e∈w)
      (k : Nat) (hk : k<3) (C : ShortPrecision h hh k x) :
      Q (rawRun x w) ∧ ShortPrecision h hh (k+1) (rawRun x w) := by
    have D := short_offset_cover h hh sep Q closed same x qx w k hk C
    exact ⟨D.1,fun i=>D.2.2 i (.inl ⟨RearTrace.predecessor i,W _,RearTrace.right_predecessor i⟩)⟩
  obtain ⟨q₁,A⟩ := advance x qx u U 0 (by decide) (by intro i; simp)
  obtain ⟨q₂,B⟩ := advance _ q₁ v V 1 (by decide) A
  obtain ⟨q₃,C⟩ := advance _ q₂ w W 2 (by decide) B
  refine ⟨q₃,fun i=>⟨?_,short_successor_word h sep Q closed same _ q₂ w i (.inl (W i))⟩⟩
  have L := C i
  have bound : off (rawRun (rawRun (rawRun x u) v) w i)≤3 := by
    unfold off
    have Z := ((ShortGeo.mis.off.read (rawRun (rawRun (rawRun x u) v) w i).mis1)).isLt
    omega
  exact (Nat.min_eq_right bound).symm.trans L

/-- In the actual MIS1 wire decoder, saturated offsets remove every
spurious body-site admission gate. Header K1 is the only gate. -/
theorem short_mis_gate_exact {s n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (x : Raw s n) (same : ∀ i,header (x i)=h i)
    (C : ∀ i,off (x i)=min 3 (ordinal h hh i)) (i : Fin n) (j : Fin 3) :
    MISByteCodec.atGate (header (x i)) (x i).mis1 j=true ↔ j.val=1 ∧ h i=true := by
  have E : MISByteCodec.get (x i).mis1 94 2 (by decide)=off (x i) := rfl
  have nonzero (A : h i=false) : off (x i)≠0 := by
    rw [C i]
    have B : ordinal h hh i ≠ 0 := fun B => Bool.noConfusion (A.symm.trans ((ordinal_zero h hh i).mp B))
    omega
  cases H : h i with
  | false =>
    rw [same i,H]
    simp only [MISByteCodec.atGate,MISByteCodec.off,Bool.false_eq_true,if_false,E]
    simp [nonzero H]
  | true =>
    rw [same i,H]
    simp [MISByteCodec.atGate,MISByteCodec.off]

end L4.PhysicalCustody
