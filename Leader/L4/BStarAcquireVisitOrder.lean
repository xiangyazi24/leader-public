import Leader.L4.BStarCommandChronology

namespace L4.BStarAcquireVisitOrder
open AllSizeProtocol BStarLongClaims BStarH6WordChart BStarCommandChronology

abbrev Pos (n : Nat) := Fin n × Fin 11

def Edge {a : LargeParams} {n : Nat} (b : LargeRows a) (x : Fin n → LargeSite a)
    (u v : Pos n) : Prop :=
  ∃ i c d, c ∈ orderedCommands (oldPair b x i) ∧ c.destination=some d ∧
    u=(site i c.source.side,c.source.occurrence) ∧ v=(site i d.side,d.occurrence)

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

/-- Any entering link into K1 or K2 from the preceding occurrence
lands at the responder of its old H6 seam, not a body slot. -/
theorem enter_header {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {u v : Pos n}
    (E : Edge b x u v) (h : u.2.val < v.2.val) (hk : v.2.val ≤ 2) :
    oldH6 b x v.1 = true := by
  obtain ⟨i,c,d,hc,hd,rfl,rfl⟩ := E
  let good (H : Bool) (C : CommandClaim) : Bool :=
    match C.destination with
    | none => true
    | some D => if C.source.occurrence.val < D.occurrence.val ∧ D.occurrence.val ≤ 2
      then H && (D.side == .right) else true
  let g := oldPair b x i
  have F (I L H J : Bool) :
      (commandClaims (geo false I L, geo H J false)).all (good H) = true := by
    cases I <;> cases L <;> cases H <;> cases J <;> decide +kernel
  have raw := BStarLongFenceTopology.selected_command_raw g c hc
  have R : commandClaims g =
      commandClaims (geo false g.1.inside g.1.last, geo g.2.axes.h6 g.2.inside false) := rfl
  rw [R] at raw
  have H := List.all_eq_true.mp (F g.1.inside g.1.last g.2.axes.h6 g.2.inside) c raw
  have J : good (oldH6 b x (rightNeighbor i)) c = true := H
  simp only [good,hd,if_pos (And.intro h hk),Bool.and_eq_true,beq_iff_eq] at J
  simpa only [J.2, site] using J.1

/-- Destination indices of actual links are monotone with no jumps. -/
theorem index_step {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {u v : Pos n} (E : Edge b x u v) :
    u.2.val ≤ v.2.val ∧ v.2.val ≤ u.2.val+1 := by
  obtain ⟨i,c,d,hc,hd,rfl,rfl⟩ := E
  dsimp only
  rw [actual_occurrence_next b x i c d hc hd]
  split <;> omega

/-- A structural path records only actual departure positions; the
final slot is deliberately omitted. -/
inductive Path {a : LargeParams} {n : Nat} (b : LargeRows a) (x : Fin n → LargeSite a) :
    Pos n → List (Pos n) → Pos n → Prop where
  | nil (u) : Path b x u [] u
  | cons {u v z L} : Edge b x u v → Path b x v L z → Path b x u (u::L) z

private theorem crossing {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {u z : Pos n} {L : List (Pos n)} (P : Path b x u L z)
    {k : Nat} (hu : u.2.val < k) (hz : k < z.2.val) (hk : k ≤ 2) :
    ∃ v ∈ L, v.2.val=k ∧ oldH6 b x v.1=true := by
  induction P with
  | nil => omega
  | @cons u v z L E P ih =>
    have B := index_step E
    by_cases T : v.2.val=k
    · have H := enter_header E (by omega) (by omega)
      cases P with
      | nil => omega
      | cons E' P' => exact ⟨v,by simp,T,H⟩
    · obtain ⟨s,hs,H⟩ := ih (by omega) hz
      exact ⟨s,List.mem_cons_of_mem _ hs,H⟩

/-- A K0-header to K10 trajectory departs from a header at each of
K0, K1 and K2, in addition to reaching its endpoint. -/
theorem departures {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {u z : Pos n} {L : List (Pos n)} (P : Path b x u L z)
    (hu : u.2.val=0) (huH : oldH6 b x u.1=true) (hz : z.2.val=10) :
    (∀ k, k≤2 → ∃ v ∈ L, v.2.val=k ∧ oldH6 b x v.1=true) := by
  intro k hk
  by_cases T : k=0
  · cases P with
    | nil => omega
    | cons E P => exact ⟨u,by simp,by omega,huH⟩
  · exact crossing P (by omega) (by omega) hk

private theorem edge_rank {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} (hh : ∃ j, oldH6 b x j=true)
    {u v : Pos n} (E : Edge b x u v) :
    rank (oldH6 b x) hh u.1 u.2 < rank (oldH6 b x) hh v.1 v.2 := by
  obtain ⟨i,c,d,hc,hd,rfl,rfl⟩ := E
  exact (actual_link b x hh i c d hc hd).1

/-- The actual departure word is strictly increasing in physical rank. -/
theorem departure_order {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} (hh : ∃ j, oldH6 b x j=true)
    {u z : Pos n} {L : List (Pos n)} (P : Path b x u L z) :
    L.Pairwise (fun s t => rank (oldH6 b x) hh s.1 s.2 < rank (oldH6 b x) hh t.1 t.2) := by
  let R (v : Pos n) := rank (oldH6 b x) hh v.1 v.2
  have mono {s t : Pos n} {W : List (Pos n)} (Q : Path b x s W t) :
      ∀ v ∈ W, R s ≤ R v := by
    induction Q with
    | nil => simp
    | cons E Q ih =>
      intro v hv
      rcases List.mem_cons.mp hv with rfl|hm
      · exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_of_lt (edge_rank hh E)) (ih v hm)
  induction P with
  | nil => exact .nil
  | cons E P ih =>
    exact .cons (fun v hv => Nat.lt_of_lt_of_le (edge_rank hh E) (mono P v hv)) ih

private theorem header_rank {n : Nat} (h : Fin n → Bool) (hh : ∃ j, h j=true)
    (v : Pos n) (hv : h v.1=true) (hk : v.2.val≤2) :
    rank h hh v.1 v.2 = v.2.val*n := by
  simp [rank, forward, hk, (BStarH6Ordinal.ordinal_zero h hh v.1).mpr hv]

/-- Counting the list positions (not merely distinct vertices), a
K0-header to K10 structural path has exactly one departure from a
header at each of K0, K1 and K2. -/
theorem departures_once {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {u z : Pos n} {L : List (Pos n)} (P : Path b x u L z)
    (hu : u.2.val=0) (huH : oldH6 b x u.1=true) (hz : z.2.val=10)
    (k : Nat) (hk : k≤2) :
    (L.filter (fun v => v.2.val == k && oldH6 b x v.1)).length = 1 := by
  let hh : ∃ j, oldH6 b x j=true := ⟨u.1,huH⟩
  let p (v : Pos n) := v.2.val == k && oldH6 b x v.1
  let R (v : Pos n) := rank (oldH6 b x) hh v.1 v.2
  have H (v : Pos n) (h : p v = true) : R v = k*n := by
    have C : v.2.val=k ∧ oldH6 b x v.1=true := by simpa [p] using h
    change rank (oldH6 b x) hh v.1 v.2 = k*n
    rw [header_rank _ hh v C.2 (by omega), C.1]
  have NN : ∀ {W : List (Pos n)}, W.Pairwise (fun s t => R s<R t) →
      (W.filter p).length ≤ 1 := by
    intro W D
    induction D with
    | nil => simp
    | @cons v W F D ih =>
      by_cases hp : p v=true
      · have z : W.filter p = [] := by
          cases T : W.filter p with
          | nil => rfl
          | cons w ws =>
            have hw : w ∈ W.filter p := by simp [T]
            obtain ⟨hm,hp'⟩ := List.mem_filter.mp hw
            have E := F w hm
            rw [H v hp,H w hp'] at E
            omega
        simp [hp,z]
      · simpa [List.filter_cons,hp] using ih
  obtain ⟨v,hv,he,hH⟩ := departures P hu huH hz k hk
  have hm : v ∈ L.filter p := List.mem_filter.mpr ⟨hv, by simp [p,he,hH]⟩
  have hpos := List.length_pos_of_mem hm
  have hle := NN (departure_order hh P)
  exact Nat.le_antisymm hle hpos

end L4.BStarAcquireVisitOrder
