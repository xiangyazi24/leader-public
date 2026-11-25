import Leader.L4.ReportPulseWinsSkeleton
import Leader.L4.ReportPulseDoubleWarm
namespace L4.ReportPulseDisjoint
open ReportPulseRecode ReportPulseRounds ReportPulseWinsSkeleton
universe u
variable {G : Type u}

def Good (a : Scan) : Prop :=
  (a.rounds.map Prod.fst).Nodup ∧ (∀ k∈a.rounds.map Prod.fst,k<a.next) ∧
    ∀ k, a.waiting=some k → k<a.next ∧ ∀ j∈a.rounds.map Prod.fst, j<k

theorem good_bump (a : Scan) (H : Good a) :
    Good {a with next:=a.next+1} :=
  ⟨H.1,fun k K=>Nat.lt_succ_of_lt (H.2.1 k K),
    fun k E=>⟨Nat.lt_succ_of_lt (H.2.2 k E).1,(H.2.2 k E).2⟩⟩

variable [DecidableEq G]

theorem good_step (g : G) (a : Scan) (e : Option (Event G)) (H : Good a) :
    Good (a.step g e) := by
  cases e with
  | none => exact good_bump a H
  | some t =>
    cases t with
    | start h =>
      by_cases E : h=g
      · simp only [Scan.step,if_pos E]
        exact ⟨H.1,fun k K=>Nat.lt_succ_of_lt (H.2.1 k K),fun k K=>by
          have L := Option.some.inj K
          subst k
          exact ⟨Nat.lt_succ_self _,H.2.1⟩⟩
      · simpa only [Scan.step,if_neg E] using good_bump a H
    | complete h =>
      by_cases E : h=g
      · simp only [Scan.step,if_pos E]
        cases W : a.waiting with
        | none => simpa only [W] using good_bump a H
        | some k =>
          have B := H.2.2 k W
          unfold Good
          simp only [List.map_append,List.map_cons,List.map_nil]
          refine ⟨List.nodup_append.mpr ⟨H.1,by simp,?_⟩,?_,?_⟩
          · intro i I j J
            have L : j=k := List.mem_singleton.mp J
            subst j
            exact Nat.ne_of_lt (B.2 i I)
          · intro i I
            rcases List.mem_append.mp I with L|L
            · exact Nat.lt_succ_of_lt (H.2.1 i L)
            · rw [List.mem_singleton.mp L]
              exact Nat.lt_succ_of_lt B.1
          · intro i Eq
            contradiction
      · simpa only [Scan.step,if_neg E] using good_bump a H

theorem good_scan (g : G) (a : Scan) (w : List (Option (Event G))) (H : Good a) :
    Good (scan g a w) := by
  induction w generalizing a with
  | nil => exact H
  | cons e w IH => exact IH _ (good_step g a e H)

theorem extract_nodup_starts (g : G) (J : Nat) (w : List (Option (Event G))) :
    ((extract g J w).map Prod.fst).Nodup := by
  have A : Good (⟨0,none,[]⟩ : Scan) := by simp [Good]
  have H := (good_scan g _ w A).1
  unfold extract
  dsimp only
  rw [List.map_drop]
  exact List.Nodup.sublist (List.drop_sublist _ _) H

variable {n : Nat}

noncomputable def recoded (put : G × Bool → Fin n) (s : Phase G) (w : List (Fin n)) :
    List (Option (Event G)) :=
  skeleton (armed s) ((encodeFin put s w).map (readLabel put))

noncomputable def starts (put : G × Bool → Fin n) (g : G) (J : Nat)
    (s : Phase G) (w : List (Fin n)) : List Nat :=
  (extract g J (recoded put s w)).map Prod.fst

theorem starts_nodup (put : G × Bool → Fin n) (g : G) (J : Nat)
    (s : Phase G) (w : List (Fin n)) : (starts put g J s w).Nodup :=
  extract_nodup_starts g J _

theorem pair_start_global (put : G × Bool → Fin n) (inj : Function.Injective put)
    (g : G) (s : Phase G) (u v : List (Fin n)) (pair : Nat × Nat)
    (H : PairAt g u.length (physicalEvents (physicalRun s (u.map (readLabel put)))
      (v.map (readLabel put))) pair) :
    u.length≤pair.1 ∧ pair.1<(u++v).length ∧
      (recoded put s (u++v))[pair.1]?=some (some (.start g)) := by
  obtain ⟨j,k,E,J,K,Start,_⟩ := H
  have Length := events_length (physicalRun s (u.map (readLabel put))) (v.map (readLabel put))
  rw [List.length_map] at Length
  rw [E]
  refine ⟨Nat.le_add_right _ _,by simp only [List.length_append]; omega,?_⟩
  unfold recoded
  rw [skeleton_encodeFin put inj,List.map_append,events_append]
  have L : (physicalEvents s (u.map (readLabel put))).length=u.length :=
    (events_length s _).trans (List.length_map (readLabel put))
  rw [List.getElem?_append_right (by rw [L]; omega),L,show u.length+j-u.length=j by omega]
  exact Start

theorem recoded_prefix (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Phase G) (u v : List (Fin n)) :
    (recoded put s (u++v)).take u.length=recoded put s u :=
  skeleton_prefixFin put inj s u v

theorem prefix_tag_lift (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Phase G) (u v : List (Fin n)) (j : Nat) (J : j<u.length)
    (g : G) (H : (recoded put s u)[j]?=some (some (.start g))) :
    (recoded put s (u++v))[j]?=some (some (.start g)) := by
  rw [←recoded_prefix put inj s u v,List.getElem?_take,if_pos J] at H
  exact H

/-- Distinct gates' extracted starts may be in the same physical prefix,
but cannot share an index: a skeleton cell has one event tag only. -/
theorem distinct_gate_starts (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Phase G) (left right : G) (D : left≠right)
    (u v : List (Fin n)) (L R : List Nat)
    (A : ∀ j∈L,j<u.length ∧ (recoded put s u)[j]?=some (some (.start left)))
    (B : ∀ j∈R,(recoded put s (u++v))[j]?=some (some (.start right))) :
    ∀ j∈L,j∉R := by
  intro j M N
  have P := A j M
  have Q := prefix_tag_lift put inj s u v j P.1 left P.2
  rw [B j N] at Q
  exact D (ReportPulseRecode.Event.start.inj ((Option.some.inj (Option.some.inj Q)).symm))

/-- Same gate, second award is rebased behind the first actual paint.
This is the positional separation consumed by the joint count. -/
theorem ordered_starts (q : Nat) (L R : List Nat)
    (left : ∀ j∈L,j<q) (right : ∀ j∈R,q≤j) :
    ∀ j∈L,j∉R := by
  intro j A B
  exact (Nat.not_lt_of_ge (right j B)) (left j A)

open AllSizeProtocol ReportByteRows ReportPulseRaw ReportPulseWarmup

theorem raw_credit_start_tags {X : Type}
    (put : G × Bool → Fin n) (inj : Function.Injective put) (g : G)
    {raw : X → Fin n → X} {Q : X → Prop} {p : Params} {bytes : X → BitVec p.w}
    (Wire : Wire raw (put (g,true)) Q p bytes)
    (Adj : rightNeighbor (put (g,false))=put (g,true)) (J : 0<p.streak)
    (base : X) (Good : Q base) (s : Phase G)
    (Initial : s g=phaseOf (readClock p bytes base).phase)
    (w : List (Fin n))
    (C : Credit (put (g,false)) (put (g,true)) p.streak (cleanAt raw p bytes base) w) :
    ∀ j∈starts put g p.streak s w,
      j<w.length ∧ (recoded put s w)[j]?=some (some (.start g)) := by
  obtain ⟨u,v,E,_,P⟩ := raw_credit_extract put inj g Wire Adj J base Good s Initial w C
  subst w
  intro j M
  obtain ⟨pair,H,rfl⟩ := List.mem_map.mp M
  exact (pair_start_global put inj g s u v pair (P pair H)).2

theorem same_gate_disjoint_actual {X : Type}
    (put : G × Bool → Fin n) (inj : Function.Injective put) (g : G)
    {raw : X → Fin n → X} {Q : X → Prop} {p : Params} {bytes : X → BitVec p.w}
    (Wire : Wire raw (put (g,true)) Q p bytes)
    (Adj : rightNeighbor (put (g,false))=put (g,true)) (J : 0<p.streak)
    (base : X) (Good : Q base) (Clean0 : Clean (readClock p bytes base))
    (s : Phase G) (Initial : s g=phaseOf (readClock p bytes base).phase)
    (u v : List (Fin n)) (e f : Fin n)
    (C₁ : countedPaint (put (g,true)) p bytes (u.foldl raw base) e=true)
    (C₂ : countedPaint (put (g,true)) p bytes (v.foldl raw (raw (u.foldl raw base) e)) f=true) :
    let L := starts put g p.streak s (u++[e])
    let R := starts put g p.streak s ((u++[e])++(v++[f]))
    ∀ j∈L,j∉R := by
  have Distinct : put (g,false)≠put (g,true) := by
    intro H
    have E := congrArg Prod.snd (inj H)
    contradiction
  obtain ⟨First,Second⟩ := ReportPulseDoubleWarm.same_gate_two_credits Wire (put (g,false))
    Adj Distinct J base Good Clean0 u v e f C₁ C₂
  have FirstBound := raw_credit_start_tags put inj g Wire Adj J base Good s Initial _ First
  obtain ⟨lead,wins,E,C,Win⟩ := Second
  let cut := (u++[e])++lead
  have Cut : cleanAt raw p bytes base cut := by
    unfold cleanAt cut
    rw [List.foldl_append,List.foldl_append]
    exact C
  have Empty := raw_clean_empty put inj g Wire Adj J base Good s Initial cut Cut
  have Last := wins_extract put inj g s cut wins p.streak Empty Win
  have Eq : ((u++[e])++(v++[f]))=cut++wins := by rw [E]; simp [cut,List.append_assoc]
  have Right : ∀ j∈starts put g p.streak s ((u++[e])++(v++[f])), (u++[e]).length≤j := by
    intro j Mem
    rw [Eq] at Mem
    obtain ⟨pair,H,rfl⟩ := List.mem_map.mp Mem
    have T := (pair_start_global put inj g s cut wins pair (Last.2 pair H)).1
    unfold cut at T
    simp only [List.length_append] at T ⊢
    omega
  exact ordered_starts (u++[e]).length _ _ (fun j M => (FirstBound j M).1) Right

end L4.ReportPulseDisjoint
