import Leader.L4.BStarNeedTailService
import Leader.L4.BStarPhysicalPhase

namespace L4.Height.FreshNeedPrefixBand
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongLayout BStarLongDoor
open BStarLongWork BStarLongToken BStarLongCommand BStarH6WordChart BStarAcquireVisitOrder
open BStarSeparatingRail BStarOwnerLaunchOrigin BStarGeneratedOwner BStarGeneratedTapeCuts BStarNeedTrace
open BStarGrantWriterHistory BStarLongEvents BStarNeedTailService
open BStarLongFixedRouting BStarSealHealthyHop BStarLongPublication BStarNeedServicePlan
open BStarClearanceOffset BStarH6Ordinal BStarAcquireAnchors BStarAcquireRailCoverage
open BStarStageCandidateWrite BStarResetChartTouch
open BStarAcquireLiteralChain BStarLongLiteral BStarBitParity

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

private theorem foreign (x : X) (i e : Fin n) (h : oldH6 B x i=true)
    (away : rightNeighbor e≠i) : pc (step x e) i=pc x i := by
  by_cases E : i=e
  · subst i
    let pair := (x e,x (rightNeighbor e))
    have h' : (oldHeaders B pair.1).h6=true := h
    have t := BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair h'
    unfold BStarGeneratedBandScan.pc
    simp only [AllSizeS1Geometry.step,if_true]
    exact congrArg (fun y : BitVec 2 × BitVec 9 => y.2.toNat) t
  · unfold BStarGeneratedBandScan.pc
    simp only [AllSizeS1Geometry.step,if_neg E,if_neg (Ne.symm away)]

private theorem busy_pc {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {w : List (Fin n)} {a b : Cursor} (T : BusyOnly hp base addr len op x a w b)
    (u v : List (Fin n)) (W : w=u++v) : pc (play x u) (addr 0).1=op := by
  subst w
  induction u generalizing x a with
  | nil =>
    exact (at_start hp (busy_generated hp T)).1.2.2.2
  | cons e u ih =>
    cases T with
    | cons _ _ R => exact ih R

private theorem idle_pc {x : X} (i : Fin n) {w : List (Fin n)}
    (heads : ∀ u v : List (Fin n), w=u++v → oldH6 B (play x u) i=true)
    (away : ∀ e∈w,rightNeighbor e≠i) :
    ∀ u v : List (Fin n), w=u++v → pc (play x u) i=pc x i := by
  intro u v W
  subst w
  induction u generalizing x with
  | nil => rfl
  | cons e u ih =>
    have H := heads [] (e::(u++v)) rfl
    have A := away e (List.mem_cons_self)
    have R := ih (x:=step x e)
      (fun l s eq => heads (e::l) s (congrArg (List.cons e) eq))
      (fun f mem => away f (List.mem_cons_of_mem _ mem))
    exact R.trans (foreign hp x i e H A)

theorem launch_pc {x : X} {addr : Nat→Pos n} {len op : Nat} {e : Fin n}
    (E : Event hp addr len x e .idle (.busy op (.out 0))) :
    pc x (addr 0).1=op := by
  cases E with
  | launch _ _ =>
    rfl

theorem prefix_append {x : X} {u v : List (Fin n)} {P : X → Prop}
    (U : ∀ a, a<+:u → P (play x a))
    (V : ∀ a, a<+:v → P (play (play x u) a)) :
    ∀ a, a<+:u++v → P (play x a) := by
  intro a H
  have L : u<+:u++v := ⟨v,rfl⟩
  by_cases le : a.length≤u.length
  · exact U a (List.prefix_of_prefix_length_le H L le)
  · obtain ⟨b,rfl⟩ := List.prefix_of_prefix_length_le L H (by omega)
    obtain ⟨t,T⟩ := H
    rw [List.append_assoc] at T
    have bv : b<+:v := ⟨t,List.append_cancel_left T⟩
    rw [BStarResetSchedule.run_append]
    exact V b bv

theorem before_busy {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {w : List (Fin n)} {a b : Cursor} (T : BusyOnly hp base addr len op x a w b)
    (N : op≠2) : ∀ u, u<+:w → pc (play x u) (addr 0).1≠2 := by
  intro u H
  obtain ⟨v,rfl⟩ := H
  rw [busy_pc hp T u v rfl]
  exact N

theorem before_idle {x : X} {i : Fin n} {w : List (Fin n)}
    (heads : ∀ u, u<+:w → oldH6 B (play x u) i=true)
    (away : ∀ e∈w,rightNeighbor e≠i)
    (N : pc (play x w) i≠2) : ∀ u, u<+:w → pc (play x u) i≠2 := by
  have K := idle_pc hp i (w:=w) (fun l s eq => heads l ⟨s,eq.symm⟩) away
  intro u H
  obtain ⟨v,E⟩ := H
  rw [K u v E.symm,←K w [] (List.append_nil w).symm]
  exact N

theorem prefix_cons {x : X} {e : Fin n} {w : List (Fin n)} {P : X → Prop}
    (I : P x) (V : ∀ a, a<+:w → P (play (step x e) a)) :
    ∀ a, a<+:e::w → P (play x a) := by
  intro a H
  cases a with
  | nil => exact I
  | cons d a =>
    obtain ⟨l,L⟩ := H
    obtain ⟨rfl,A⟩ := List.cons.inj L
    exact V a ⟨l,A⟩

/-- Every prefix cut in the actual matched NEED itinerary, up to its first
center COMMIT mark, has source PC distinct from RESET2. -/
theorem no_pc_two {base x : X} {addr : Nat→Pos n} {len k : Nat}
    {w : List (Fin n)} (M : Matched hp base addr len k x w)
    (head : ∀ u, u<+:w → oldH6 B (play x u) (addr 0).1=true) :
    ∀ u, u<+:w → pc (play x u) (addr 0).1≠2 := by
  obtain ⟨sf,w1,bf,w2,cf,rfl,H⟩ := M
  let door := RearTrace.predecessor (addr 0).1
  let P : X → Prop := fun y => pc y (addr 0).1≠2
  change ∀ u, u<+:sf++door::(w1++door::(bf++door::(w2++door::cf))) →
    P (play x u)
  have A := before_busy hp H.sealFlight (by decide)
  have D := before_busy hp H.bitFlight (by decide)
  have F := before_busy hp H.commitFlight (by decide)
  have H₁ : ∀ u, u<+:w1 → oldH6 B (play (step (play x sf) door) u) (addr 0).1=true := by
    intro u U
    obtain ⟨v,V⟩ := U
    have pre : (sf++door::u)<+:tailWord door sf w1 bf w2 cf := by
      refine ⟨v++door::(bf++door::(w2++door::cf)),?_⟩
      simp [tailWord,←V,List.append_assoc]
    simpa only [BStarResetSchedule.run_append,BStarResetSchedule.run] using head (sf++door::u) pre
  let z := step (play (step (play (step (play x sf) door) w1) door) bf) door
  have H₂ : ∀ u, u<+:w2 → oldH6 B (play z u) (addr 0).1=true := by
    intro u U
    obtain ⟨v,V⟩ := U
    have pre : (sf++door::(w1++door::(bf++door::u)))<+:tailWord door sf w1 bf w2 cf := by
      refine ⟨v++door::cf,?_⟩
      simp [tailWord,←V,List.append_assoc]
    simpa only [z, BStarResetSchedule.run_append,BStarResetSchedule.run] using head (sf++door::(w1++door::(bf++door::u))) pre
  have C₁ := before_idle hp (i:=(addr 0).1) H₁ H.beforeBitOff
    (by rw [launch_pc hp H.bitIssue]; decide)
  have C₂ := before_idle hp (i:=(addr 0).1) H₂ H.beforeCommitOff
    (by rw [launch_pc hp H.commitIssue]; decide)
  exact prefix_append hp (P:=P) A
    (prefix_cons hp (A sf ⟨[],List.append_nil sf⟩)
      (prefix_append hp C₁ (prefix_cons hp (C₁ w1 ⟨[],List.append_nil w1⟩)
        (prefix_append hp D (prefix_cons hp (D bf ⟨[],List.append_nil bf⟩)
          (prefix_append hp C₂ (prefix_cons hp (C₂ w2 ⟨[],List.append_nil w2⟩) F)))))))

/-- Truncate a certified continuation at the original publication-free tape.
The appended marks serve only to complete the deterministic witness; no
assumption is made that the original tape contains the service word. -/
theorem no_pc_two_on_miss {base x : X} {addr : Nat→Pos n} {len k : Nat}
    (i : Fin n) (w service : List (Fin n))
    (miss : ∀ pre post, w=pre++i::post →
      NoPublication hp (play x pre) i i)
    (replay : ∃ pre tail, w++service=pre++i::tail ∧
      Matched hp base addr len k x pre ∧ ¬NoPublication hp (play x pre) i i)
    (head : ∀ u, u<+:w++service → oldH6 B (play x u) (addr 0).1=true) :
    ∀ u, u<+:w → pc (play x u) (addr 0).1≠2 := by
  obtain ⟨pre,tail,E,M,pub⟩ := replay
  have before : BeforePublication hp x i w := by
    intro a e b H
    apply Classical.byContradiction
    intro N
    have Q := BStarNeedPrefix.publication_is_outgoing hp (play x a) e i N
    subst e
    exact N (miss a b H)
  have W := BStarNeedPrefix.prefix_before_first_publish hp x i w service pre tail E pub before
  have P : pre<+:w++service := ⟨i::tail,E.symm⟩
  exact fun u U => no_pc_two hp M (fun a A => head a (A.trans P)) u (U.trans W)

/-- A healthy accepted NEED SEAL cannot be followed by RESET2 on a
publication-free raw suffix. No service subsequence is assumed in that suffix. -/
theorem accepted_need_seal_on_miss {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len)
    (gateIdx : S.getD g fall=(bSite,1)) (ord : oldOrdinal B base hh bSite=4)
    (lead : List (Fin n))
    (history : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy sealOp (.out k)))
    (pay : Payload) (well : Well pay) (d : Descriptor) (need : d.need=true)
    (oldFacts : let x := play origin lead
      Q x ∧ correct (oldH6 B base) hh 5 x ∧ BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false ∧
      BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (x i).long d=true ∧ readOptional (stage.read (x i).long)=some d ∧
      (centerLink (oldPair B x i),.advance pay)∈actualOffers (oldPair B x i)
        ((x i).long,(x (rightNeighbor i)).long))
    (ch : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (ct : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true) 
    (w : List (Fin n))
    (miss : ∀ pre post, w=pre++i::post →
      NoPublication hp (play (step (play origin lead) i) pre) i i) :
    ∀ u, u<+:w → pc (play (step (play origin lead) i) u) (S.getD 0 fall).1≠2 := by
  let x := step (play origin lead) i
  obtain ⟨P⟩ := plan_exists hp C ch ct k g K G.2
  let labels := service hp P i bSite
  have sub : labels.Sublist (w++labels) :=
    List.sublist_append_of_sublist_right (List.Sublist.refl labels)
  obtain ⟨pre,tail,gate,s,E,U,R,before,M,trace⟩ := need_tail_sealed_trace hp C Q fiber
    closed sep i k K idx head own bSite g G gateIdx ord lead history pay well d need oldFacts P
    (w++labels) sub
  have pub : ¬NoPublication hp (play x pre) i i := by
    intro N
    dsimp at trace
    exact N .left rfl ⟨.left,candidate d (BStarBitParity.firstBit s)⟩
      (by rw [trace.2.1]; exact List.mem_cons_self) rfl
  have hX : Q x := closed _ oldFacts.1 i
  have heads (u : List (Fin n)) (_ : u<+:w++labels) :
      oldH6 B (play x u) (S.getD 0 fall).1=true :=
    (root_cuts hp C Q hX (fun y e Y => closed y Y e) fiber u).1
  change ∀ u, u<+:w → pc (play x u) (S.getD 0 fall).1≠2
  exact no_pc_two_on_miss hp (base:=base) (addr:=fun j=>S.getD j fall) (len:=len) (k:=k)
    (x:=x) i w labels miss ⟨pre,tail,E,M,pub⟩ heads

end L4.Height.FreshNeedPrefixBand
