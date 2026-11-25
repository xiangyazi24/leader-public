import Leader.L4.BStarRawReadSealOrigin

namespace L4.BStarRawReadSeparation
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarH6Ordinal BStarClearanceOffset BStarLongLiteral BStarLongPublication BStarAcquireAnchors
open BStarNeedPrefixFresh BStarGrantWriterHistory BStarFirstDoorService BStarBitControllerOrigin
open BStarCommitTailScan BStarNeedPrefix BStarNeedServicePlan BStarRawReadSealOrigin

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

theorem before_append (x : X) (i : Fin n) (u v : List (Fin n))
    (U : BeforePublication hp x i u) (V : BeforePublication hp (play x u) i v) :
    BeforePublication hp x i (u++v) := by
  intro pre e tail E
  rcases List.append_eq_append_iff.mp E with ⟨q,P,Q⟩|⟨q,P,Q⟩
  · rw [P,BStarResetSchedule.run_append]
    exact V q e tail Q
  · cases q with
    | nil =>
      simp only [List.append_nil] at P
      rw [←P]
      exact V [] e tail Q.symm
    | cons m q =>
      have Q' : e::tail=m::(q++v) := Q
      have equality := (List.cons.inj Q').1
      subst m
      exact U pre e q P

theorem before_single (x : X) (i e : Fin n) (silent : NoPublication hp x e i) :
    BeforePublication hp x i [e] := by
  intro pre a tail W
  cases pre with
  | nil =>
    have eq : e=a := (List.cons.inj (show e::[]=a::tail from W)).1
    exact eq ▸ silent
  | cons a pre =>
    have E := congrArg List.length W
    simp only [List.length_append,List.length_cons,List.length_nil] at E
    omega

/-- In a settled generated epoch with no inherited ISSUE410, two
distinct raw first observations of the same owner require a physical
publication of that owner between them. Neither read is required to
finish, and no coverage assumption is made on the input word. -/
theorem two_raw_reads_separated {base x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ j,Layout B base j=Layout B x j)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (off0 : correct (oldH6 B base) hh 5 x)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len) (gateIdx : S.getD g fall=(bSite,1))
    (ord : oldOrdinal B base hh bSite=4)
    (P : Plan hp base (fun j=>S.getD j fall) len k g)
    (prior gap : List (Fin n)) (a b : Fin n) {m : Mode}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle (prior++a::gap) m)
    (notInherited : pc x (S.getD 0 fall).1≠bitOp)
    (first : RawFirstRead (fun j=>S.getD j fall) g (play x prior) a)
    (second : RawFirstRead (fun j=>S.getD j fall) g (play x (prior++a::gap)) b) :
    ¬BeforePublication hp (play x prior) i (a::gap) := by
  intro noBetween
  obtain ⟨_,past,_⟩ := BStarGeneratedTapeCuts.split hp prior (a::gap) T
  obtain ⟨lead,remain,p,d,split,leader,pW,need,noEarlier,oldFacts⟩ :=
    matching_old_seal hp C Q fiber closed sep qx off0 coherent i k K idx head own g
      (Nat.le_of_lt G.2) prior past notInherited a first
  let next := step (play x lead) i
  have time1 : play x prior=play next remain := by
    rw [split,BStarResetSchedule.run_append]; rfl
  have time2 : play x (prior++a::gap)=play next (remain++a::gap) := by
    rw [BStarResetSchedule.run_append,time1,BStarResetSchedule.run_append]
  have same := BStarGeneratedTapeCuts.at_end hp T
  have typed := raw_read_is_owned hp C sep g (Nat.le_of_lt G.2) (prior++a::gap) b T second
  have op := BStarNeedQuietRead.first_read_mode hp same typed
  have noMode : ∀ z,m≠.busy commitOp z := by
    intro z E
    exact (by decide : bitOp≠commitOp) (Mode.busy.inj (op.symm.trans E)).1
  have silent := BStarWriterOwnerInterval.no_publication hp C sep T same b i own noMode
  have U : BeforePublication hp next i (remain++a::gap) :=
    before_append hp next i remain (a::gap) noEarlier (time1 ▸ noBetween)
  have extended := before_append hp next i (remain++a::gap) [b] U
    (before_single hp (play next (remain++a::gap)) i b (time2 ▸ silent))
  have one := unfinished_need_at_most_one hp C Q fiber closed sep i k K idx head own bSite g G gateIdx
    ord lead leader p pW d need oldFacts P ((remain++a::gap)++[b]) extended
  have firstSplit : (remain++a::gap)++[b]=remain++a::(gap++[b]) := by
    rw [List.append_assoc,List.cons_append]
  have order : remain.length<(remain++a::gap).length := by simp [List.length_append]
  exact one remain a (gap++[b]) (remain++a::gap) b [] firstSplit rfl order (time1 ▸ first) (time2 ▸ second)

#print axioms two_raw_reads_separated
end L4.BStarRawReadSeparation
