import Leader.L4.BStarNumericIssueDefined

/-! The forward numeric stop at ISSUE408. The old physical inputs
are separate from the conclusion that the PC stays in the band. -/
namespace L4.BStarForwardNumericBand
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongDoor BStarLongLayout
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarResetMarkAdapter BStarGeneratedOwner BStarGeneratedTapeCuts BStarSeparatingRail
open BStarResetChartService BStarFreshNumericTrace BStarFreshNumeric BStarGeneratedBandScan

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

def Live (addr : Nat→Pos n) (x : X) (m : Mode) : Prop :=
  (13≤pc x (addr 0).1 ∧ pc x (addr 0).1<408) ∧
    ∀ op z,m=.busy op z → HealthAt op (project addr x) z

def Issue408 (addr : Nat→Pos n) (x : X) (m : Mode) : Prop :=
  m=.idle ∧ pc x (addr 0).1=408

private theorem foreign_pc (x : X) (i e : Fin n)
    (h : oldH6 B x i=true) (away : e≠RearTrace.predecessor i) :
    pc (step x e) i=pc x i := by
  have R : rightNeighbor e≠i := fun E =>
    away ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor E))
  by_cases E : i=e
  · subst i
    let pair := (x e,x (rightNeighbor e))
    have h' : (oldHeaders B pair.1).h6=true := h
    have t := BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair h'
    unfold BStarGeneratedBandScan.pc
    simp only [AllSizeS1Geometry.step,if_true]
    exact congrArg (fun y : BitVec 2 × BitVec 9 => y.2.toNat) t
  · unfold BStarGeneratedBandScan.pc
    simp only [AllSizeS1Geometry.step,if_neg E,if_neg (Ne.symm R)]

/-- Before the first ISSUE408, every literal generated mark either
keeps a healthy numeric mode or is the real 407→408 consume. -/
theorem one_mark {base x : X} {hh : ∃ b,oldH6 B base b=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (e : Fin n) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {a b : Mode} (head : oldH6 B x (S.getD 0 fall).1=true)
    (I : Current hp base (fun j=>S.getD j fall) len x a)
    (J : Current hp base (fun j=>S.getD j fall) len (step x e) b)
    (E : Event hp (fun j=>S.getD j fall) len x e a b)
    (L : Live (fun j=>S.getD j fall) x a)
    (center : ((capturedSelector 1).read (x (S.getD 0 fall).1).long).toNat<3)
    (data : ∀ k≤len,(S.getD k fall).2.val=1 →
      (longGeometry B (x (S.getD k fall).1)).inside=true → operands (x (S.getD k fall).1).long) :
    Live (fun j=>S.getD j fall) (step x e) b ∨ Issue408 (fun j=>S.getD j fall) (step x e) b := by
  let adr := fun j=>S.getD j fall
  let root := (adr 0).1
  have band : 13≤pc x root ∧ pc x root<408 := L.1
  cases E with
  | idle_hold away =>
    have eq := foreign_pc hp x root e head away
    exact .inl ⟨(show 13≤pc (step x e) root ∧ pc (step x e) root<408 from eq.symm ▸ band),fun _ _ bad=>by cases bad⟩
  | bad_issue own bad =>
    have H := BStarNumericIssueDefined.initial_defined (x root).long (pc x root) band.1 band.2 center
    change initial (pc x root) (x root).long=none at bad
    rw [bad] at H
    cases H
  | launch own launch =>
    have eq : pc (step x e) root=pc x root :=
      congrArg (fun t : _ × BitVec 9=>t.2.toNat) launch.2.choose_spec.2
    refine .inl ⟨(show 13≤pc (step x e) root ∧ pc (step x e) root<408 from eq.symm ▸ band),?_⟩
    intro op z eqMode
    cases eqMode
    obtain ⟨f,F,V,O⟩ := BStarFreshNumericLaunch.source_health launch band.1 band.2
    have K := (root_header hp C J.1.1).2
    refine ⟨f,?_,V,congrArg BitVec.toNat O⟩
    change atSite (step x e root).long (adr 0).2=.forward f
    rw [K]
    exact F
  | transit op z d go M =>
    have eq : pc (step x e) root=pc x root := J.1.2.2.2.trans I.1.2.2.2.symm
    refine .inl ⟨(show 13≤pc (step x e) root ∧ pc (step x e) root<408 from eq.symm ▸ band),?_⟩
    intro op' z' eqMode
    cases eqMode
    cases M with
    | cons _ _ A _ rest =>
      cases rest
      exact mark_health hp C e (sep e) op I.1 z d A I.2.1 J.2.1 (L.2 op z rfl)
        (fun k K => data k (by have H := I.2.1; rw [K] at H; exact H.1)) (fun Z=>False.elim (go Z))
  | arrived_hold op away =>
    have eq := foreign_pc hp x root e head away
    refine .inl ⟨(show 13≤pc (step x e) root ∧ pc (step x e) root<408 from eq.symm ▸ band),?_⟩
    intro op' z' eqMode
    cases eqMode
    exact mark_health hp C e (sep e) op I.1 (.back 0) (.back 0) (.stay _)
      I.2.1 J.2.1 (L.2 op (.back 0) rfl) (by intro k K; cases K) (fun _=>away)
  | consume op own clear =>
    have pcEq : pc x root=op := I.1.2.2.2
    have inc := BStarFreshNumericConsume.source_successor hp C sep op (pcEq ▸ band.1)
      (pcEq ▸ band.2) I.1 (L.2 op (.back 0) rfl) (fun _=>center)
    change BStarAcquireWaitControl.control (step x (RearTrace.predecessor root) root).long=
      (1,BitVec.ofNat 9 (op+1)) at inc
    change e=RearTrace.predecessor root at own
    rw [←own] at inc
    have fin : pc (step x e) root=op+1 := by
      have Q := congrArg (fun t : BitVec 2 × BitVec 9=>t.2.toNat) inc
      change pc (step x e) root=(BitVec.ofNat 9 (op+1)).toNat at Q
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show op+1<2^9 by omega)] using Q
    by_cases endPC : op+1=408
    · exact .inr ⟨rfl,fin.trans endPC⟩
    · exact .inl ⟨(show 13≤pc (step x e) root ∧ pc (step x e) root<408 by omega),fun _ _ bad=>by cases bad⟩

/-- Scan the real generated word up to first ISSUE408, or through
the end if the numeric band is unfinished. At a marked cut the
environment may use the lower PC bound only on strictly earlier old
marks. This supports an inductive drained-frame proof, not a circular
assumption that the PC already stays in band. -/
theorem stopped_word {base x : X} {hh : ∃ b,oldH6 B base b=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {a b : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x a w b)
    (L : Live (fun j=>S.getD j fall) x a)
    (facts : ∀ u e v,w=u++e::v →
      (∀ q f t,u=q++f::t → 11≤pc (play x q) (S.getD 0 fall).1) →
      let y := play x u
      oldH6 B y (S.getD 0 fall).1=true ∧
      ((capturedSelector 1).read (y (S.getD 0 fall).1).long).toNat<3 ∧
      (∀ k≤len,(S.getD k fall).2.val=1 →
        (longGeometry B (y (S.getD k fall).1)).inside=true → operands (y (S.getD k fall).1).long)) :
    ∃ pre post m,w=pre++post ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len x a pre m ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len (play x pre) m post b ∧
      (∀ u e v, pre=u++e::v → 13≤pc (play x u) (S.getD 0 fall).1 ∧
        pc (play x u) (S.getD 0 fall).1<408) ∧
      (Issue408 (fun j=>S.getD j fall) (play x pre) m ∨
        post=[] ∧ Live (fun j=>S.getD j fall) (play x pre) m) := by
  induction T with
  | endpoint I =>
    exact ⟨[],[],_,rfl,.endpoint I,.endpoint I, (by intro u e v H; cases u <;> cases H),
      .inr ⟨rfl,L⟩⟩
  | @next x a e w b dest I E tail ih =>
    obtain ⟨H,V,D⟩ := facts [] e w rfl (by intro u e v A; cases u <;> cases A)
    have J := at_start hp tail
    rcases one_mark hp C e sep H I J E L V D with live|hit
    · have localFacts u f v (W : w=u++f::v)
          (prior : ∀ q s t,u=q++s::t → 11≤pc (play (step x e) q) (S.getD 0 fall).1) :=
        facts (e::u) f v (congrArg (List.cons e) W) (by
          intro q s t Z
          cases q with
          | nil => have lo := L.1.1; exact Nat.le_trans (by decide : 11≤13) lo
          | cons g q =>
            obtain ⟨rfl,U⟩ := List.cons.inj Z
            exact prior q s t U)
      obtain ⟨pre,post,m,Eq,A,B',old,done⟩ := ih live localFacts
      refine ⟨e::pre,post,m,congrArg (List.cons e) Eq,.next I E A,B',?_,done⟩
      intro u f v H
      cases u with
      | nil => exact L.1
      | cons g u =>
        obtain ⟨rfl,W⟩ := List.cons.inj H
        exact old u f v W
    · refine ⟨[e],w,_,rfl,.next I E (.endpoint J),tail,?_,.inl hit⟩
      intro u f v H
      cases u with
      | nil => exact L.1
      | cons g u =>
        have W := (List.cons.inj H).2
        cases u <;> cases W

end L4.BStarForwardNumericBand
