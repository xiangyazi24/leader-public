import Leader.L4.Height.StageSealStay
import Leader.L4.BStarSealWriterInterval

namespace L4.Height.StageSealFrameActual
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarLongGrant BStarGrantReaderHistory BStarLongLandingFrame BStarLongFiberOwner BStarPublicationBirth BStarGrantBirth BStarAcquireAnchors
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- From the actual post-STAGE center seed, retain matched STAGE,
selector and writer at every cut before the selected SEAL. Scope is
stated on the real generated tape; no external writer exclusion table. -/
theorem ready_at_prefix {base origin x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val)
    (k : Nat) (le : k≤len) (idx : S.getD k fall=(i,1))
    (lead w : List (Fin n)) (landed : play origin lead=x)
    (d : Descriptor) (valid : d.valid=true)
    (seed : BStarLongOutgoing.actual (x i).long d=true ∧
      conflict (ports x i)=false ∧ stage.read (x i).long=packOptional (some d))
    (scope : ∀ u e v,w=u++e::v → ∃ m,
      GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle (lead++u) m ∧
      Current hp base (fun j=>S.getD j fall) len (play x u) m ∧
      oldH6 B (play x u) i=true ∧
      (BStarSealOwnerFrame.Excluded k m ∨ BStarSealPackedFrame.RingNoLatch hp (play x u) e i) ∧
      (∀ a,m≠.busy releaseOp a)) :
    ∀ a b,w=a++b →
      BStarLongOutgoing.actual (play x a i).long d=true ∧
      readOptional (stage.read (play x a i).long)=some d ∧ conflict (ports (play x a) i)=false := by
  have old := Bool.and_eq_true_iff.mp seed.1
  have seedLive : bit x i 1≠0 := by
    intro zero
    change (grant 1).read (x i).long=0 at zero
    rw [zero] at old
    exact (by decide : ¬ (0 : BitVec 1).getLsbD 0 = true) old.1
  have writers := BStarSealWriterInterval.live_writer_word hp C sep i own lead w landed ⟨seedLive,seed.2.1⟩
    (by intro u e v W; obtain ⟨m,G,I,H,_,R⟩ := scope u e v W; exact ⟨m,G,I,H,R⟩)
  intro a b W
  have read := BStarSealPackedFrame.word_frame hp x a i sep (by
    intro u e v E
    obtain ⟨m,G,I,H,N,_⟩ := scope u e (v++b) (by rw [W,E,List.append_assoc,List.cons_append])
    have eq : play origin (lead++u)=play x u := by rw [BStarResetSchedule.run_append,landed]
    refine ⟨H,?_⟩
    rcases N with N|N
    · exact eq ▸ BStarSealOwnerFrame.no_latch hp C sep i k le idx G (eq.symm ▸ I) N e
    · exact N)
  have sel : selector.read (play x a i).long=selector.read (x i).long := congrArg Prod.fst read
  have latch : stage.read (play x a i).long=stage.read (x i).long :=
    congrArg (fun z : BitVec 2 × BitVec 8 × BitVec 8=>z.2.1) read
  have writer := writers a b W
  refine ⟨?_,?_,writer.2⟩
  · unfold BStarLongOutgoing.actual
    have S : readSel (play x a i).long=readSel (x i).long := by unfold readSel; rw [sel]
    rw [S]
    exact Bool.and_eq_true_iff.mpr ⟨BStarSealWriterInterval.live_at_end_bit writer.1,old.2⟩
  · rw [latch,seed.2.2]
    exact BStarSealWriterInterval.optional_roundtrip d valid

#print axioms ready_at_prefix

open BStarGeneratedTapeCuts BStarOwnerLaunchOrigin BStarSeparatingRail
open StageSealPhaseScope StageSealStay BStarAcquireHistoryReturn

/-- Per-mark old mode and latch scope, expressed entirely on a physical subword. -/
def LocalScope {base : X} (addr : Nat→Pos n) (len k : Nat) (i : Fin n) (x : X)
    (w : List (Fin n)) : Prop :=
  ∀ u e v,w=u++e::v → ∃ m, Current hp base addr len (play x u) m ∧
    (BStarSealOwnerFrame.Excluded k m ∨ BStarSealPackedFrame.RingNoLatch hp (play x u) e i) ∧
    (∀ a,m≠.busy releaseOp a)

theorem LocalScope.append {base : X} {addr : Nat→Pos n} {len k : Nat} {i : Fin n}
    {x : X} {w v : List (Fin n)}
    (A : LocalScope hp (base:=base) addr len k i x w)
    (D : LocalScope hp (base:=base) addr len k i (play x w) v) :
    LocalScope hp (base:=base) addr len k i x (w++v) := by
  intro pre e tail W
  rcases List.append_eq_append_iff.mp W with ⟨a,L,R⟩|⟨a,L,R⟩
  · subst pre
    rw [BStarResetSchedule.run_append]
    exact D a e tail R
  · subst w
    cases a with
    | nil =>
      obtain ⟨m,I,N,O⟩ := D [] e tail R.symm
      simp only [List.append_nil,BStarResetSchedule.run] at I N
      exact ⟨m,I,N,O⟩
    | cons f a =>
      obtain ⟨rfl,E⟩ := List.cons.inj R
      exact A pre e a rfl

theorem idle_one {base x : X} {addr : Nat→Pos n} {len k : Nat}
    {i e : Fin n} (I : Current hp base addr len x .idle) :
    LocalScope hp (base:=base) addr len k i x [e] := by
  intro u f v W
  have J := congrArg List.length W
  have L : u=[] := List.length_eq_zero_iff.mp (by simp at J; omega)
  subst u
  exact ⟨.idle,I,.inl (by intro _ _ H; cases H),by intro _ H; cases H⟩

/-- The literal three-block interval after accepted center STAGE and before
the selected SEAL center: busy STAGE/return, the actual idle foreign
segment and launch, then exact precenter busy SEAL (including holds). -/
theorem interval_scope {base x : X} {addr : Nat→Pos n} {len k : Nat} {i ack door : Fin n}
    (K : k<len) (loc : addr k=(i,1)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a mid b : List (Fin n))
    (A : BusyOnly hp base addr len stageOp x (.out (k+1)) a (.back 0))
    (Idle : GeneratedOwner hp base addr len (step (play x a) ack) .idle (mid++[door]) (.busy sealOp (.out 0)))
    (foreign : ∀ e∈mid,e≠RearTrace.predecessor (addr 0).1)
    (F : BusyOnly hp base addr len sealOp (step (play (step (play x a) ack) mid) door) (.out 0) b (.out k)) :
    LocalScope hp (base:=base) addr len k i x (a++ack::(mid++door::b)) := by
  have first : LocalScope hp (base:=base) addr len k i x (a++[ack]) := by
    apply LocalScope.append hp
    · intro u e v W
      obtain ⟨m,I,N,R⟩ := post_stage_scope hp K A u e v W
      exact ⟨m,I,.inl N,R⟩
    · intro u e v W
      have J := congrArg List.length W
      have L : u=[] := List.length_eq_zero_iff.mp (by simp at J; omega)
      subst u
      exact ⟨.busy stageOp (.back 0),(busy_end hp (x:=x) A),.inl (by intro _ _ H; cases H),by intro _ H; cases H⟩
  let y := step (play x a) ack
  have middle : LocalScope hp (base:=base) addr len k i y (mid++[door]) := by
    have idleAt : ∀ u v, mid=u++v → Current hp base addr len (play y u) .idle := by
      intro u v W
      obtain ⟨m,M,_⟩ := split hp mid [door] Idle
      exact idle_foreign_prefix hp M (by
        intro e H eq
        exact foreign e H ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor eq))) u v W
    apply LocalScope.append hp
    · intro u e v W
      exact ⟨.idle,idleAt u (e::v) W,.inl (by intro _ _ H; cases H),by intro _ H; cases H⟩
    · exact idle_one hp (idleAt mid [] (List.append_nil mid).symm)
  have last : LocalScope hp (base:=base) addr len k i (step (play y mid) door) b := by
    intro u e v E
    exact pre_seal_no_latch hp (Nat.le_of_lt K) loc sep F u e v E
  have two : LocalScope hp (base:=base) addr len k i y ((mid++[door])++b) :=
    LocalScope.append hp middle (by rw [BStarResetSchedule.run_append]; exact last)
  have three : LocalScope hp (base:=base) addr len k i x ((a++[ack])++((mid++[door])++b)) :=
    LocalScope.append hp first (by rw [BStarResetSchedule.run_append]; exact two)
  simpa only [List.append_assoc,List.singleton_append] using three

#print axioms interval_scope
end L4.Height.StageSealFrameActual
