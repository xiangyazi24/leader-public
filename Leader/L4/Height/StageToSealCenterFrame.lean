import Leader.L4.Height.StageSealScoped
import Leader.L4.BStarSealWriterInterval

namespace L4.Height.StageToSealCenterFrame
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
      oldH6 B (play x u) i=true ∧ BStarSealOwnerFrame.Excluded k m ∧
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
    exact ⟨H,eq ▸ BStarSealOwnerFrame.no_latch hp C sep i k le idx G (eq.symm ▸ I) N e⟩)
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
end L4.Height.StageToSealCenterFrame
