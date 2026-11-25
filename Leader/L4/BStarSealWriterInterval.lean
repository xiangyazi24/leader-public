import Leader.L4.BStarWriterOwnerInterval
import Leader.L4.BStarSealOutgoingFrame
import Leader.L4.BStarSealLanding
import Leader.L4.BStarBankCapture

namespace L4.BStarSealWriterInterval
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarResetMarkAdapter BStarGeneratedOwner BStarLongCommand BStarLongGrant BStarLongDoor
open BStarGrantWriterHistory BStarWriterOwnerInterval BStarLongLayout
open BStarPublicationBirth BStarGrantBirth
open BStarAcquireAnchors BStarLongFiberOwner BStarAcquireForwardTrace

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Retain the actual writer across the generated post-SEAL interval.
Only RELEASE is excluded, not a precenter COMMIT or any other owner
mark. The fold exposes both live writer and conflict-freedom at every
prefix. No future successful body event is assumed. -/
theorem live_writer_word {base origin x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val)
    (lead w : List (Fin n)) (landed : play origin lead=x)
    (seed : bit x i 1≠0 ∧ conflict (BStarGrantReaderHistory.ports x i)=false)
    (scope : ∀ u e v,w=u++e::v → ∃ m,
      GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle (lead++u) m ∧
      Current hp base (fun j=>S.getD j fall) len (play x u) m ∧
      (longGeometry B ((play x u) i)).axes.h6=true ∧
      (∀ a, m≠.busy releaseOp a)) :
    ∀ u v,w=u++v →
      bit (play x u) i 1≠0 ∧ conflict (BStarGrantReaderHistory.ports (play x u) i)=false := by
  have move (u : List (Fin n)) (e : Fin n) (v : List (Fin n)) (split : w=u++e::v)
      (old : bit (play x u) i 1≠0 ∧ conflict (BStarGrantReaderHistory.ports (play x u) i)=false) :
      bit (step (play x u) e) i 1≠0 ∧
        conflict (BStarGrantReaderHistory.ports (step (play x u) e) i)=false := by
    obtain ⟨m,G,now,head,off⟩ := scope u e v split
    have align : play origin (lead++u)=play x u := by
      rw [BStarResetSchedule.run_append,landed]
    apply keeps_writer hp _ e i (sep e) head old.2
      (BStarGrantReaderHistory.canonical_of_live _ i 1 old.2 old.1)
    intro s loc
    have nr := no_release_request hp C sep G (align.symm ▸ now) e i s loc own
      off
    exact align ▸ nr
  have loop (rev v : List (Fin n)) (E : w=rev.reverse++v) :
      bit (play x rev.reverse) i 1≠0 ∧
        conflict (BStarGrantReaderHistory.ports (play x rev.reverse) i)=false := by
    induction rev generalizing v with
    | nil => exact seed
    | cons e rev ih =>
      have A : w=rev.reverse++e::v := by
        simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using E
      have H := move rev.reverse e v A (ih (e::v) A)
      simpa only [List.reverse_cons,BStarResetSchedule.run_append,BStarResetSchedule.run] using H
  intro u v E
  simpa only [List.reverse_reverse] using
    (loop u.reverse v (by simpa only [List.reverse_reverse] using E))

theorem live_at_end_bit {x : X} {i : Fin n} (H : bit x i 1≠0) :
    ((grant 1).read (x i).long).getLsbD 0=true := by
  have z : ∀ b : BitVec 1, b≠0 → b.getLsbD 0=true := by decide
  exact z _ H

open BStarLongPublication BStarLongLandingFrame BStarBitNoAbort
open BStarLongEvents BStarLongLiteral

theorem optional_roundtrip (d : Descriptor) (valid : d.valid=true) :
    readOptional (packOptional (some d))=some d := by
  have finite : ∀ (a b c : Fin 3) (s : Bool), let t : Descriptor := ⟨a,b,c,s⟩
      t.valid=true → readOptional (packOptional (some t))=some t := by decide
  cases d with
  | mk a b c s => exact finite a b c s valid

/-- Seed the full matched seal at the actual whole outgoing mark.
The old authenticated writer is retained despite the simultaneous
grant row, since this generated owner is executing SEAL, not RELEASE. -/
theorem after_selected_seal {base origin x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val) (k : Nat)
    (lead : List (Fin n)) (atOld : play origin lead=x)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy sealOp (.out k)))
    (now : Current hp base (fun j=>S.getD j fall) len x (.busy sealOp (.out k)))
    (header : oldH6 B x i=true) (coh : conflict (BStarGrantReaderHistory.ports x i)=false)
    (f : Payload) (d : Descriptor)
    (F : f.fault=0) (op : f.opcode.toNat=sealOp)
    (D : BStarLongPublication.decode (BitVec.ofNat 7 (f.argument.toNat/2))=some d)
    (auth : BStarLongOutgoing.actual (x i).long d=true)
    (staged : readOptional (stage.read (x i).long)=some d)
    (pick : (centerLink (oldPair B x i),.advance f)∈
      actualOffers (oldPair B x i) ((x i).long,(x (rightNeighbor i)).long)) :
    let y := step x i
    SealedCenter d (y i).long ∧ conflict (BStarGrantReaderHistory.ports y i)=false := by
  dsimp only
  have A := Bool.and_eq_true_iff.mp auth
  have live : bit x i 1≠0 := by
    intro Z
    have W : ((grant 1).read (x i).long).getLsbD 0=true := A.1
    change (grant 1).read (x i).long=0 at Z
    rw [Z] at W
    contradiction
  have keep := keeps_writer hp x i i (sep i) header coh
    (BStarGrantReaderHistory.canonical_of_live _ i 1 coh live) (by
      intro s address
      have N : ∀ a, Mode.busy sealOp (.out k)≠.busy releaseOp a := by
        intro a E
        exact (by decide : sealOp≠releaseOp) (Mode.busy.inj E).1
      have request := no_release_request hp C sep G (atOld.symm ▸ now) i i s address own N
      exact atOld ▸ request)
  have pub := BStarSealLanding.joined_selected_seal k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x i,x (rightNeighbor i)) f d header F op D auth staged pick
  have eq : readPublication (step x i i).long=
      (selector.read (x i).long,stage.read (x i).long,packOptional (some d)) := by
    simp only [AllSizeS1Geometry.step,if_true]
    exact pub
  have er := congrArg Prod.fst eq
  have et := congrArg (fun z : BitVec 2 × BitVec 8 × BitVec 8 => z.2.1) eq
  have es := congrArg (fun z : BitVec 2 × BitVec 8 × BitVec 8 => z.2.2) eq
  change selector.read (step x i i).long=selector.read (x i).long at er
  change stage.read (step x i i).long=stage.read (x i).long at et
  change sealField.read (step x i i).long=packOptional (some d) at es
  refine ⟨⟨live_at_end_bit keep.1,?_,(congrArg readOptional et).trans staged,?_⟩,keep.2⟩
  · unfold readSel
    rw [er]
    exact beq_iff_eq.mp A.2
  · rw [es,optional_roundtrip d (BStarBankCapture.decode_valid D)]

/-- A single generated-tape geometry/chronology interface transports
both writer custody and the matching descriptor seal at every cut.
Neither the final writer bit nor latch values are caller postconditions. -/
theorem every_sealed_prefix {base origin x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val)
    (k : Nat) (kle : k≤len) (slot : S.getD k fall=(i,1))
    (lead w : List (Fin n)) (landed : play origin lead=x)
    (d : Descriptor) (seed : SealedCenter d (x i).long)
    (coh : conflict (BStarGrantReaderHistory.ports x i)=false)
    (scope : ∀ u e v,w=u++e::v → ∃ m,
      GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle (lead++u) m ∧
      Current hp base (fun j=>S.getD j fall) len (play x u) m ∧
      oldH6 B (play x u) i=true ∧ (∀ a, m≠.busy releaseOp a) ∧
      (e=i → BStarSealOwnerFrame.Excluded k m)) :
    ∀ u v,w=u++v →
      SealedCenter d (play x u i).long ∧ conflict (BStarGrantReaderHistory.ports (play x u) i)=false := by
  have seedLive : bit x i 1≠0 := by
    have W := seed.1
    intro Z
    change (grant 1).read (x i).long=0 at Z
    rw [Z] at W
    contradiction
  have live := live_writer_word hp C sep i own lead w landed ⟨seedLive,coh⟩ (by
    intro u e v E
    obtain ⟨m,P,I,head,off,_⟩ := scope u e v E
    exact ⟨m,P,I,head,off⟩)
  intro u v E
  have H := live u v E
  refine ⟨BStarSealOutgoingFrame.sealed_until_outgoing hp C sep i k kle slot lead u landed d seed ?_ ?_
    (live_at_end_bit H.1),H.2⟩
  · intro a e f S
    have all : w=a++e::(f++v) := by rw [E,S,List.append_assoc,List.cons_append]
    obtain ⟨_,_,_,head,_,_⟩ := scope a e (f++v) all
    exact head
  · intro a f S
    have all : w=a++i::(f++v) := by rw [E,S,List.append_assoc,List.cons_append]
    obtain ⟨m,P,I,_,_,off⟩ := scope a i (f++v) all
    exact ⟨m,P,I,off rfl⟩

#print axioms live_writer_word
#print axioms live_at_end_bit
#print axioms after_selected_seal
#print axioms every_sealed_prefix
end L4.BStarSealWriterInterval
