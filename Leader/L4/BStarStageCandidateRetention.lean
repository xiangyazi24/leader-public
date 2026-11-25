import Leader.L4.BStarStageCandidateJoined
import Leader.L4.BStarBodyStageProvenance

namespace L4.BStarStageCandidateRetention
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongPublication BStarLongOutgoing
open BStarLongWork BStarLongCommand BStarLongToken BStarLongClaims BStarBankCapture
open BStarBankTrace BStarCaptureInterval BStarLongTransport BStarLongEvents

private theorem bank_compose (b : Fin 3) {p q : Patch LW}
    (P : BankFrame b p) (Q : BankFrame b q) : BankFrame b (p.compose q) := by
  intro i lo hi
  simp [Patch.compose,P i lo hi,Q i lo hi]

/-- COMMIT may change the selector but cannot write any candidate
bank bytes. Without healthy center STAGE, every outgoing row is
bank-disjoint, including malformed and refused outgoing commands. -/
theorem outgoing_bank_frame (g : LongGeometry) (j : Fin 11) (x : BitVec LW)
    (p : Payload) (b : Fin 3)
    (N : j.val=1 → p.fault=0 → p.opcode.toNat≠stageOp) :
    BankFrame b (execute g j x p).row := by
  by_cases ne : j.val≠1
  · rw [noncenter_hold _ _ _ _ ne]
    exact (frame_empty b).1
  by_cases F : p.fault≠0
  · rw [faulty_hold _ _ _ _ F]
    exact (frame_empty b).1
  have S := N (Classical.not_not.mp ne) (Classical.not_not.mp F)
  simp only [execute,Classical.not_not.mp ne,Classical.not_not.mp F,
    bne_self_eq_false,Bool.false_or,Bool.false_eq_true,if_false,S,beq_iff_eq]
  split
  · exact (frame_compose (frame_stage_field _ _) (frame_seal_field _ _)).1
  split
  · split
    · exact (frame_empty b).1
    · split
      · exact (frame_seal_field _ _).1
      · exact (frame_empty b).1
  split
  · split
    · exact (frame_empty b).1
    · split
      · split
        · intro i lo hi
          apply Bool.eq_false_iff.mpr
          intro M
          obtain ⟨_,E⟩ := (commit_support _ _ _ _ _ _).mp M
          have B : 2222≤bankBase b ∧ bankBase b+45≤2357 := by
            simp only [bankBase]
            omega
          omega
        · exact (frame_empty b).1
      · exact (frame_empty b).1
  · exact (frame_empty b).1

def NoStage (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (s : Side) : Prop :=
  ∀ c p, (c,.advance p)∈offers g raw → c.source.side=s → c.source.occurrence.val=1 →
    (beforeOutgoing g raw c p).2.fault=0 → (beforeOutgoing g raw c p).2.opcode.toNat≠stageOp

def SideBank (b : Fin 3) (s : Side) (w : Bool × Patch LW) : Prop :=
  w.1=sideFlag s → BankFrame b w.2

private theorem selected_bank (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : Side) (b : Fin 3) (H : NoStage g raw s) (o : CmdOffer) (M : o∈offers g raw) :
    ∀ w∈(selected g raw o).work, SideBank b s w := by
  obtain ⟨c,t⟩ := o
  cases t <;> simp only [selected]
  all_goals try (intro w hw; simp at hw; done)
  · split
    · intro w hw; simp at hw
    · intro w hw _
      obtain rfl := List.mem_singleton.mp hw
      exact (BStarBankWork.of_beforeBank (BStarBankWork.door_frame _ _ _ ‹_›) b).1
    · intro w hw _
      obtain rfl := List.mem_singleton.mp hw
      exact (BStarBankWork.of_beforeBank (BStarBankWork.accept_frame _ _ _) b).1
  · rename_i p
    intro w hw eq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl
    · exact (BStarBankWork.of_beforeBank (BStarBankWork.numeric_visit _ _ _ _) b).1
    · have hs : c.source.side=s := by
        cases h : c.source.side <;> cases s <;> simp_all [sideFlag]
      exact outgoing_bank_frame _ _ _ _ b (H c p M hs)

private theorem selected_fold_bank (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : Side) (b : Fin 3) (H : NoStage g raw s) (os : List CmdOffer)
    (subset : ∀ a∈os,a∈offers g raw) (acc : Selected)
    (init : ∀ w∈acc.work,SideBank b s w) :
    ∀ w∈(os.foldl (fun a o => Selected.append a (selected g raw o)) acc).work,SideBank b s w := by
  induction os generalizing acc with
  | nil => exact init
  | cons o os ih =>
    apply ih (fun a ha => subset a (List.mem_cons_of_mem _ ha))
    intro w hw
    exact (List.mem_append.mp hw).elim (init w)
      (selected_bank g raw s b H o (subset o List.mem_cons_self) w)

theorem work_bank (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (s : Side) (b : Fin 3)
    (H : NoStage g raw s) : BankFrame b (lane (sideFlag s) (longWork g raw)) := by
  have routine : ∀ w∈(longTrace g raw).assignments, SideBank b s w := by
    intro w hw
    unfold longTrace at hw
    simp only [List.mem_append] at hw
    rcases hw with (((((hf|hc)|hg)|hd)|hw)|hl)
    · obtain ⟨q,_,rfl⟩ := List.mem_map.mp hf
      exact fun _ => (k_protects b q).1
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl
      · exact fun _ => (nonheader_protects b g.1).1
      · exact fun _ => (nonheader_protects b g.2).1
    · exact fun _ => (grant_protects g raw _ b w hg).1
    · exact fun _ => (copy_protects g _ _ b w hd).1
    · exact selected_fold_bank g raw s b H _ (fun _ e => e) _ (by simp) w hw
    · obtain ⟨q,_,rfl⟩ := List.mem_map.mp hl
      exact fun _ => (k_protects b q).1
  intro i lo hi
  rw [exact_assignment_mask]
  apply Bool.eq_false_iff.mpr
  intro M
  obtain ⟨w,hw,hf⟩ := List.any_eq_true.mp M
  have ⟨hs,hm⟩ := Bool.and_eq_true_iff.mp hf
  have F := routine w hw (beq_iff_eq.mp hs)
  simp [F i lo hi] at hm

private theorem guard_bank (b : Fin 3) (head : Bool) (x : BitVec LW) (q : Patch LW)
    (H : BankFrame b q) : BankFrame b (LongDoorGuard.guard manifest head x q) := by
  unfold LongDoorGuard.guard
  split
  · exact bank_compose b H (BStarBankWork.of_beforeBank BStarBankWork.repair_frame b).1
  · exact H

private theorem pair_bank (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (s : Side)
    (b : Fin 3) (w t : Pair (Patch LW))
    (W : BankFrame b (lane (sideFlag s) w)) (T : BankFrame b (lane (sideFlag s) t)) :
    BankFrame b (lane (sideFlag s) (LongDoorGuard.pairGuard manifest g raw
      (w.1.compose t.1,w.2.compose t.2))) := by
  cases s
  · exact bank_compose b W T
  · exact guard_bank _ _ _ _ (bank_compose b W T)

theorem joined_bank (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (s : Side) (b : Fin 3)
    (H : NoStage g raw s) : BankFrame b (lane (sideFlag s) (joinedPatch g raw)) := by
  unfold joinedPatch
  exact pair_bank g raw s b _ _ (work_bank g raw s b H) (scratch_frame g raw s b).1

theorem bank_digit_read {b : Fin 3} {q : Patch LW} (h : BankFrame b q) (x : BitVec LW)
    (f : Fin 9) : (bankDigit b f).read (q.apply x)=(bankDigit b f).read x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,bankDigit,bankPart]
  exact Patch.hold _ _ _ (h _ (by omega) (by omega))

theorem bank_header_read {b : Fin 3} {q : Patch LW} (h : BankFrame b q) (x : BitVec LW)
    (f : Fin 9) : (bankHeader b f).read (q.apply x)=(bankHeader b f).read x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,bankHeader,bankPart]
  exact Patch.hold _ _ _ (h _ (by omega) (by omega))

def BankAt (b : Fin 3) (x : BitVec LW) :=
  ((fun f => (bankDigit b f).read x),(fun f => (bankHeader b f).read x))

theorem joined_keeps (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (s : Side) (b : Fin 3)
    (H : NoStage g raw s) : BankAt b (joinedRead g raw s)=BankAt b (lane (sideFlag s) raw) := by
  have P := joined_bank g raw s b H
  exact Prod.ext (funext (bank_digit_read P _)) (funext (bank_header_read P _))

open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarResetMarkAdapter BStarGeneratedOwner BStarLongDoor BStarClearanceSource
open BStarStageProvenance

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

def RingNoStage (x : X) (e i : Fin n) : Prop :=
  ∀ s, i=site e s →
    NoStage (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) s

theorem ring_keeps (x : X) (e i : Fin n) (sep : e≠rightNeighbor e) (b : Fin 3)
    (H : RingNoStage hp x e i) :
    BankAt b (step x e i).long=BankAt b (x i).long := by
  by_cases L : i=e
  · subst i
    have K := congrArg (BankAt b) (joined_read k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) .left)
    simpa [AllSizeS1Geometry.step,sideFlag,lane] using
      K.trans (joined_keeps (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) .left b (H .left rfl))
  · by_cases R : i=rightNeighbor e
    · subst i
      have K := congrArg (BankAt b) (joined_read k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
        (x e,x (rightNeighbor e)) .right)
      simpa [AllSizeS1Geometry.step,Ne.symm sep,sideFlag,lane] using
        K.trans (joined_keeps (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) .right b (H .right rfl))
    · simp only [AllSizeS1Geometry.step,if_neg L,if_neg R]

/-- To rule out any healthy STAGE at an old site, it suffices that
its actual K1 owner is generated and not busy STAGE. This does not
constrain simultaneous COMMIT at that site. -/
theorem excludes_stage {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (P : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (run x w) m)
    (e i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val)
    (no : ∀ a,m≠.busy stageOp a) :
    RingNoStage hp (run x w) e i := by
  intro s loc K p sel hs hj hf ho
  let y := run x w
  have idx : address e K.source=(i,1) :=
    Prod.ext ((congrArg (site e) hs).trans loc.symm) (Fin.ext hj)
  have act : active (longGeometry B (base i)) (1 : Fin 11)=true := rfl
  obtain ⟨k,hk,J⟩ := List.getElem_of_mem (C.cover (i,1) act own)
  have named : S.getD k fall=(i,1) := (List.getElem_eq_getD _).symm.trans J
  have L := C.length
  have le : k≤len := by omega
  have A := BStarBodyStageProvenance.selected_descriptor hp C sep P now k le e K p
    (named.trans idx.symm) sel ⟨hf,ho⟩
  exact no _ A.1

/-- Bank bytes stay fixed on the actual raw suffix, even if its last
mark is a literal successful COMMIT and changes the selected bank. -/
theorem word_keeps (x : X) (w : List (Fin n)) (i : Fin n) (b : Fin 3)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (H : ∀ u e v,w=u++e::v → RingNoStage hp (run x u) e i) :
    BankAt b (run x w i).long=BankAt b (x i).long := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    have K := ring_keeps hp x e i (sep e) b (H [] e w rfl)
    have next := ih (step x e) (fun u q v E => H (e::u) q v (congrArg (List.cons e) E))
    exact next.trans K

/-- A fixed site's just-staged candidates stay fixed until and
including publication if no later prefix of that site's generated
K1 owner is busy STAGE. In particular any mix of 409/410/411 is
permitted. The old endpoint checks are on one actual word. -/
theorem word_keeps_owned {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead suffix : List (Fin n)) (i : Fin n) (b : Fin 3)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (atPrefix : ∀ u e v, suffix=u++e::v →
      let w := lead++u
      ∃ m, GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m ∧
        Current hp base (fun j => S.getD j fall) len (run x w) m ∧
        (∀ a,m≠.busy stageOp a)) :
    BankAt b (run x (lead++suffix) i).long=BankAt b (run x lead i).long := by
  rw [BStarResetSchedule.run_append]
  apply word_keeps hp _ _ _ _ sep
  intro u e v W
  obtain ⟨m,P,N,no⟩ := atPrefix u e v W
  have E : run x (lead++u)=run (run x lead) u := BStarResetSchedule.run_append _ _ _ _
  exact E ▸ excludes_stage hp C sep P N e i own no

#print axioms word_keeps_owned
#print axioms excludes_stage
#print axioms word_keeps
#print axioms joined_keeps
end L4.BStarStageCandidateRetention
