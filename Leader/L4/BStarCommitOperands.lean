import Leader.L4.BStarCutOperandReadout
import Leader.L4.BStarReaderOwnerInterval
import Leader.L4.BStarH6Ordinal

namespace L4.BStarCommitOperands
open AllSizeProtocol BStarTrace BStarLongClaims
open BStarH6WordChart BStarGrantBirth BStarFirstCut BStarCaptureInterval
open BStarCutOperandReadout BStarBodyStageProvenance BStarGrantWriterHistory
open BStarLongPublication BStarLongEvents BStarLongCommand
open BStarLongWork BStarBodyGrantReadout

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- The physical readout of a selected operand, with an explicit address
map for its body IN digits. No tag or digit permutation is inferred. -/
def OperandAt (y : X) (i : Fin n) (sites : Fin r → Fin n) :=
  (selectedHeader (y i).long,
    fun d => (payloadView (readSel (y i).long) (y (sites d)).long).1)

structure Acquisition (x : X) (cut tape : List (Fin n))
    (header : Fin n) (port : Fin 3) where
  lead : List (Fin n)
  mark : Fin n
  post : List (Fin n)
  exactTape : tape=lead++mark::post
  afterCut : cut.length≤lead.length
  won : WonAt hp (run x lead) mark header port
  live : Continuous hp (step (run x lead) mark) header port post
  writerBefore : port=1 → BeforePublication hp (step (run x lead) mark) header post

/-- Reader acquisition evidence from an actual won mark plus the exact
continuity result supplied by its recovered owner (or a direct bit-history). -/
def Acquisition.reader (x : X) (cut tape : List (Fin n)) (header : Fin n)
    (port : Fin 3) (ne : port≠1)
    (lead : List (Fin n)) (mark : Fin n) (post : List (Fin n))
    (E : tape=lead++mark::post) (L : cut.length≤lead.length)
    (won : WonAt hp (run x lead) mark header port)
    (life : Continuous hp (step (run x lead) mark) header port post) :
    Acquisition hp x cut tape header port :=
  ⟨lead,mark,post,E,L,won,life,fun h => (ne h).elim⟩

/-- Writer acquisition evidence from the recovered owner's actual won mark
and its protected interval, which expressly ends before publication. -/
def Acquisition.writer (x : X) (cut tape : List (Fin n)) (header : Fin n)
    (lead : List (Fin n)) (mark : Fin n) (post : List (Fin n))
    (E : tape=lead++mark::post) (L : cut.length≤lead.length)
    (won : WonAt hp (run x lead) mark header 1)
    (life : Continuous hp (step (run x lead) mark) header 1 post)
    (before : BeforePublication hp (step (run x lead) mark) header post) :
    Acquisition hp x cut tape header 1 :=
  ⟨lead,mark,post,E,L,won,life,fun _ => before⟩

open BStarAcquireVisitOrder BStarAcquireRailCoverage BStarAcquireLiteralChain
open BStarAcquireAnchors BStarLongFiberOwner BStarGeneratedOwner BStarLongDoor
open BStarClearanceSource BStarLongGrant
open BStarResetChartTouch BStarResetMarkAdapter

/-- Attach the actual reader's own generated history to the common tape. -/
def Acquisition.reader_owned {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (cut tape lead : List (Fin n)) (birth i : Fin n) (port : Fin 3)
    (ne : port≠1) (post : List (Fin n)) (E : tape=lead++birth::post)
    (after : cut.length≤lead.length)
    (own : commandOwner (oldH6 B base) i ⟨port.val,by omega⟩=o.val)
    (won : WonAt hp (run x lead) birth i port)
    (atPrefix : ∀ u e v, post=u++e::v →
      let w := lead++birth::u
      ∃ m, GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m ∧
        Current hp base (fun j => S.getD j fall) len (run x w) m ∧
        (ctrlOp.read ((run x w) (S.getD 0 fall).1).long).toNat≠releaseOp ∧
        (longGeometry B ((run x w) i)).axes.h6=true) :
    Acquisition hp x cut tape i port :=
  .reader hp x cut tape i port ne lead birth post E after won
    (BStarReaderOwnerInterval.owned_interval hp chart sep lead birth i port ne post own won atPrefix).1

/-- Attach the actual centre writer's generated history to the common
tape, with the old publication PC excluded until the designated stop. -/
def Acquisition.writer_owned {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (cut tape lead : List (Fin n)) (birth i : Fin n)
    (post : List (Fin n)) (E : tape=lead++birth::post) (after : cut.length≤lead.length)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (won : WonAt hp (run x lead) birth i 1)
    (atPrefix : ∀ u e v, post=u++e::v →
      let w := lead++birth::u
      ∃ m, GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m ∧
        Current hp base (fun j => S.getD j fall) len (run x w) m ∧
        (ctrlOp.read ((run x w) (S.getD 0 fall).1).long).toNat≠releaseOp ∧
        (ctrlOp.read ((run x w) (S.getD 0 fall).1).long).toNat≠commitOp ∧
        (longGeometry B ((run x w) i)).axes.h6=true) :
    Acquisition hp x cut tape i 1 :=
  let K := BStarWriterOwnerInterval.owned_interval hp chart sep lead birth i post own won atPrefix
  .writer hp x cut tape i lead birth post E after won K.2.1 K.1

theorem operand_at_acquire (base x : X) (cut tail : List (Fin n))
    (header : Fin n) (port : Fin 3) (sites : Fin r → Fin n)
    (A : Acquisition hp x cut (cut++tail) header port)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ v, oldH6 B (run x (cut++v))=oldH6 B base)
    (auth : ∀ v e z, BodyAuthority hp (run x (cut++v)) e z header)
    (sites_ok : WordSites (oldH6 B base) header sites) :
    OperandAt (run x (cut++tail)) header sites=OperandAt (run x A.lead) header sites := by
  obtain ⟨lead,mark,post,W,L,won,live,h⟩ := A
  dsimp only
  obtain ⟨q,Q⟩ := lead_after W L
  have A : BodyWord hp (run x lead) header sites (mark::post) := by
    rw [Q]
    exact bodyword_from_cut hp base x cut q _ header sites layout auth sites_ok
  rw [W,BStarResetSchedule.run_append]
  apply Prod.ext
  all_goals
    by_cases P : port=1
    · subst port
      have H := held_writer_word hp sep _ mark header won post live (h rfl) sites A
      first | exact H.1 | exact funext H.2
    · have H := held_reader_word hp sep _ mark header port P won post live sites A
      first | exact H.1 | exact funext H.2

/-- At one literal successful COMMIT, all three operands are evaluated
on its *same old physical state*. The returned witness for each
operand is its given acquisition prefix on that exact tape. The
scheduler order of the distinct prefix times is not assumed. -/
theorem precommit_three (base x : X) (cut tail : List (Fin n)) (commit : Fin n)
    (header : Fin 3 → Fin n) (sites : Fin 3 → Fin r → Fin n)
    (A : ∀ j, Acquisition hp x cut (cut++tail) (header j) j)
    (distinct : ∀ j k, j≠k → (A j).lead.length≠(A k).lead.length)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ v, oldH6 B (run x (cut++v))=oldH6 B base)
    (auth : ∀ j v e z, BodyAuthority hp (run x (cut++v)) e z (header j))
    (sites_ok : ∀ j, WordSites (oldH6 B base) (header j) (sites j))
    (pub : ¬NoPublication hp (run x (cut++tail)) commit (header 1)) :
    ∃ (lead : Fin 3 → List (Fin n)) (marks : Fin 3 → Fin n)
      (post : Fin 3 → List (Fin n)),
      (∀ j k, j≠k → (lead j).length≠(lead k).length) ∧
      (∀ j, (cut++tail)=(lead j)++marks j::post j ∧ cut.length≤(lead j).length ∧
        WonAt hp (run x (lead j)) (marks j) (header j) j ∧
        OperandAt (run x (cut++tail)) (header j) (sites j)=
          OperandAt (run x (lead j)) (header j) (sites j)) ∧
      (∃ (s : Side) (C : CommandClaim) (q : BStarLongToken.Payload) (b : Fin 3),
        header 1=site commit s ∧ C.source.side=s ∧
        let y := run x (cut++tail)
        let g := oldPair B y commit
        let raw : Pair (BitVec LW) := ((y commit).long,(y (rightNeighbor commit)).long)
        (C,.advance q)∈actualOffers g raw ∧
        LiteralCommit (geometry g s) C.source (y (header 1)).long q b) := by
  refine ⟨fun j => (A j).lead,fun j => (A j).mark,fun j => (A j).post,distinct,?_,?_⟩
  · intro j
    exact ⟨(A j).exactTape,(A j).afterCut,(A j).won,
      operand_at_acquire hp base x cut tail (header j) j (sites j) (A j) sep layout (auth j) (sites_ok j)⟩
  · exact stopping_commit hp _ commit (header 1) pub

open BStarH6Ordinal

theorem right_back (i : Fin n) (k : Nat) : rightNeighbor (back i (k+1))=back i k := by
  apply Fin.ext
  change (((((i.val : Int)-((k+1 : Nat) : Int))%(n : Int)).toNat+1)%n)
    = (((i.val : Int)-(k : Int))%(n : Int)).toNat
  have nn : 0<(n : Int) := by have := i.isLt; omega
  have N (j : Nat) : 0≤((i.val : Int)-(j : Int))%(n : Int) :=
    Int.emod_nonneg _ (Int.ne_of_gt nn)
  apply Int.ofNat_inj.mp
  simp only [Int.natCast_emod,Int.natCast_add,Int.natCast_one]
  rw [Int.toNat_of_nonneg (by simpa only [Int.natCast_add,Int.natCast_one] using N (k+1)),
    Int.toNat_of_nonneg (N k)]
  rw [Int.add_emod,Int.emod_emod,← Int.add_emod]
  congr 1
  omega

/-- A site's nearest old header labels the same cyclic word, including
when the backward path crosses numeric index zero. -/
theorem first_word {h : Fin n → Bool} (hh : ∃ i,h i=true) (i : Fin n)
    (k : Nat) (H : First h i k) : word h (back i k)=word h i := by
  have chain (l : Nat) (L : l≤k) : word h (back i l)=word h i := by
    induction l with
    | zero => rw [back_zero]
    | succ l ih =>
      have F := H.2 l (by omega)
      have R := right_word h (back i (l+1))
      rw [right_back,F] at R
      simp only [Bool.toNat_false,Int.natCast_zero,Int.add_zero] at R
      have range := word_range h (back i (l+1)) hh
      rw [Int.emod_eq_of_lt range.1 range.2] at R
      exact R.symm.trans (ih (by omega))
  exact chain k (Nat.le_refl _)

/-- The physical ordinal address for each digit suffices for WordSites;
no extra cyclic word-equality hypothesis is needed. Digit numbering is
certified by the exact ordinal, not solely by the shared word label. -/
theorem word_sites_of_ordinal {h : Fin n → Bool} (hh : ∃ i,h i=true)
    (header : Fin n) (sites : Fin r → Fin n)
    (owns : ∀ d, back (sites d) (ordinal h hh (sites d))=header)
    (digit : ∀ d, ordinal h hh (sites d)=d.val) :
    WordSites h header sites := by
  intro d D
  have K := (ordinal_spec h hh (sites d)).2
  constructor
  · have N : ordinal h hh (sites d)≠0 := by
      intro z
      exact D ((back_zero _).symm.trans (z ▸ owns d))
    have positive : 0<ordinal h hh (sites d) := by rw [digit d] at N ⊢; omega
    simpa only [back_zero] using K.2 0 positive
  · exact (congrArg (word h) (owns d).symm).trans (first_word hh _ _ K)

end L4.BStarCommitOperands
