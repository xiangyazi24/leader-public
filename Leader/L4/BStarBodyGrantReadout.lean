import Leader.L4.BStarStageAfterCut
import Leader.L4.BStarCapturedHeader

namespace L4.BStarBodyGrantReadout
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongTransport BStarLongToken
open BStarH6WordChart BStarLongLayout BStarLongGrant BStarGrantBirth BStarBodyStageProvenance
open BStarCaptureInterval BStarBodyBankHistory BStarGrantWriterHistory

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

theorem winner_old_writer_absent (x : X) (e i : Fin n) (j : Fin 3)
    (won : WonAt hp x e i j) : original (x i).long 1=false := by
  obtain ⟨s,E,_,W,_⟩ := won
  subst i
  have raw : BStarLongGrant.atOld ((x e).long,(x (rightNeighbor e)).long) s=(x (site e s)).long := by
    cases s <;> rfl
  by_cases h : j=1
  · subst j
    have V := BStarGrantWriterHistory.win_no_grants _ _ _ W 1
    rwa [raw] at V
  · have V := BStarGrantReaderHistory.win_writer_free _ _ _ j h W
    rwa [raw] at V

def BodyWord (x : X) (i : Fin n) (sites : Fin r → Fin n) (w : List (Fin n)) : Prop :=
  ∀ d, sites d≠i → ∀ u a v, w=u++a::v →
    let z := run x u
    oldH6 B z (sites d)=false ∧ word (oldH6 B z) i=word (oldH6 B z) (sites d) ∧
      BodyAuthority hp z a (sites d) i

/-- With the actual after-A STAGE law on a body word, a won uninterrupted
reader sees its entire acquired operand at every later protected end,
not only its header. On the acquisition mark the old writer is absent
even before the new reader bit is installed. -/
theorem held_reader_word (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (e i : Fin n) (j : Fin 3) (ne : j≠1)
    (won : WonAt hp x e i j) (w : List (Fin n))
    (life : Continuous hp (step x e) i j w)
    (sites : Fin r → Fin n)
    (A : BodyWord hp x i sites (e::w)) :
    let y := run x (e::w)
    selectedHeader (y i).long=selectedHeader (x i).long ∧
      ∀ d, (payloadView (BStarLongPublication.readSel (y i).long) (y (sites d)).long).1=
        (payloadView (BStarLongPublication.readSel (x i).long) (x (sites d)).long).1 := by
  apply BStarCapturedHeader.reader_operand hp sep x e i j ne won w life sites
  intro d D u mark v E
  obtain ⟨body,same,auth⟩ := A d D u mark v E
  cases u with
  | nil =>
    have eq : e=mark := (List.cons.inj E).1
    subst mark
    exact unwritten_body hp x e (sites d) i _ (winner_old_writer_absent hp x e i j won) body same auth
  | cons birth u =>
    obtain ⟨eq,T⟩ := List.cons.inj E
    subst birth
    have K := BStarGrantReaderHistory.header_interval hp sep x e i j ne won w life u (mark::v) T
    exact reader_body hp (run (step x e) u) mark (sites d) i j ne _ K.2.2 body same auth

/-- Before the writer's actual authorized publication, the center
writer sees the entire acquisition-time selected operand. Its own
STAGE authors only the complementary banks. -/
theorem held_writer_word (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (e i : Fin n) (won : WonAt hp x e i 1) (w : List (Fin n))
    (life : Continuous hp (step x e) i 1 w)
    (pre : BeforePublication hp (step x e) i w)
    (sites : Fin r → Fin n)
    (A : BodyWord hp x i sites (e::w)) :
    let y := run x (e::w)
    selectedHeader (y i).long=selectedHeader (x i).long ∧
      ∀ d, (payloadView (BStarLongPublication.readSel (y i).long) (y (sites d)).long).1=
        (payloadView (BStarLongPublication.readSel (x i).long) (x (sites d)).long).1 := by
  apply BStarCapturedHeader.writer_operand hp sep x e i won w life pre sites
  intro d D u mark v E
  obtain ⟨body,same,auth⟩ := A d D u mark v E
  cases u with
  | nil =>
    have eq : e=mark := (List.cons.inj E).1
    subst mark
    exact unwritten_body hp x e (sites d) i _ (winner_old_writer_absent hp x e i 1 won) body same auth
  | cons birth u =>
    obtain ⟨eq,T⟩ := List.cons.inj E
    subst birth
    have K := BStarGrantWriterHistory.header_interval hp sep x e i won w life pre u (mark::v) T
    exact writer_body hp (run (step x e) u) mark (sites d) i _ K.1 body same auth

#print axioms held_reader_word
#print axioms held_writer_word
end L4.BStarBodyGrantReadout
