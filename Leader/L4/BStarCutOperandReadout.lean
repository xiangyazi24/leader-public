import Leader.L4.BStarBodyGrantReadout
import Leader.L4.BStarFirstCut

namespace L4.BStarCutOperandReadout
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarH6WordChart BStarGrantBirth BStarFirstCut BStarCaptureInterval
open BStarBodyGrantReadout BStarGrantWriterHistory BStarBodyStageProvenance

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Fixed word addresses on the old recovered fibre. The header itself
can occur among the digit locations, where the header proof applies. -/
def WordSites (h6 : Fin n → Bool) (i : Fin n) (sites : Fin r → Fin n) : Prop :=
  ∀ d, sites d≠i → h6 (sites d)=false ∧ word h6 i=word h6 (sites d)

theorem lead_after {u rest lead : List (Fin n)} {e : Fin n} {tail : List (Fin n)}
    (E : u++rest=lead++e::tail) (L : u.length≤lead.length) :
    ∃ q, lead=u++q := by
  rcases List.append_eq_append_iff.mp E with ⟨q,Q,_⟩|⟨q,Q,_⟩
  · exact ⟨q,Q⟩
  · have K := congrArg List.length Q
    simp only [List.length_append] at K
    have empty : q=[] := List.length_eq_zero_iff.mp (by omega)
    rw [empty,List.append_nil] at Q
    exact ⟨[],by simpa using Q.symm⟩

/-- Recover the whole physical body law from the already proved
post-A old mark theorem, not from assumptions that digit values
stay equal on the tape. -/
theorem bodyword_from_cut (base x : X) (u extra tape : List (Fin n))
    (i : Fin n) (sites : Fin r → Fin n)
    (layout : ∀ v, oldH6 B (run x (u++v))=oldH6 B base)
    (authority : ∀ v e z, BodyAuthority hp (run x (u++v)) e z i)
    (site : WordSites (oldH6 B base) i sites) :
    BodyWord hp (run x (u++extra)) i sites tape := by
  intro d hd pre e tail E
  have Q : run (run x (u++extra)) pre=run x (u++(extra++pre)) := by
    rw [←BStarResetSchedule.run_append,List.append_assoc]
  dsimp only
  rw [Q]
  obtain ⟨H,W⟩ := site d hd
  exact ⟨(congrFun (layout _) (sites d)).trans H,
    (congrArg (fun h => word h i) (layout _)).trans
      (W.trans (congrArg (fun h => word h (sites d)) (layout _)).symm),
    authority _ _ _⟩

/-- Full readout of a live post-A reader, at the last physical
state of the given tape. Its acquisition can be earlier than
the second cut; the actual birth stays recorded. -/
theorem reader_cut_operand (base x : X) (u tail : List (Fin n)) (i : Fin n) (j : Fin 3)
    (reader : j≠1) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (sites : Fin r → Fin n)
    (layout : ∀ v, oldH6 B (run x (u++v))=oldH6 B base)
    (auth : ∀ v e z, BodyAuthority hp (run x (u++v)) e z i)
    (site : WordSites (oldH6 B base) i sites)
    (birth : BirthAfter hp x (u++tail) i j u.length) :
    ∃ pre e post, (u++tail)=pre++e::post ∧ u.length≤pre.length ∧
      let y := run x (u++tail)
      let z := run x pre
      selectedHeader (y i).long=selectedHeader (z i).long ∧
      ∀ d, (payloadView (BStarLongPublication.readSel (y i).long) (y (sites d)).long).1=
        (payloadView (BStarLongPublication.readSel (z i).long) (z (sites d)).long).1 := by
  obtain ⟨pre,e,post,W,L,_,won,live⟩ := birth
  obtain ⟨q,Q⟩ := lead_after W L
  have B0 := bodyword_from_cut hp base x u q (e::post) i sites layout auth site
  have B1 : BodyWord hp (run x pre) i sites (e::post) := by rw [Q]; exact B0
  have U := held_reader_word hp sep (run x pre) e i j reader won post live sites B1
  refine ⟨pre,e,post,W,L,?_⟩
  rw [W,BStarResetSchedule.run_append]
  exact U

/-- Writer version, on the actual old prefix before its own first
authorized publication. Excluding that mark is necessary: that
mark deliberately installs the new selector. -/
theorem writer_cut_operand (base x : X) (u tail pre : List (Fin n)) (e i : Fin n)
    (post : List (Fin n)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (sites : Fin r → Fin n)
    (layout : ∀ v, oldH6 B (run x (u++v))=oldH6 B base)
    (auth : ∀ v e z, BodyAuthority hp (run x (u++v)) e z i)
    (site : WordSites (oldH6 B base) i sites)
    (W : (u++tail)=pre++e::post) (L : u.length≤pre.length)
    (won : WonAt hp (run x pre) e i 1)
    (live : Continuous hp (step (run x pre) e) i 1 post)
    (before : BeforePublication hp (step (run x pre) e) i post) :
    let y := run x (u++tail)
    let z := run x pre
    selectedHeader (y i).long=selectedHeader (z i).long ∧
      ∀ d, (payloadView (BStarLongPublication.readSel (y i).long) (y (sites d)).long).1=
        (payloadView (BStarLongPublication.readSel (z i).long) (z (sites d)).long).1 := by
  dsimp only
  obtain ⟨q,Q⟩ := lead_after W L
  have B0 := bodyword_from_cut hp base x u q (e::post) i sites layout auth site
  have B1 : BodyWord hp (run x pre) i sites (e::post) := by rw [Q]; exact B0
  have U := held_writer_word hp sep (run x pre) e i won post live before sites B1
  rw [W,BStarResetSchedule.run_append]
  exact U

end L4.BStarCutOperandReadout
