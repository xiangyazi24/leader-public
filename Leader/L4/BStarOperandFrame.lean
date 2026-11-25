import Leader.L4.BStarNativeSelectorOutput
import Leader.L4.BStarOperandBank
import Leader.L4.BStarCommitRingLanding
import Leader.L4.BStarCustodyCuts
import Leader.L4.BStarCommitOperands

/-! Exact visibility frame on the settled fibre. A foreign COMMIT may
occur on the selected mark: the exclusion is only at the observed header. -/
namespace L4.BStarOperandFrame
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarH6WordChart BStarLongFixedRouting BStarCaptureInterval
open BStarCustodyCuts BStarGrantWriterHistory BStarBodyStageProvenance BStarBodyBankHistory
open BStarCommitOperands BStarCutOperandReadout

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

private theorem header_held (x : X) (e i : Fin n)
    (sep : e≠rightNeighbor e) (head : oldH6 B x i=true)
    (no : NoPublication hp x e i) :
    HeldStep (BStarLongPublication.readSel (x i).long) (x i).long (step x e i).long := by
  have side (s : Side) (loc : i=site e s) :
      HeldStep (BStarLongPublication.readSel (x i).long) (x i).long (step x e i).long := by
    let g := oldPair B x e
    let raw := ((x e).long,(x (rightNeighbor e)).long)
    let b := BStarLongPublication.readSel (x i).long
    have h : (geometry g s).axes.h6=true := by
      rw [loc] at head
      cases s <;> exact head
    have old : BStarLongPublication.readSel (BStarLongGrant.atOld raw s)=b := by
      dsimp only [b]
      rw [loc]
      cases s <;> rfl
    have safe := header_safe g raw s b h old (no s loc)
    have M := bStar_held_step k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) s b safe
    subst i
    cases s with
    | left =>
      change HeldStep _ (x e).long (step x e e).long
      simp only [AllSizeS1Geometry.step,if_true]
      exact M
    | right =>
      change HeldStep _ (x (rightNeighbor e)).long (step x e (rightNeighbor e)).long
      simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true]
      exact M
  by_cases le : i=e
  · exact side .left le
  · by_cases ri : i=rightNeighbor e
    · exact side .right ri
    · rw [show step x e i=x i by simp [AllSizeS1Geometry.step,le,ri]]
      exact .noTouch _

/-- Selected digits and header bits of an H6 word frame every
physical mark on which that word does not publish. -/
theorem nonpublishing_word_step (x : X) (e i : Fin n) (sites : Fin r→Fin n)
    (sep : e≠rightNeighbor e) (head : oldH6 B x i=true)
    (loc : WordSites (oldH6 B x) i sites)
    (authority : ∀ j, BodyAuthority hp x e j i)
    (no : NoPublication hp x e i) :
    OperandAt (step x e) i sites=OperandAt x i sites := by
  let b := BStarLongPublication.readSel (x i).long
  have H := header_held hp x e i sep head no
  have held (j : Fin r) : HeldStep b (x (sites j)).long (step x e (sites j)).long := by
    by_cases E : sites j=i
    · simpa only [E] using H
    · obtain ⟨body,word⟩ := loc j E
      exact body_step hp x e (sites j) b sep
        (writer_body hp x e (sites j) i b rfl body word (authority (sites j)))
  have ⟨hdr,digits⟩ := held_operand (.next (.empty _) H)
    (fun j => .next (.empty _) (held j))
  exact Prod.ext hdr (funext digits)

/-- The post-custody extraction uses A's actual per-mark body
authority and arbitrary continuations of the same original tape. -/
theorem nonpublishing_after_cuts {base initial : X} (u v tail : List (Fin n))
    (facts : CutFacts hp base initial u v)
    (Q : X→Prop) (init : Q initial) (closed : ∀ x e,Q x→Q (step x e))
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (e i : Fin n) (sites : Fin r→Fin n) (sep : e≠rightNeighbor e)
    (head : oldH6 B base i=true) (loc : WordSites (oldH6 B base) i sites)
    (no : NoPublication hp (run initial ((u++v)++tail)) e i) :
    let x := run initial ((u++v)++tail)
    OperandAt (step x e) i sites=OperandAt x i sites := by
  have keep (x : X) (w : List (Fin n)) (I : Q x) : Q (run x w) := by
    induction w generalizing x with
    | nil => exact I
    | cons e w ih => exact ih _ (closed _ _ I)
  let x := run initial ((u++v)++tail)
  have same : oldH6 B base=oldH6 B x :=
    funext fun j => congrArg Prod.fst (fiber x (keep _ _ init) j)
  have auth (j : Fin n) : BodyAuthority hp x e j i := by
    have H := facts.body (v++tail) e j i head
    rwa [←List.append_assoc] at H
  exact nonpublishing_word_step hp x e i sites sep (same ▸ head) (same ▸ loc) auth no

theorem nonpublishing_word_trace {base initial : X} (u v lead w : List (Fin n))
    (facts : CutFacts hp base initial u v)
    (Q : X→Prop) (init : Q initial) (closed : ∀ x e,Q x→Q (step x e))
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (i : Fin n) (sites : Fin r→Fin n) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : oldH6 B base i=true) (loc : WordSites (oldH6 B base) i sites)
    (no : BeforePublication hp (run initial ((u++v)++lead)) i w) :
    OperandAt (run initial ((u++v)++(lead++w))) i sites=
      OperandAt (run initial ((u++v)++lead)) i sites := by
  induction w generalizing lead with
  | nil => simp only [List.append_nil]
  | cons e w ih =>
    have cut : run initial ((u++v)++(lead++[e]))=
        step (run initial ((u++v)++lead)) e := by
      rw [←List.append_assoc,BStarResetSchedule.run_append]; rfl
    have N : BeforePublication hp (run initial ((u++v)++(lead++[e]))) i w := by
      intro a f t E
      rw [cut]
      exact no (e::a) f t (congrArg (List.cons e) E)
    rw [show lead++e::w=(lead++[e])++w by simp [List.append_assoc],ih (lead++[e]) N,cut]
    exact nonpublishing_after_cuts hp u v lead facts Q init closed fiber e i sites (sep e)
      head loc (no [] e w rfl)

open BStarNativeSelectorOutput BStarNativeStageDigits BStarLongLayout
open L4.Compiler.Native

/-- No raw selector change, no visible header bit change and no
physical digit change jointly imply equality of the native readout. -/
theorem visible_eq_of_operand (x y : X) (i : Fin n) (sites : Fin r→Fin n)
    (E : OperandAt y i sites=OperandAt x i sites) : visible y i sites=visible x i sites := by
  have digits := congrArg Prod.snd E
  have hdr := congrArg Prod.fst E
  have dataEq : (visible y i sites).digits=(visible x i sites).digits := by
    funext f
    unfold visible
    dsimp only
    apply congrArg L4.Compiler.Digits.val
    funext j
    apply Fin.ext
    exact congrArg BitVec.toNat (congrFun (congrFun digits j) f)
  have flagsEq : (visible y i sites).hdr=(visible x i sites).hdr := by
    funext f
    unfold visible
    dsimp only
    exact congrArg (fun z : BitVec 1 => z.getLsbD 0) (congrFun (congrArg Prod.snd hdr) f)
  have E : Output.mk (visible y i sites).digits (visible y i sites).hdr =
      Output.mk (visible x i sites).digits (visible x i sites).hdr :=
    congr (congrArg Output.mk dataEq) flagsEq
  exact E

/-- Pointwise global frame: even if the mark publishes at its
initiator, the visible record of every other H6 word is unchanged. -/
theorem visible_pointwise {base initial : X} (u v tail : List (Fin n))
    (facts : CutFacts hp base initial u v)
    (Q : X→Prop) (init : Q initial) (closed : ∀ x e,Q x→Q (step x e))
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (e : Fin n) (sep : e≠rightNeighbor e) (sites : Fin n→Fin r→Fin n)
    (loc : ∀ i,oldH6 B base i=true → WordSites (oldH6 B base) i (sites i)) :
    let x := run initial ((u++v)++tail)
    ∀ i, oldH6 B base i=true → (i≠e ∨ NoPublication hp x e e) →
      visible (step x e) i (sites i)=visible x i (sites i) := by
  dsimp only
  intro i hi N
  apply visible_eq_of_operand
  apply nonpublishing_after_cuts hp u v tail facts Q init closed fiber e i (sites i) sep hi (loc i hi)
  intro s is a mem
  have ae : a.endpoint=.left :=
    BStarLongEvents.literal_endpoint_left _ _ a mem
  intro same
  have ie : i=e := by
    rw [ae] at same
    rw [←same] at is
    exact is
  rcases N with ne|zero
  · exact ne ie
  · exact zero s (ie.symm.trans is) a mem same

open BStarOperandBank BStarOperandSites

/-- The actual three-port compiler input bank frames port-by-port
where the corresponding header does not publish, even if a
different header publishes on this mark. -/
theorem input_port_after_cuts {base initial : X} (u v tail : List (Fin n))
    (facts : CutFacts hp base initial u v)
    (Q : X→Prop) (init : Q initial) (closed : ∀ x e,Q x→Q (step x e))
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (e : Fin n) (sep : e≠rightNeighbor e) (header : Fin 3→Fin n) (q : Fin 3)
    (head : oldH6 B base (header q)=true)
    (loc : WordSites (oldH6 B base) (header q) (sites (r:=r) (header q)))
    (no : NoPublication hp (run initial ((u++v)++tail)) e (header q)) :
    let x := run initial ((u++v)++tail)
    let y := step x e
    (bankAt (r:=r) y header).digits q=(bankAt (r:=r) x header).digits q ∧
    (bankAt (r:=r) y header).hdr q=(bankAt (r:=r) x header).hdr q := by
  dsimp only
  have A := nonpublishing_after_cuts hp u v tail facts Q init closed fiber e (header q)
    (sites (r:=r) (header q)) sep head loc no
  exact ⟨digit_agree header q A,funext fun _ => congrArg (fun z : BitVec 9 => z.getLsbD _) (header_agree header q A)⟩

#print axioms visible_pointwise
#print axioms input_port_after_cuts
#print axioms nonpublishing_after_cuts
#print axioms nonpublishing_word_trace
end L4.BStarOperandFrame
