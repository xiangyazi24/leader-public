import Leader.L4.BStarOperandSites
import Leader.L4.BStarCopyIncidenceAuthority
import Leader.L4.BStarLongArithmetic
import Leader.L4.BStarCopyRightStrip

namespace L4.BStarCopyCenterActualWitness
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarLongFixedRouting
open BStarGrantWriterHistory BStarCustodyCuts BStarCommitOperands BStarCutOperandReadout
open BStarBodyGrantReadout BStarCaptureInterval BStarGrantBirth BStarLongArithmetic BStarLongLayout
open BStarH6Ordinal
open BStarCopyRightStrip (addr)
set_option maxRecDepth 4096
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

theorem actual_center_header {base old : X} (mark center : Fin n)
    (fixed : ∀ i,Layout B base i=Layout B old i)
    (pub : ¬ NoPublication hp old mark center) : oldH6 B base center=true := by
  obtain ⟨s,K,p,b,loc,_,_,L⟩ := stopping_commit hp old mark center pub
  have header : oldH6 B old center=true := by
    rw [loc]
    cases s <;> exact L.2.1
  exact (congrArg Prod.fst (fixed center)).trans header

theorem body_of_acquisition {base x : X} {u v : List (Fin n)} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)}
    (cuts : CutFacts hp base x u v)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (pre reset tail middle : List (Fin n))
    (W : (u++v)++tail=(pre++reset)++middle)
    (early : u.length≤pre.length)
    (w : List (Fin n))
    (A : Acquisition hp (run x (pre++reset)) [] w (endpoint (oldH6 B base) hh o 1).1 1)
    (noShort : ∀ z,oldH6 B base (rightNeighbor z)=true → r≤ordinal (oldH6 B base) hh z+1) :
    let head := (endpoint (oldH6 B base) hh o 1).1
    let sites : Fin r → Fin n := fun j => addr head j.val
    BodyWord hp (run (run x (pre++reset)) A.lead) head sites (A.mark::A.post) := by
  dsimp only
  let head := (endpoint (oldH6 B base) hh o 1).1
  have h : oldH6 B base head=true := (endpoint_spec (oldH6 B base) hh o 1).1
  obtain ⟨ext,E⟩ := BStarCopyIncidenceAuthority.after_cut v tail reset middle W early
  have keep (z : X) (w : List (Fin n)) (J : Q z) : Q (run z w) := by
    induction w generalizing z with
    | nil => exact J
    | cons e w ih => exact ih _ (closed z e J)
  have same (w : List (Fin n)) : oldH6 B (run x w)=oldH6 B base :=
    funext (fun i => (congrArg Prod.fst (fiber _ (keep x w I) i)).symm)
  have P : run (run x (pre++reset)) A.lead=run x (u++(ext++A.lead)) := by
    calc
      _ = run x ((pre++reset)++A.lead) := (BStarResetSchedule.run_append step x (pre++reset) A.lead).symm
      _ = _ := congrArg (run x) ((congrArg (·++A.lead) E).trans (List.append_assoc _ _ _))
  have addr_eq (n : Nat) : addr head n=BStarOperandSites.advance head n := by
    induction n with
    | zero => exact Fin.ext (Nat.mod_eq_of_lt head.isLt)
    | succ n ih =>
      rw [BStarCopyRightStrip.addr_next, BStarOperandSites.advance,ih]
  have ok : WordSites (oldH6 B base) head (fun j : Fin r=>addr head j.val) := by
    have E' : (fun j : Fin r=>addr head j.val)=BStarOperandSites.sites head := funext (fun j=>addr_eq j.val)
    rw [E']
    exact (BStarOperandSites.exact_sites hh head h noShort).2.2
  rw [P]
  exact bodyword_from_cut hp base x u (ext++A.lead) _ head _ (fun w=>same (u++w))
    (fun w e z=>cuts.body w e z head h) ok

theorem digit_at_numeric_prefix {x : X} {w : List (Fin n)} {head : Fin n}
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (A : Acquisition hp x [] w head 1)
    (body : BodyWord hp (run x A.lead) head (fun j : Fin r=>addr head j.val) (A.mark::A.post))
    (lead peek rest between : List (Fin n)) (ack : Fin n)
    (born : lead=A.lead++A.mark::between)
    (cut : w=(lead++[ack]++peek)++rest)
    (j : Fin r) (f : Fin 9) :
    let bank := BStarLongPublication.readSel (run x A.lead head).long
    digitLoad (run x (lead++[ack]++peek) (addr head j.val)).long 1 f bank.val =
      some (((bankDigit bank f).read (run x A.lead (addr head j.val)).long).toNat) := by
  let mid := between++[ack]++peek
  have E : lead++[ack]++peek=A.lead++A.mark::mid := by
    rw [born]
    simp only [mid,List.append_assoc,List.cons_append]
  have W : A.post=mid++rest := by
    have H : A.lead++A.mark::A.post=A.lead++A.mark::(mid++rest) := by
      calc
        _ = w := A.exactTape.symm
        _ = (lead++[ack]++peek)++rest := cut
        _ = (A.lead++A.mark::mid)++rest := congrArg (·++rest) E
        _ = _ := by simp only [List.append_assoc,List.cons_append]
    exact (List.cons.inj (List.append_cancel_left H)).2
  have alive : Continuous hp (step (run x A.lead) A.mark) head 1 mid := by
    intro a b T
    exact A.live a (b++rest) (by rw [W,T,List.append_assoc])
  have prior : BeforePublication hp (step (run x A.lead) A.mark) head mid := by
    intro a e b T
    exact A.writerBefore rfl a e (b++rest) (by rw [W,T,List.append_assoc,List.cons_append])
  have covered : BodyWord hp (run x A.lead) head (fun j : Fin r=>addr head j.val) (A.mark::mid) := by
    intro d hd a e b S
    exact body d hd a e (b++rest) (by rw [W,←List.cons_append,S,List.append_assoc,List.cons_append])
  have held := held_writer_word hp sep (run x A.lead) A.mark head A.won mid alive prior
    (fun j : Fin r=>addr head j.val) covered
  have H := congrArg Prod.fst held.1
  change BStarLongPublication.readSel (run (run x A.lead) (A.mark::mid) head).long=
    BStarLongPublication.readSel (run x A.lead head).long at H
  have Q := congrFun (held.2 j) f
  change (bankDigit (BStarLongPublication.readSel (run (run x A.lead) (A.mark::mid) head).long) f).read
      (run (run x A.lead) (A.mark::mid) (addr head j.val)).long =
    (bankDigit (BStarLongPublication.readSel (run x A.lead head).long) f).read
      (run x A.lead (addr head j.val)).long at Q
  rw [H] at Q
  rw [E,BStarResetSchedule.run_append]
  dsimp only
  simp only [digitLoad,Fin.val_one,beq_self_eq_true,if_true,
    dif_pos (BStarLongPublication.readSel (run x A.lead head).long).isLt]
  exact congrArg (some ∘ BitVec.toNat) Q

end L4.BStarCopyCenterActualWitness
