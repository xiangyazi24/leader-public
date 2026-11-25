import Leader.L4.BStarCopyRightLoadAdvance
import Leader.L4.BStarNumericChronology

namespace L4.BStarCopyRightLoadCoverage
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongToken BStarLongEvents BStarLongDoor
open BStarCopyRightStrip BStarCopyRightAuthority BStarCopyRightK2Past
open BStarCopyLoadHistory BStarCopyLoadCarry
open BStarAcquireVisitOrder BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireLiteralChain
open BStarResetChartTouch BStarClearanceDataChart BStarAcquireAnchors BStarResetMarkAdapter
open BStarSeparatingRail BStarResetSchedule BStarSeparatorControl BStarAcquireForwardTrace

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

private theorem single {x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {z d : Cursor} (seen : Seen ring (project addr) anyTag len x z [e] d) :
    Advance len z d := by
  cases seen with
  | cons _ _ on _ tail => cases tail; exact on

/-- Every strict preterminal index is crossed on the actual BusyOnly
tour from its initial outward address to actual completed return.
Only adjacent advances can change an outward ordinal. -/
theorem busy_crosses {base x : X} {addr : Nat → Pos n} {len op k : Nat}
    {z : Cursor} {w : List (Fin n)}
    (busy : BusyOnly hp base addr len op x z w (.back 0)) (hk : k<len) :
    ∀ f, z=.out f → f≤k →
    ∃ pre e post, w=pre++e::post ∧
      BusyOnly hp base addr len op x (.out f) pre (.out k) ∧
      Event hp addr len (play x pre) e (.busy op (.out k)) (.busy op (.out (k+1))) ∧
      BusyOnly hp base addr len op (ring (play x pre) e) (.out (k+1)) post (.back 0) := by
  generalize finEq : Cursor.back 0=fin at busy
  induction busy with
  | nil =>
    intro f F _
    exact False.elim (by rcases finEq.trans F with h; cases h)
  | @cons x z d fin e w I E tail ih =>
    intro f F fk
    subst z
    have A : Advance len (.out f) d := by
      cases E with
      | transit _ _ _ _ N => exact single hp N
    cases A with
    | stay =>
      obtain ⟨pre,m,post,split,lead,ev,rest⟩ := ih finEq f rfl fk
      exact ⟨e::pre,m,post,congrArg (List.cons e) split,.cons I E lead,ev,rest⟩
    | forward =>
      by_cases fkEq : f=k
      · subst f
        exact ⟨[],e,w,rfl,.nil I,E,finEq.symm ▸ tail⟩
      · obtain ⟨pre,m,post,split,lead,ev,rest⟩ := ih finEq (f+1) rfl (by omega)
        exact ⟨e::pre,m,post,congrArg (List.cons e) split,.cons I E lead,ev,rest⟩
    | turn => omega

private theorem generated_append {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base addr len x a u b)
    (Q : GeneratedOwner hp base addr len (play x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

private theorem busy_as_generated {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {a b : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base addr len op x a w b) :
    GeneratedOwner hp base addr len x (.busy op a) w (.busy op b) := by
  induction P with
  | nil I => exact .endpoint I
  | cons I E _ ih => exact .next I E ih

/-- Complete old chart coverage supplies a unique preterminal K2
ordinal for every physical RS slot in the right strip. -/
theorem rs_ord {base : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (a : Fin n) (seam tail : Nat) (C : Strip B base a seam tail)
    (ownerHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (i : Nat) (lo : seam≤i) (hi : i≤tail) :
    ∃ k<len, S.getD k fall=(addr a i,2) := by
  have own := (strip_same_owner C i hi).trans ownerHead
  have rs : rail seam i=.rs := if_neg (by omega)
  rw [rs] at own
  have owner : commandOwner (oldH6 B base) (addr a i) 2=o.val := own
  have act : BStarAcquireRailCoverage.active (longGeometry B (base (addr a i))) 2=true := by
    simp [BStarAcquireRailCoverage.active]
  obtain ⟨k,kl,K⟩ := List.getElem_of_mem (chart.cover (addr a i,2) act owner)
  have M : S.getD k fall=(addr a i,2) := (List.getElem_eq_getD (h:=kl) fall).symm.trans K
  have Le : k≤len := by have := chart.length; omega
  have nEnd : k≠len := by
    intro E
    subst k
    have V := congrArg Prod.snd (chart.terminal.symm.trans M)
    change (10 : Fin 11)=2 at V
    contradiction
  exact ⟨k,by omega,M⟩

#print axioms busy_crosses
#print axioms rs_ord

/-- Exact launch cut of an original generated word, carrying the
landing history as well as the uninterrupted BusyOnly suffix. -/
theorem launch_cut {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {start : Mode} {w : List (Fin n)} {z : Cursor}
    (T : GeneratedOwner hp base addr len x start w (.busy op z)) :
    (∃ lead rest, w=lead++rest ∧
      GeneratedOwner hp base addr len x start lead (.busy op (.out 0)) ∧
      BusyOnly hp base addr len op (play x lead) (.out 0) rest z) ∨
    (∃ a, start=.busy op a ∧ BusyOnly hp base addr len op x a w z) := by
  generalize K : Mode.busy op z=fin at T
  induction T with
  | endpoint I =>
    cases K
    exact .inr ⟨z,rfl,.nil I⟩
  | next I E tail ih =>
    rcases ih K with ⟨lead,rest,R,H,Bu⟩|⟨a,R,Bu⟩
    · exact .inl ⟨_::lead,rest,congrArg (List.cons _) R,.next I E H,Bu⟩
    · subst R
      cases E with
      | launch _ H =>
        exact .inl ⟨[_],_,rfl,.next I (.launch ‹_› H) (.endpoint (busy_start hp Bu)),Bu⟩
      | transit _ _ _ live seen => exact .inr ⟨_,rfl,.cons I (.transit op _ _ live seen) Bu⟩
      | arrived_hold _ ne => exact .inr ⟨_,rfl,.cons I (.arrived_hold op ne) Bu⟩

/-- Per-source witness on one physical successful LOAD8 word. The
word split, actual old selected claim/advance, and matched ordinal
are recovered from the owner's original word, not chosen in a
separate admissible visit schedule. -/
theorem original_rs_load_visit {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a : Fin n) (seam tail : Nat) (strip : Strip B base a seam tail)
    (ownerHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w (.busy 8 (.back 0)))
    (i : Nat) (lo : seam≤i) (hi : i≤tail) :
    ∃ (lead : List (Fin n)) (e : Fin n) (rest : List (Fin n)) (k : Nat) (cl : CommandClaim) (pay : Payload),
      w=lead++e::rest ∧ k<len ∧ S.getD k fall=(addr a i,2) ∧ e=addr a i ∧
      cl.source=L 2 ∧ cl.kind≠.door ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle lead (.busy 8 (.out k)) ∧
      Event hp (fun j=>S.getD j fall) len (play x lead) e (.busy 8 (.out k)) (.busy 8 (.out (k+1))) ∧
      BusyOnly hp base (fun j=>S.getD j fall) len 8
        (ring (play x lead) e) (.out (k+1)) rest (.back 0) ∧
      (cl,.advance pay)∈actualOffers (oldPair B (play x lead) e)
        (((play x lead) e).long,((play x lead) (rightNeighbor e)).long) ∧
      (longGeometry B ((play x lead) e)).inside=true := by
  obtain ⟨k,kl,idx⟩ := rs_ord hp chart a seam tail strip ownerHead i lo hi
  rcases launch_cut hp T with ⟨launch,suffix,W,H,Busy⟩|⟨_,bad,_⟩
  · obtain ⟨pre,e,rest,spl,part,E,after⟩ := busy_crosses hp Busy kl 0 rfl (Nat.zero_le _)
    let lead := launch++pre
    have old : play x lead=play (play x launch) pre := BStarResetSchedule.run_append _ _ _ _
    have G := generated_append hp H (busy_as_generated hp part)
    have G' : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle (lead++[e])
        (.busy 8 (.out (k+1))) := by
      apply generated_append hp G
      exact .next (BStarGeneratedTapeCuts.at_end hp G) (old.symm ▸ E)
        (.endpoint (old.symm ▸ busy_start hp after))
    obtain ⟨_,_,_,_,_,_,_,_,outPayload⟩ := generated_load_word hp chart sep G'
    have pay : ∃ f, project (fun j=>S.getD j fall) (ring (play x lead) e) (k+1)=.forward f ∧
        f.fault=0 := by
      rw [BStarResetSchedule.run_append] at outPayload
      exact ⟨_,outPayload,rfl⟩
    obtain ⟨f,F,Fp⟩ := pay
    have oldC := BStarGeneratedTapeCuts.at_end hp G
    obtain ⟨cl,_,offer,selected,_,src,_⟩ := BStarNumericChronology.ring_departure
      hp chart e (sep e) 8 k kl oldC.1 oldC.2.1 oldC.2.2 f F Fp
    have occ : cl.source.occurrence=2 := congrArg Prod.snd (src.symm.trans idx)
    have mem : cl∈orderedCommands (oldPair B (play x lead) e) := by
      rw [←actualOffers_claims _ (((play x lead) e).long,((play x lead) (rightNeighbor e)).long)]
      exact List.mem_map.mpr ⟨_,selected,rfl⟩
    have raw := raw_k2 (oldPair B (play x lead) e) cl mem occ
    have srcL : cl.source=L 2 := by
      rw [raw]
      cases (oldPair B (play x lead) e).2.axes.h6 <;> rfl
    have nd : cl.kind≠.door := by
      rw [raw]
      cases (oldPair B (play x lead) e).2.axes.h6 <;> decide
    have loc := congrArg Prod.fst (src.symm.trans idx)
    have ee : e=addr a i := by rwa [srcL] at loc
    have inside : (longGeometry B ((play x lead) e)).inside=true := by
      have same := congrArg (fun z : Bool × Bool × Bool => z.2.1) (oldC.1.1 e)
      exact same.symm.trans (ee.symm ▸ strip.rs_in i lo hi)
    refine ⟨lead,e,rest,k,cl,offer,?_,kl,idx,ee,srcL,nd,G,old.symm ▸ E,old.symm ▸ after,selected,inside⟩
    rw [W,spl,List.append_assoc]
  · cases bad

#print axioms original_rs_load_visit
end L4.BStarCopyRightLoadCoverage
