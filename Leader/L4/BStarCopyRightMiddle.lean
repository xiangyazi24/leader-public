import Leader.L4.BStarCopyRightLoadToInject
import Leader.L4.BStarCopyAttemptBand

namespace L4.BStarCopyRightMiddle
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarCopyRightLoadToInject BStarCopyAttemptBand BStarGeneratedBandScan
open BStarGeneratedOwner BStarGeneratedPCAncestry BStarGeneratedTapeCuts
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarResetChartService BStarSeparatingRail BStarOwnerControlHistory
open BStarResetSchedule BStarSeparatorControl BStarClearanceSource BStarLongDoor

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

def Range (x : X) (root : Fin n) : Prop := 8≤pc x root ∧ pc x root≤10

set_option maxHeartbeats 700000 in
private theorem consume_increment {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {e : Fin n} (sep : e≠rightNeighbor e)
    {op : Nat}
    (I : Current hp base (fun t => S.getD t fall) len x (.busy op (.back 0)))
    (E : Event hp (fun t => S.getD t fall) len x e (.busy op (.back 0)) .idle)
    (post : Range (ring x e) (S.getD 0 fall).1) :
    pc (ring x e) (S.getD 0 fall).1=op+1 := by
  obtain ⟨hh,root⟩ := root_header hp chart I.1.1
  have low : 7≤pc (ring x e) (S.getD 0 fall).1 := Nat.le_trans (by decide) post.1
  have high : pc (ring x e) (S.getD 0 fall).1≤408 := Nat.le_trans post.2 (by decide)
  exact (consume_to_band hp (base:=base) (x:=x) (addr:=fun t=>S.getD t fall)
    (len:=len) (op:=op) (e:=e) root hh sep I E low high).1

/-- A genuinely issued PC10 cannot return to idle inside the closed
8..10 band. Its only idle transition would consume to PC11. -/
theorem busy10_never_idle {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (G : GeneratedOwner hp base (fun t => S.getD t fall) len x m w .idle)
    (band : ∀ a b,w=a++b → Range (play x a) (S.getD 0 fall).1) :
    ∀ z, m≠.busy 10 z := by
  generalize Tend : Mode.idle=fin at G
  induction G with
  | endpoint _ => intro z H; rw [←Tend] at H; contradiction
  | @next x m e w d fin I E tail ih =>
    intro z H
    subst m
    have afterBand := band [e] w rfl
    have orig := E
    cases E with
    | transit _ _ _ _ _ =>
      exact ih (fun a b eq => band (e::a) b (congrArg (List.cons e) eq)) Tend _ rfl
    | arrived_hold _ =>
      exact ih (fun a b eq => band (e::a) b (congrArg (List.cons e) eq)) Tend _ rfl
    | consume =>
      have inc := consume_increment hp chart (sep e) I orig afterBand
      have Q := afterBand.2
      change pc (ring x e) (S.getD 0 fall).1≤10 at Q
      omega

private def After8 (x : X) (root : Fin n) (m : Mode) : Prop :=
  m=.busy 8 (.back 0) ∨ 9≤pc x root

private theorem after8_next {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m d : Mode} (e : Fin n)
    (I : Current hp base (fun t => S.getD t fall) len x m)
    (E : Event hp (fun t => S.getD t fall) len x e m d)
    (N : Current hp base (fun t => S.getD t fall) len (ring x e) d)
    (layout : ∀ u,BStarLongFixedRouting.Layout B base u=BStarLongFixedRouting.Layout B x u)
    (old : Range x (S.getD 0 fall).1) (next : Range (ring x e) (S.getD 0 fall).1)
    (prior : After8 x (S.getD 0 fall).1 m) :
    After8 (ring x e) (S.getD 0 fall).1 d := by
  rcases prior with rfl|prior
  · have orig := E
    cases E with
    | transit _ _ _ live _ => exact (live rfl).elim
    | arrived_hold _ => exact .inl rfl
    | consume =>
      exact .inr (by
        have h := consume_increment hp chart (sep e) I orig next
        exact Nat.le_of_eq h.symm)
  · have E := band_step hp chart sep layout e I E N
      ⟨by have := old.1; omega,by have := old.2; omega⟩
      ⟨by have := next.1; omega,by have := next.2; omega⟩
    exact .inr (Nat.le_trans prior E)

/-- The uninterrupted middle prefix ending idle has only opcode 9
on old outward marks, derived from the literal controller and the
closed 8..10 band. It permits arbitrary old PC9 K2 stutters. -/
theorem early_outward9 {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (G : GeneratedOwner hp base (fun t => S.getD t fall) len x m w .idle)
    (band : ∀ a b,w=a++b → Range (play x a) (S.getD 0 fall).1)
    (layout : ∀ a b,w=a++b → ∀ u, BStarLongFixedRouting.Layout B base u=
      BStarLongFixedRouting.Layout B (play x a) u)
    (initial : After8 x (S.getD 0 fall).1 m) :
    ∀ a e b, w=a++e::b → ∀ op j,
      Current hp base (fun t => S.getD t fall) len (play x a) (.busy op (.out j)) → op=9 := by
  generalize Tend : Mode.idle=fin at G
  induction G with
  | endpoint _ => intro a e b eq; cases a <;> contradiction
  | @next x m e w d fin I E tail ih =>
    intro a k b eq op j C
    cases a with
    | nil =>
      have H := band [] (e::w) rfl
      have PC : pc x (S.getD 0 fall).1=op := C.1.2.2.2
      have not10 : op≠10 := by
        intro Oo
        cases Oo
        cases m with
        | idle =>
          exact (by decide : (1:Nat)≠2) (I.1.2.symm.trans C.1.2.2.1)
        | busy op z =>
          have Q : pc x (S.getD 0 fall).1=op := I.1.2.2.2
          have Eo : op=10 := Q.symm.trans PC
          cases Eo
          exact busy10_never_idle hp chart sep (Tend.symm ▸ GeneratedOwner.next I E tail) band z rfl
      rcases initial with rfl|lower
      · have F := C.2.1.2.1
        exact (pointed_backward_no_forward _ len 0 I.2.1 j C.2.1.1 F).elim
      · have upper := H.2
        change pc x (S.getD 0 fall).1≤10 at upper
        omega
    | cons u a =>
      obtain ⟨rfl,J⟩ := List.cons.inj eq
      have now := at_start hp tail
      have next := after8_next hp chart sep e I E now (layout [] (e::w) rfl)
        (band [] (e::w) rfl) (band [e] w rfl) initial
      exact ih (fun a b eq => band (e::a) b (congrArg (List.cons e) eq))
        (fun a b eq => layout (e::a) b (congrArg (List.cons e) eq)) next Tend a k b J op j C

private theorem generated_append {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base addr len x a u b)
    (Q : GeneratedOwner hp base addr len (play x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

/-- Build the interstage certificate from actual successful controller
cuts, not an externally supplied per-mark PC9 shape. The fixed
whole-word phase band and genuine launch10 are enough. -/
theorem own_middle_of_band {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (pre early : List (Fin n)) (launch : Fin n)
    (hpre : GeneratedOwner hp base (fun t => S.getD t fall) len origin .idle pre (.busy 8 (.back 0)))
    (hEarly : GeneratedOwner hp base (fun t => S.getD t fall) len
      (play origin pre) (.busy 8 (.back 0)) early .idle)
    (finalLaunch : Event hp (fun t => S.getD t fall) len
      (play (play origin pre) early) launch .idle (.busy 10 (.out 0)))
    (last : Current hp base (fun t => S.getD t fall) len
      (ring (play (play origin pre) early) launch) (.busy 10 (.out 0)))
    (band : ∀ a b,early=a++b → Range (play (play origin pre) a) (S.getD 0 fall).1)
    (layout : ∀ a b,early=a++b → ∀ v,BStarLongFixedRouting.Layout B base v=
      BStarLongFixedRouting.Layout B (play (play origin pre) a) v) :
    OwnMiddle hp base origin (fun t => S.getD t fall) len pre (early++[launch]) := by
  have idle := at_end hp hEarly
  have tail := generated_append hp hEarly (.next idle finalLaunch (.endpoint last))
  have whole := generated_append hp hpre tail
  refine ⟨hpre,whole,tail,?_⟩
  intro a e z E op j cur
  rw [BStarResetSchedule.run_append] at cur
  have atIdle (H : a=early) : op=9 := by
    rw [H] at cur
    exact False.elim ((by decide : (1:Nat)≠2) (idle.1.2.symm.trans cur.1.2.2.1))
  rcases List.append_eq_append_iff.mp E with ⟨s,U,V⟩|⟨s,U,V⟩
  · cases s with
    | nil => exact atIdle (by simpa only [List.append_nil] using U)
    | cons v t =>
      have h := congrArg List.length V
      simp only [List.length_cons,List.length_nil,List.length_append] at h
      omega
  · cases s with
    | nil =>
      have H : early=a := by simpa only [List.append_nil] using U
      exact atIdle H.symm
    | cons v t =>
      exact early_outward9 hp chart sep hEarly band layout (.inl rfl) a v t U op j cur

end L4.BStarCopyRightMiddle
