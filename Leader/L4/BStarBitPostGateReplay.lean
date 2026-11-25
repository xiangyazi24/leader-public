import Leader.L4.BStarBitHealthyIdle

namespace L4.BStarBitPostGateReplay
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarBitHealthyService BStarBitUniqueGate BStarBitGateGeometry BStarClearanceOffset BStarH6Ordinal

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Every earlier physical mark either stutters or advances one slot,
retaining the exact well-formed BIT. No scheduler premise. -/
theorem arbitrary_postgate_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (g : Nat) (G : g<len) (gateK : (S.getD g fall).2=1)
    (gateH : oldOrdinal B base hh (S.getD g fall).1=4)
    (j : Nat) (J : j<len) (after : g<j) (qx : Q x) (ready : correct (oldH6 B base) hh 5 x) (e : Fin n) (pay : Payload) (well : Wire pay)
    (cur : Current hp base (fun k=>S.getD k fall) len x (.busy bitOp (.out j)))
    (old : project (fun k=>S.getD k fall) x j=.forward pay) :
    ∃ k, j≤k ∧ k≤j+1 ∧
      Event hp (fun t=>S.getD t fall) len x e (.busy bitOp (.out j)) (.busy bitOp (.out k)) ∧
      Current hp base (fun t=>S.getD t fall) len (step x e) (.busy bitOp (.out k)) ∧
      project (fun t=>S.getD t fall) (step x e) k=.forward pay ∧
      (linkAt hp x e (fun t=>S.getD t fall) len j → k=j+1) := by
  have fixed : ∀ i,oldH6 B x i=oldH6 B base i := fun i => (congrArg Prod.fst (fiber x qx i)).symm
  have on : gate bitOp (S.getD g fall).2 (longGeometry B (x (S.getD g fall).1))=true := by
    rw [gateK]
    exact (bit_gate_iff hp hh fixed ready _ 1).mpr ⟨rfl,gateH⟩
  have off (u : Nat) (U : u≤len) (late : g<u) :
      gate bitOp (S.getD u fall).2 (longGeometry B (x (S.getD u fall).1))=false := by
    apply Bool.eq_false_iff.mpr
    intro H
    exact (Nat.ne_of_lt late) (chart_no_second_gate hp C fixed ready (Nat.le_of_lt G) U on H)
  have away := off j (by omega) after
  by_cases link : linkAt hp x e (fun t=>S.getD t fall) len j
  · obtain ⟨E,I,F⟩ := nominated_step hp C Q fiber closed sep qx e j pay cur old well link away
    exact ⟨j+1,by omega,Nat.le_refl _,E,I,by rw [off (j+1) (by omega) (by omega),if_neg (by decide : ¬ (false=true))] at F; exact F,fun _ => rfl⟩
  · obtain ⟨m,ev,nxt⟩ := current_step hp C Q fiber closed sep qx e (.busy bitOp (.out j)) cur
    have K : j<len := by omega
    have silent := (BStarBitHealthyIdle.silent_at_bit hp C e (sep e) bitOp j cur.1 pay
      cur.2.1 old well away link (fun E => (Nat.ne_of_lt K E).elim)).2
    have F : project (fun t=>S.getD t fall) (step x e) j=.forward pay := silent.trans old
    cases ev with
    | transit _ _ d live seen =>
      cases seen with
      | cons M go adv gd tail =>
        cases tail
        cases adv with
        | stay => exact ⟨j,Nat.le_refl _,by omega,.transit _ _ _ live (.cons M go (.stay _) gd (.nil _ _)),nxt,F,
            fun H => (link H).elim⟩
        | forward =>
          have E := (BStarOwnerControlHistory.pointed_unique_forward _ len (j+1) nxt.2.1 nxt.2.2 j (by omega)).mp ⟨pay,F⟩
          omega
        | turn => omega

/-- A replay with the nominated ordered subsequence reaches the terminal
on some prefix. Intervening marks may help but cannot undo progress or
change the well-formed BIT before that first terminal cut. -/
theorem reaches_terminal_of_sublist {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (g : Nat) (G : g<len) (gateK : (S.getD g fall).2=1)
    (gateH : oldOrdinal B base hh (S.getD g fall).1=4)
    (pay : Payload) (well : Wire pay)
    {ls w : List (Fin n)} (sub : ls.Sublist w) :
    ∀ (x : X) (a j : Nat), a+ls.length=len → a≤j → j≤len → g<j → Q x → correct (oldH6 B base) hh 5 x →
      Current hp base (fun t=>S.getD t fall) len x (.busy bitOp (.out j)) →
      project (fun t=>S.getD t fall) x j=.forward pay →
      (∀ k (hk : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y ls[k] (fun t=>S.getD t fall) len (a+k)) →
      ∃ pre post, w=pre++post ∧
        BusyOnly hp base (fun t=>S.getD t fall) len bitOp x (.out j) pre (.out len) ∧
        project (fun t=>S.getD t fall) (play x pre) len=.forward pay := by
  induction sub with
  | slnil =>
    intro state a j J A U _ _ _ I F _
    have eq : j=len := by simp at J; omega
    subst j
    exact ⟨[],[],rfl,.nil I,F⟩
  | @cons ls w e sub ih =>
    intro state a j J A U later q ready I F nominate
    by_cases eqa : j=len
    · subst j
      exact ⟨[],e::w,rfl,.nil I,F⟩
    have jl : j<len := by omega
    obtain ⟨k,jk,K,E,now,new,_⟩ := arbitrary_postgate_step hp C Q fiber closed sep g G
      gateK gateH j jl later q ready e pay well I F
    have offset := stable hp _ hh state e (sep e)
      (fun i => (congrArg Prod.fst (fiber state q i)).symm)
      (BStarClearanceOffsetMask.leftFrame hp state e) ready
    obtain ⟨pre,post,W,T,P⟩ := ih (step state e) a k J (by omega) (by omega) (by omega) (closed _ q e) offset
      now new nominate
    exact ⟨e::pre,post,congrArg (List.cons e) W,.cons I E T,P⟩
  | @cons_cons ls w e sub ih =>
    intro state a j J A U later q ready I F nominate
    by_cases eqa : j=len
    · subst j
      exact ⟨[],e::w,rfl,.nil I,F⟩
    have jl : j<len := by omega
    obtain ⟨k,jk,K,E,now,new,served⟩ := arbitrary_postgate_step hp C Q fiber closed sep g G
      gateK gateH j jl later q ready e pay well I F
    have kA : a+1≤k := by
      by_cases same : a=j
      · subst a
        have link := nominate 0 (by simp) state (fiber state q)
        have eq := served (by simpa using link)
        omega
      · omega
    have nom' (t : Nat) (ht : t<ls.length) (y : X) (H : ∀ i,Layout B base i=Layout B y i) :
        linkAt hp y ls[t] (fun t=>S.getD t fall) len ((a+1)+t) := by
      have link := nominate (t+1) (by simp; omega) y H
      have eq : a+(t+1)=(a+1)+t := by omega
      simpa only [List.getElem_cons_succ,eq] using link
    have offset := stable hp _ hh state e (sep e)
      (fun i => (congrArg Prod.fst (fiber state q i)).symm)
      (BStarClearanceOffsetMask.leftFrame hp state e) ready
    obtain ⟨pre,post,W,T,P⟩ := ih (step state e) (a+1) k (by simp at J; omega) kA (by omega) (by omega)
      (closed _ q e) offset now new nom'
    exact ⟨e::pre,post,congrArg (List.cons e) W,.cons I E T,P⟩

end L4.BStarBitPostGateReplay
