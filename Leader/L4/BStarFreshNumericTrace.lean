import Leader.L4.BStarFreshNumericFrame

/-! Forward payload and return safety on every prefix of a literal
numeric itinerary, with the operand-tag premise isolated. -/
namespace L4.BStarFreshNumericTrace
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongEvents BStarLongCommand
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace
open BStarResetChartTouch BStarAcquireLiteralChain BStarResetMarkAdapter BStarResetRailRing
open BStarResetChartService BStarSeparatingRail BStarSeparatorControl
open BStarFreshNumeric BStarFreshNumericFrame BStarNumericReturn BStarNumericReceipt
open BStarOwnerLaunchOrigin BStarResetSchedule

def HealthAt (op : Nat) (rail : BStarSeparatingRail.Rail) : Cursor → Prop
  | .out k => ∃ p, rail k=.forward p ∧ Healthy p ∧ p.opcode.toNat=op
  | .back k => ∃ p, rail k=.reply p ∧ Stable p ∧ p.opcode.toNat=op

variable {k₁ k₂ t₂ J₁ J₂ r c pmod c₁ n : Nat} (hp : 0<pmod)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c pmod c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c pmod c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

theorem mark_health {base x : X} {hh : ∃ z,oldH6 B base z=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (he : e≠rightNeighbor e) (op : Nat)
    (W : Waiting hp base (S.getD 0 fall).1 op x)
    (z d : Cursor) (A : Advance len z d)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) z)
    (J : Good anyTag len (project (fun j => S.getD j fall) (step x e)) d)
    (H : HealthAt op (project (fun j => S.getD j fall) x) z)
    (D : ∀ k, z=.out k → (S.getD k fall).2.val=1 →
      (longGeometry B (x (S.getD k fall).1)).inside=true → operands (x (S.getD k fall).1).long)
    (hold : z=.back 0 → e≠RearTrace.predecessor (S.getD 0 fall).1) :
    HealthAt op (project (fun j => S.getD j fall) (step x e)) d := by
  classical
  let addr := fun j => S.getD j fall
  let U := project addr x
  let V := project addr (step x e)
  change HealthAt op U z at H
  change HealthAt op V d
  have depart {k : Nat} (p : Payload) (F : U k=.forward p) (Hp : Healthy p)
      (G : Good anyTag len U (.out k)) (L : linkAt hp x e addr len k) :
      V k=.trail := ring_link_trail hp chart e he op k W G p F Hp L
  cases A with
  | stay =>
    cases z with
    | out k =>
      obtain ⟨p,F,Hp,Op⟩ := H
      obtain ⟨q,Q⟩ := J.2.1
      have nolink : ¬linkAt hp x e addr len k := by
        intro L
        have Hout := depart p F Hp G L
        exact Token.noConfusion (Q.symm.trans Hout)
      have noturn : k=len → ¬onTerminal hp x e addr len := by
        intro E T
        subst k
        have Hout := ring_turn hp e he T p F Hp
        exact Token.noConfusion (Q.symm.trans Hout)
      exact ⟨p,ring_hold hp chart e he op k W G p F Hp nolink noturn,Hp,Op⟩
    | back k =>
      obtain ⟨p,F,Hp,Op⟩ := H
      cases k with
      | zero =>
        exact ⟨p,arrived_payload hp chart W.1 e he (hold rfl) p Hp ⟨G.2.1,G.2.2.2⟩ F,Hp,Op⟩
      | succ k =>
        have R := reverse_or_hold hp chart e he op k W p Hp G F
        change (if linkAt hp x e addr len k then V k=.reply p ∧ V (k+1)=.empty else V (k+1)=.reply p) at R
        split at R
        · have T := J.2.2.1 k (by omega)
          exact Token.noConfusion (R.1.symm.trans T)
        · exact ⟨p,R,Hp,Op⟩
  | forward k =>
    obtain ⟨p,F,Hp,Op⟩ := H
    have lt : k<len := by have v := J.1; omega
    have L : linkAt hp x e addr len k := by
      by_cases h : linkAt hp x e addr len k
      · exact h
      · have Hout := ring_hold hp chart e he op k W G p F Hp h (by omega)
        exact Token.noConfusion (Hout.symm.trans (J.2.2 k (by omega)))
    obtain ⟨q,E,Hq,Oq⟩ := ring_link hp e he L p F Hp (D k rfl)
    exact ⟨q,E,Hq,(congrArg BitVec.toNat Oq).trans Op⟩
  | turn =>
    obtain ⟨p,F,Hp,Op⟩ := H
    have L : ¬linkAt hp x e addr len len := fun h => (Nat.lt_irrefl _ h.1)
    have T : onTerminal hp x e addr len := by
      by_cases h : onTerminal hp x e addr len
      · exact h
      · have Hout := ring_hold hp chart e he op len W G p F Hp L (fun _ => h)
        obtain ⟨q,Q⟩ := J.2.1
        exact Token.noConfusion (Hout.symm.trans Q)
    exact ⟨output p,ring_turn hp e he T p F Hp,⟨Hp.numeric.1,fun g j => output_bind g j p Hp.numeric⟩,Op⟩
  | reverse k =>
    obtain ⟨p,F,Hp,Op⟩ := H
    have R := reverse_or_hold hp chart e he op k W p Hp G F
    change (if linkAt hp x e addr len k then V k=.reply p ∧ V (k+1)=.empty else V (k+1)=.reply p) at R
    split at R
    · exact ⟨p,R.1,Hp,Op⟩
    · have high : k+1≤len := G.1
      have Hout := J.2.2.2 (k+1) (by omega) high
      exact Token.noConfusion (R.symm.trans Hout)

/-- The old physical data condition sufficient for numeric safety. It
says nothing about the resulting controller or packet. -/
def OperandTape (addr : Nat → Pos n) (len : Nat) (x : X) (w : List (Fin n)) : Prop :=
  ∀ u e v, w=u++e::v → ∀ k≤len,
    let y := BStarResetSchedule.run step x u
    (addr k).2.val=1 → (longGeometry B (y (addr k).1)).inside=true → operands (y (addr k).1).long

/-- At every prefix of an actual busy numeric tour the pointed packet
is healthy and has the original opcode, including the precise return.
The only new environmental premise is old-marks retained input tags. -/
theorem busy_prefix_health {base x : X} {hh : ∃ b,oldH6 B base b=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {w : List (Fin n)} {z d : Cursor}
    (T : BusyOnly hp base (fun j => S.getD j fall) len op x z w d)
    (D : OperandTape hp (fun j => S.getD j fall) len x w)
    (H : HealthAt op (project (fun j => S.getD j fall) x) z) :
    HealthAt op (project (fun j => S.getD j fall) (BStarResetSchedule.run step x w)) d ∧
    ∀ u v, w=u++v → ∃ cursor,
      BusyOnly hp base (fun j => S.getD j fall) len op x z u cursor ∧
      BusyOnly hp base (fun j => S.getD j fall) len op (BStarResetSchedule.run step x u) cursor v d ∧
      HealthAt op (project (fun j => S.getD j fall) (BStarResetSchedule.run step x u)) cursor := by
  induction T with
  | nil I =>
    refine ⟨H,?_⟩
    intro u v e
    obtain ⟨U,V⟩ := List.append_eq_nil_iff.mp e.symm
    subst u
    subst v
    exact ⟨_,.nil I,.nil I,H⟩
  | @cons x z mid final e w I E tail ih =>
    have next := (busy_start hp tail).2.1
    have before := I.2.1
    have move : Advance len z mid := by
      cases E with
      | transit pc cur dest live h =>
        cases h with | cons _ _ A _ more => cases more; exact A
      | arrived_hold => exact .stay _
    have keep : z=.back 0 → e≠RearTrace.predecessor (S.getD 0 fall).1 := by
      intro eq
      cases E with
      | transit _ _ _ live _ => exact (live eq).elim
      | arrived_hold _ away => exact away
    have fresh := mark_health hp chart e (sep e) op I.1 z mid move before next H
      (fun k eq => D [] e w rfl k (by subst z; exact before.1)) keep
    have post : OperandTape hp (fun j => S.getD j fall) len (step x e) w := by
      intro u f v F k K
      exact D (e::u) f v (congrArg (List.cons e) F) k K
    obtain ⟨last,all⟩ := ih post fresh
    refine ⟨last,?_⟩
    intro u v U
    cases u with
    | nil =>
      simp only [List.nil_append] at U
      subst v
      exact ⟨_,.nil I,.cons I E tail,H⟩
    | cons f u =>
      obtain ⟨rfl,Q⟩ := List.cons.inj U
      obtain ⟨cursor,L,R,H⟩ := all u v Q
      exact ⟨cursor,.cons I E L,R,H⟩

#print axioms busy_prefix_health
#print axioms mark_health
end L4.BStarFreshNumericTrace
