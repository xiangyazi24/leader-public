import Leader.L4.BStarNumericWidth

/-! Health and fixed-opcode witnesses recovered from an actual successful outward tape. -/
namespace L4.BStarNumericHealthy
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongEvents BStarLongLiteral BStarLongRouting
open BStarAcquireVisitOrder BStarAcquireForwardTrace BStarH6WordChart BStarLongRegisters
open BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail BStarSeparatorControl
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetSchedule
open BStarLongArithmetic BStarNumericCarry BStarNumericConsecutive BStarNumericChronology
open BStarLongCommand BStarClearanceForward BStarNumericWidth
  BStarAcquireLiteralChain BStarResetChartTouch BStarResetQuiet

private theorem outgoing_back (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p q : Payload)
    (H : (BStarLongOutgoing.execute g j x p).carried=.forward q) :
    BStarForwardProvenance.Back p q := by
  intro F
  unfold BStarLongOutgoing.execute at H
  dsimp only at H
  repeat' first
    | (change (Token.forward p) = .forward q at H; cases H; exact ⟨F,rfl⟩)
    | (change fault false = .forward q at H; unfold fault at H; cases H; contradiction)
    | split at H
  cases H
  exact ⟨F,rfl⟩

private theorem visit_back (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) :
    BStarForwardProvenance.Back p (visit g j x p).2 := by
  unfold visit
  split
  · exact .refl _
  · split
    · exact .refl _
    · split
      · intro h
        contradiction
      · rename_i c _
        cases c <;> simp [physicalDigit,BStarForwardProvenance.Back] <;>
          split <;> simp

theorem selected_health (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (C : CommandClaim)
    (a : AtK) (p q : Payload)
    (R : arrive (geometry g a.side) a.occurrence (carried g raw C p)=.forward q)
    (H : Numeric q) :
    Numeric p ∧ p.opcode=q.opcode ∧
      (visit (geometry g C.source.side) C.source.occurrence (atOld raw C.source) p).2.fault=0 := by
  have carrier : (carried g raw C p).fault=0 ∧ (carried g raw C p).opcode=q.opcode := by
    unfold arrive at R
    split at R <;> cases R <;> exact ⟨H.1,rfl⟩
  unfold carried at carrier
  dsimp only at carrier
  split at carrier
  · rename_i u E
    obtain ⟨V,O⟩ := outgoing_back _ _ _ _ u E carrier.1
    obtain ⟨F,N⟩ := visit_back _ _ _ p V
    have Op := N.trans (O.trans carrier.2)
    exact ⟨⟨F,by rw [Op]; exact H.2.1,by rw [Op]; exact H.2.2⟩,Op,V⟩
  all_goals exact ((show (1 : BitVec 1)≠0 by decide) carrier.1).elim

theorem bound_width (g : LongGeometry) (j : Fin 11) (t : Token) (q : Payload)
    (R : BStarLongCommand.bind g j t=.forward q) (H : Numeric q) :
    q.race=0 ∧ q.outcome=0 ∧
      ∃ k, forwardWidth q.opcode.toNat q.argument.toNat=some k ∧ q.argument.toNat<2^k := by
  cases t with
  | empty => contradiction
  | trail => contradiction
  | reply u =>
    simp only [BStarLongCommand.bind] at R
    split at R <;> try (simp [fault] at R)
    split at R <;> simp at R
  | forward u =>
    let bad := u.fault != 0 || decide (u.opcode.toNat≥413) || u.outcome != 0 ||
      !(if gate u.opcode.toNat j g then decide (1≤u.race.toNat ∧ u.race.toNat≤5)
        else u.race.toNat==0)
    change (if bad then fault false else
      match forwardWidth u.opcode.toNat u.argument.toNat with
      | none => fault false
      | some w => .forward (cropped u w)) = .forward q at R
    by_cases V : bad=true
    · rw [if_pos V] at R
      cases R
      exact False.elim ((show (1 : BitVec 1)≠0 by decide) H.1)
    · rw [if_neg V] at R
      cases W : forwardWidth u.opcode.toNat u.argument.toNat with
      | none =>
        rw [W] at R
        cases R
        exact False.elim ((show (1 : BitVec 1)≠0 by decide) H.1)
      | some k =>
        rw [W] at R
        cases R
        have U : Numeric u := H
        have off := numeric_gate g j u U
        have RR : u.race=0 := by
          apply Classical.byContradiction
          intro E
          apply V
          have T : u.race.toNat ≠ 0 := fun Z => E (BitVec.eq_of_toNat_eq Z)
          simp [bad,off,T]
        have OO : u.outcome=0 := by
          apply Classical.byContradiction
          intro E
          apply V
          change u.outcome ≠ (0 : BitVec 2) at E
          simp [bad]
          exact Or.inl (Or.inr E)
        refine ⟨RR,OO,k,?_,?_⟩
        · change forwardWidth u.opcode.toNat (cropped u k).argument.toNat=some k
          rw [width_numeric U.2.1 U.2.2] at W ⊢
          cases E : arithKind u.opcode.toNat with
          | none => simpa only [E] using W
          | some a =>
            cases a <;> simp [E] at W ⊢ <;> try exact W
            obtain ⟨good,eq⟩ := W
            subst k
            have mod4 : (cropped u 2).argument.toNat % 4 = u.argument.toNat % 4 := by
              simp [cropped,low,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show u.argument.toNat % 4 < 17179869184 by omega)]
            exact ⟨mod4 ▸ good,rfl⟩
        · change (BitVec.ofNat 34 (u.argument.toNat % 2^k)).toNat<2^k
          rw [BitVec.toNat_ofNat]
          have M := Nat.mod_lt u.argument.toNat (Nat.two_pow_pos k)
          exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) M

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁) (J₂:=J₂)
  (r:=r) (c:=c) (p:=p) (c₁:=c₁)

theorem record_health {addr : Nat → Pos n} (d : D) (V : Departure.Valid hp addr d)
    (he : d.mark≠rightNeighbor d.mark) (q : Payload)
    (Q : project addr (step d.old d.mark) (d.index+1)=.forward q) (H : Numeric q) :
    Numeric d.offer ∧ d.offer.opcode=q.opcode ∧
      (visit (geom hp d) d.claim.source.occurrence (byte d) d.offer).2.fault=0 ∧
      d.offer.race=0 ∧ d.offer.outcome=0 ∧ ∃ k,
        forwardWidth d.offer.opcode.toNat d.offer.argument.toNat=some k ∧ d.offer.argument.toNat<2^k := by
  obtain ⟨sel,dst,_,endEq⟩ := V
  let x := d.old
  let e := d.mark
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have hm : d.claim∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have no := (BStarAcquireReturn.link_shape g d.claim d.destination hm dst).1
  have safe : d.destination=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : d.destination.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have N := (BStarAcquireJoinedHop.k0_dest g d.claim d.destination hm dst J).2
    simp [Z] at N
  have Jraw := (move_lands g raw d.claim d.offer d.destination dst sel (Ne.symm no)).2
  have E := (new_read B x e he d.destination).trans ((congrArg (atCursor (step x e)) endEq).symm)
  have DL := E.trans Q
  change decode (readRaw (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) d.destination)=_ at DL
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) d.destination safe,Jraw,decode_encode] at DL
  obtain ⟨P,O,F⟩ := selected_health g raw d.claim d.destination d.offer q DL H
  have W := offer_exact g raw d.claim d.offer sel P
  exact ⟨P,O,F,bound_width _ _ _ _ W P⟩

theorem records_ready {base x : X} {hh : ∃ z,oldH6 B base z=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    {op k l : Nat} {w : List (Fin n)} {ds : List D}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : Aligned hp base (fun j => S.getD j fall) len op x k w l ds)
    (hl : l≤len) (pay : Payload)
    (F : project (fun j => S.getD j fall) (BStarResetSchedule.run step x w) l=.forward pay)
    (P : Numeric pay) (i : Nat) (code : L4.Compiler.Native.Code)
    (N : nodeOf pay.opcode.toNat=some i) (K : get i=some code) :
    ∀ d∈ds.filter (significant hp base (fun j => S.getD j fall)),
    let q := (physicalDigit (geom hp d) (byte d) i code d.offer).2
    (Numeric d.offer ∧ nodeOf d.offer.opcode.toNat=some i ∧ q.fault=0) ∧
      (∀ g j, BStarLongCommand.bind g j (.forward q)=.forward q) := by
  induction T with
  | nil _ => simp
  | stay I E T ih => exact ih hl F
  | @hop x k e w l ds C a u I E V T ih =>
    intro d M
    obtain ⟨M,Sig⟩ := List.mem_filter.mp M
    rcases List.mem_cons.mp M with L|R
    · subst d
      have b := Aligned.busy hp T
      have current := busy_start hp b
      obtain ⟨j,hj,q,Q,hq,O⟩ := BStarOwnerLaunchOrigin.busy_origin hp chart sep b l hl pay F P.1
      have U := (BStarOwnerControlHistory.pointed_unique_forward _ len _
        current.2.1 current.2.2 j hj).mp ⟨q,Q⟩
      subst j
      have H : Numeric q := ⟨hq,by rw [O]; exact P.2.1,by rw [O]; exact P.2.2⟩
      obtain ⟨Num,Op,Hv,Race,Outcome,t,W,A⟩ :=
        record_health hp ⟨k,x,e,C,a,u⟩ V (sep e) q Q H
      have Node : nodeOf u.opcode.toNat=some i := by rw [Op,O,N]
      obtain ⟨one,inside⟩ := Aligned.record_significant hp (.hop I E V T) _
        (List.mem_cons_self) Sig
      rw [show C.source.occurrence = (1 : Fin 11) from Fin.ext one,
        visit_significant _ _ _ _ _ Num Node K inside] at Hv
      refine ⟨⟨Num,Node,Hv⟩,?_⟩
      intro g j
      obtain ⟨W',A',R',O'⟩ := digit_width _ _ i code u Num Node K t W A Hv
      exact slot_bind g j _ (digit_numeric _ _ _ _ _ Num Hv).1 (R'.trans Race) (O'.trans Outcome) t W' A'
    · exact ih hl F d (List.mem_filter.mpr ⟨R,Sig⟩)

/-- The selected digit sweep of an actual successful outward numeric
tour, including live bank projections. Every health/width witness is
derived from the raw busy trace and its healthy terminal forward. -/
theorem successful_sweep {base x : X} {hh : ∃ z,oldH6 B base z=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    {op k l : Nat} {w : List (Fin n)}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : BusyOnly hp base (fun j => S.getD j fall) len op x (.out k) w (.out l))
    (hl : l≤len) (pay : Payload)
    (F : project (fun j => S.getD j fall) (BStarResetSchedule.run step x w) l=.forward pay)
    (P : Numeric pay) (i : Nat) (code : L4.Compiler.Native.Code)
    (N : nodeOf pay.opcode.toNat=some i) (K : get i=some code) :
    ∃ ds : List D, Aligned hp base (fun j => S.getD j fall) len op x k w l ds ∧
    let visits := ds.filter (significant hp base (fun j => S.getD j fall))
    let digit := fun d : D => physicalDigit (geom hp d) (byte d) i code d.offer
    let updated := fun d : D => (digit d).1.apply (byte d)
    ∃ tokens : Nat → Payload,
      (∀ j : Fin visits.length, tokens j.val=visits[j.val].offer) ∧
      BStarPhysicalWordSem.DigitSweep
        (fun j : Fin visits.length => geom hp visits[j.val])
        (fun j : Fin visits.length => byte visits[j.val])
        (fun j : Fin visits.length => updated visits[j.val]) i code tokens ∧
      ∀ j : Fin visits.length, ∀ reg,
        (numeric reg).read (byte visits[j.val])=(numeric reg).read (x visits[j.val].mark).long ∧
        (numeric reg).read (updated visits[j.val]) =
          (numeric reg).read ((BStarResetSchedule.run step x w) visits[j.val].mark).long := by
  obtain ⟨ds,A⟩ := aligned_tape hp chart sep T k l pay rfl rfl hl F P.1
  have W := records_ready hp chart sep A hl pay F P i code N K
  exact ⟨ds,A,BStarNumericWordFrame.live_sweep hp chart A sep i code K
    (fun d M => (W d M).1) (fun d M => (W d M).2)⟩

end L4.BStarNumericHealthy
