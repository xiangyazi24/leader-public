import Leader.L4.BStarSerialGeneratedEvent
import Leader.L4.BStarResetHealthyCycle

namespace L4.BStarSerialResetHealth
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongDoor BStarLongCommand
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors
open BStarGeneratedOwner BStarSeparatingRail BStarSeparatorControl
open BStarResetChartTouch BStarResetChartService BStarLongFixedRouting BStarAcquireForwardTrace BStarAcquireWaitControl BStarAcquireLiteralChain
open BStarResetHealthyService BStarResetTaggedRows BStarResetMarkAdapter BStarResetSchedule
open BStarSerialGeneratedEvent
open BStarSerialTourDebt
open BStarLongEvents BStarResetQuiet BStarResetQuietTable BStarResetRailRing BStarLongLiteral
open BStarLongClaims BStarLongTransport BStarSeparatorIdleClass BStarResetChartTouch BStarAcquireRingFrame BStarResetIdleRing BStarK0Frame BStarAcquireNonRouting

theorem healthy_matches {op len : Nat} {u : BStarSeparatingRail.Rail} {a b : Cursor}
    (A : Good (healthyTag op) len u a) (D : Good anyTag len u b) : a=b := by
  cases a with
  | out i =>
    cases b with
    | out j =>
      by_cases E : i=j
      · rw [E]
      obtain ⟨p,P⟩ := D.2.1
      have F : u i=.forward (resetPayload op) := A.2.1
      rcases Nat.lt_or_gt_of_ne E with h|h
      · rw [D.2.2 i h] at F; cases F
      · rw [A.2.2 j h] at P; cases P
    | back j =>
      obtain ⟨p,P⟩ := D.2.1
      have F : u i=.forward (resetPayload op) := A.2.1
      rcases Nat.lt_trichotomy i j with h|h|h
      · rw [D.2.2.1 i h] at F; cases F
      · rw [h,P] at F; cases F
      · rw [D.2.2.2 i h A.1] at F; cases F
  | back i =>
    have R : u i=finish (resetPayload op) := A.2.1
    obtain ⟨p,P⟩ : anyTag.D (u i) := by
      rcases (show ∃ q, finish (resetPayload op)=.reply q by
        unfold finish resetPayload
        split <;> simp_all <;> repeat first | exact ⟨_,rfl⟩ | split) with ⟨q,hq⟩
      exact ⟨q,R.trans hq⟩
    cases b with
    | out j =>
      obtain ⟨q,Q⟩ := D.2.1
      rcases Nat.lt_trichotomy i j with h|h|h
      · have Eq := A.2.2.2 j (by omega) D.1
        rw [Eq] at Q; cases Q
      · rw [h,Q] at P; cases P
      · rw [A.2.2.1 j h] at Q; cases Q
    | back j =>
      by_cases E : i=j
      · rw [E]
      obtain ⟨q,Q⟩ := D.2.1
      rcases Nat.lt_or_gt_of_ne E with h|h
      · rw [D.2.2.1 i h] at P; cases P
      · rw [A.2.2.1 j h] at Q; cases Q

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

def ResetHealthy (addr : Nat→Pos n) (len : Nat) (x : X) : Mode→Prop
  | .idle => True
  | .busy op z => op<3 → Good (healthyTag op) len (project addr x) z

private theorem arrived_healthy_eq {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (same : ∀ i, Layout B base i=Layout B x i)
    (e : Fin n) (he : e≠rightNeighbor e) (away : e≠RearTrace.predecessor (S.getD 0 fall).1)
    (J : Clean (project (fun j=>S.getD j fall)) anyTag len x)
    (live : BStarResetIdleRing.ResetLive (project (fun j=>S.getD j fall) x 0)) :
    let addr := fun j=>S.getD j fall
    project addr (step x e) 0=project addr x 0 := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let y := step x e
  have R : root≠rightNeighbor e := fun r => away
    ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor r.symm))
  have Hh := root_header hp C same
  by_cases E : root=e
  · have hit : addr 0=address e (L 0) := Prod.ext E Hh.2
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    have mid : avoids (L 0) (middle g raw) := by
      apply middle_avoids_of_chart
      intro v hv ha
      have mc : v.1∈orderedCommands g := by
        rw [←actualOffers_claims g raw]
        exact List.mem_map.mpr ⟨v,hv,rfl⟩
      rcases touches hp C same e 0 (Nat.zero_le _) v.1 (L 0) mc ha hit with D|T|L|⟨i,U,_⟩
      · cases D.2.2
      · obtain ⟨Eq,k,hk,_,_,idx,H⟩ := T
        have val := congrArg (fun z : Pos n => z.2.val) (hit.symm.trans (Eq ▸ H))
        exact (by change 0=k.source.occurrence.val at val; omega : False).elim
      · obtain ⟨lim,k,d,hk,hd,src,dst⟩ := L
        have eq := address_inj e he (hit.symm.trans src)
        have old (j : Nat) (a : AtK) (h : addr j=address e a) :
            readK raw a=project addr x j :=
          (old_read x e a).trans ((congrArg (atCursor x) h).symm)
        obtain ⟨pay,dp⟩ := J.1
        have D' := (old 0 k.source src).trans dp
        have E' := (old 1 d dst).trans (J.2 1 (by decide) (by omega))
        have Lh : LinkHold (bound g (readK raw) k.source) (bound g (readK raw) d) := by
          unfold bound
          rw [D',E']
          obtain ⟨p,Bd⟩ := bound_D (geometry g k.source.side) k.source.occurrence pay
          rw [Bd]
          exact .de p
        have H := link_avoids g raw k d hk (BStarAcquireReturn.link_shape g k d hk hd).2.1 hd Lh
        exact fun w hw heq => H.1 w (List.mem_flatMap.mpr ⟨v,hv,hw⟩) (heq.trans eq)
      · omega
    have old : readK raw (L 0)=project addr x 0 :=
      (old_read x e _).trans ((congrArg (atCursor x) hit).symm)
    have new : readK (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) (L 0)
        =project addr y 0 :=
      (new_read B x e he _).trans ((congrArg (atCursor y) hit).symm)
    exact new.symm.trans ((BStarResetIdleRing.joined_idle k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) (L 0) (Or.inr (old.symm ▸ live)) 
      (not_discarded hp C same e 0 (Nat.zero_le _) _ hit) mid (safe_nonright _ _ _ (by decide))).trans old)
  · have paid : y root=x root := by simp only [y,AllSizeS1Geometry.step,if_neg E,if_neg R]
    exact congrArg (fun q : LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁) => atSite q.long (addr 0).2) paid

theorem reset_healthy_step {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) {e : Fin n} {a b : Mode}
    (sep : e≠rightNeighbor e) (layout : ∀ i, Layout B base i=Layout B x i)
    (I : Current hp base (fun j=>S.getD j fall) len x a)
    (J : Current hp base (fun j=>S.getD j fall) len (step x e) b)
    (E : Event hp (fun j=>S.getD j fall) len x e a b)
    (H : ResetHealthy (fun j=>S.getD j fall) len x a) :
    ResetHealthy (fun j=>S.getD j fall) len (step x e) b := by
  let adr := fun j=>S.getD j fall
  cases E with
  | idle_hold _ => trivial
  | bad_issue _ _ => trivial
  | consume _ _ _ => trivial
  | launch own _ =>
    intro low
    obtain ⟨hdr,k⟩ := BStarResetChartService.root_header hp C layout
    have R : rightNeighbor e=(adr 0).1 := own ▸ RearTrace.right_predecessor _
    have G := BStarResetCycle.genuine_wait hp x e sep (pc x (adr 0).1) low
      (R.symm ▸ hdr) (R.symm ▸ I.1.2) (R.symm ▸ rfl)
    have P := G.1
    rw [R] at P
    change (step x e |> fun y => atCursor y ((adr 0).1,0)) =
        .forward (resetPayload (pc x (adr 0).1)) at P
    exact ⟨Nat.zero_le _,(congrArg (atCursor (step x e))
      (show adr 0=((adr 0).1,0) from Prod.ext rfl k)).trans P,fun j hj => (Nat.not_lt_zero j hj).elim⟩
  | transit op z d live _ =>
    intro low
    have g := H low
    obtain ⟨j,_,G⟩ := lift_mark (healthyService hp C layout e sep op low z live g I.1.2.1 I.1.2.2.1).mark z live g
    exact healthy_matches G J.2.1 ▸ G
  | arrived_hold op away =>
    intro low
    obtain ⟨D,_⟩ := arrived_nonown hp C layout e sep away ⟨I.2.1.2.1,I.2.1.2.2.2⟩
    have G := H low
    exact ⟨Nat.zero_le _,(arrived_healthy_eq hp C layout e sep away ⟨I.2.1.2.1,I.2.1.2.2.2⟩ (by
      have eq : project adr x 0=finish (resetPayload op) := G.2.1
      rw [eq]
      exact .d _ (by
        rcases (show op=0 ∨ op=1 ∨ op=2 by omega) with rfl|rfl|rfl
        · exact .inl rfl
        · exact .inr (.inl rfl)
        · exact .inr (.inr (.inl rfl))))).trans G.2.1,fun j hj => (Nat.not_lt_zero j hj).elim,D.2⟩

/-- The next real consume of a generated reset has the canonical bound
reply, even after arbitrarily many non-owner marks at back-zero. -/
theorem bound_reset_reply {addr : Nat→Pos n} {len op : Nat} {x : X}
    (root : (addr 0).2=0) (H : ResetHealthy addr len x (.busy op (.back 0))) (lo : op<3)
    (f : Payload)
    (binds : bind (longGeometry B (x (addr 0).1)) 0 (atSite (x (addr 0).1).long 0)=.reply f) :
    f.fault=0 ∧ f.opcode.toNat=op := by
  have G := (H lo).2.1
  change atSite (x (addr 0).1).long (addr 0).2=finish (resetPayload op) at G
  rw [root] at G
  rw [G] at binds
  rcases (show op=0 ∨ op=1 ∨ op=2 by omega) with rfl|rfl|rfl
  all_goals
    rw [(bind_finish _ _ _ (by simp [ResetF])).1] at binds
    change Token.reply (resetPayload _)=.reply f at binds
    cases binds
    exact ⟨rfl,rfl⟩

/-- The same literal event pays or exits without an assumed matching-reset
reply: healthy ancestry supplies it from the actual chart and issued walk. -/
theorem event_debt_of_health {base x : X} {addr : Nat → Pos n} {len : Nat}
    {e : Fin n} {a b : Mode}
    (root : (addr 0).2=0) (hdr : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x a)
    (J : Current hp base addr len (step x e) b)
    (E : Event hp addr len x e a b)
    (H : ResetHealthy addr len x a) :
    let old := pc x (addr 0).1
    let new := pc (step x e) (addr 0).1
    (old=2 ∧ new=3 ∧ a=.busy 2 (.back 0) ∧ b=.idle) ∨
      toursLeft new+1≤toursLeft old ∨
      (new=old ∧ ¬ (∃ op, a=.busy op (.back 0) ∧ b=.idle) ∧
       ¬ (a=.idle ∧ b=.idle ∧ e=RearTrace.predecessor (addr 0).1)) := by
  apply event_debt hp root hdr sep I J E
  intro f matchA _ lo binds
  subst a
  exact bound_reset_reply hp root H lo f binds

/-- From an actual idle cut, any generated owner's word on an invariant
fixed chart leaves any outstanding reset packet healthy. No witness
schedule is substituted for the original scheduler word. -/
theorem reset_healthy_word {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop)
    (fiber : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y, Q y → ∀ e, Q (step y e))
    (sep : ∀ e : Fin n, e≠rightNeighbor e)
    {a b : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x a w b)
    (qx : Q x) (H : ResetHealthy (fun j=>S.getD j fall) len x a) :
    ResetHealthy (fun j=>S.getD j fall) len (BStarResetSchedule.run step x w) b := by
  induction T with
  | endpoint _ => exact H
  | next I E tail ih =>
    have J : Current hp base (fun j=>S.getD j fall) len (step _ _) _ := (by cases tail with
      | endpoint h => exact h
      | next h _ _ => exact h)
    exact ih (closed _ qx _) (reset_healthy_step hp C (sep _) (fiber _ qx) I J E H)

end L4.BStarSerialResetHealth
