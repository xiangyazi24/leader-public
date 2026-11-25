import Leader.L4.BStarCopyCleanupFrame

namespace L4.BStarCopyCleanupWindow
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongPrep BStarLongPackets
open BStarH6WordChart BStarLongFixedRouting BStarResetChartTouch BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarAcquireAnchors BStarClearanceDataChart
open BStarResetMarkAdapter BStarGeneratedOwner BStarGeneratedBandScan BStarOwnerLaunchOrigin
open BStarCopyCleanupFrame BStarCopyCleanupCoverage BStarCopyEntryGates BStarCopyGateAuthority

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem fold_hold (x : X) (w : List (Fin n)) (P : X→Prop) (old : P x)
    (hold : ∀ q e t,w=q++e::t → P (play x q) → P (step (play x q) e)) :
    P (play x w) := by
  induction w generalizing x with
  | nil => exact old
  | cons e t ih =>
    exact ih (step x e) (hold [] e t rfl old)
      (fun q f u E => hold (e::q) f u (congrArg (List.cons e) E))

private theorem hold_after {x : X} {w : List (Fin n)} (P : X→Prop)
    (q : List (Fin n)) (e : Fin n) (t : List (Fin n)) (split : w=q++e::t)
    (post : P (step (play x q) e))
    (hold : ∀ a z b,w=a++z::b → P (play x a) → P (step (play x a) z)) : P (play x w) := by
  rw [split,BStarResetSchedule.run_append]
  apply fold_hold hp _ _ P post
  intro a z b E
  have W : w=(q++e::a)++z::b := by rw [split,E]; simp [List.append_assoc]
  rw [show play (step (play x q) e) a=play x (q++e::a) from by rw [BStarResetSchedule.run_append]; rfl]
  exact hold (q++e::a) z b W

def ClosedOwner (base x : X) (o : Int) : Prop :=
  ∀ i sh, activeSheet (longGeometry B (x i)) sh=true →
    dataOwner (oldH6 B base) i sh=o → (readLane (Sheet.index sh) (x i).long).gate=false

def DrainedOwner (base x : X) (o : Int) : Prop :=
  ∀ i sh, activeSheet (longGeometry B (x i)) sh=true →
    dataOwner (oldH6 B base) i sh=o → Drained (readLane (Sheet.index sh) (x i).long)

/-- One genuine STOP tour closes every active owner gate. No ordering
between the per-lane STOP visits or foreign marks is presupposed. -/
theorem stopped {base y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (tour tail : List (Fin n))
    (out : BusyOnly hp base (fun j => S.getD j fall) len 6 y (.out 0) tour (.out len))
    (pay : Payload) (atEnd : project (fun j => S.getD j fall) (play y tour) len=.forward pay)
    (healthy : pay.fault=0) (op : pay.opcode.toNat=6)
    (layout : ∀ i, Layout B base i=Layout B (play y (tour++tail)) i)
    (noEnable : ∀ a e b,tour++tail=a++e::b → ∀ q∈
      (arbitration (round (oldPair B (play y a) e)
        (((play y a) e).long,((play y a) (rightNeighbor e)).long)).prep).1,
      dataOwner (oldH6 B base) (site e q.claim.lane.side) q.claim.lane.occurrence=o.val →
      q.claim.op≠.enable) :
    ClosedOwner hp base (play y (tour++tail)) o.val := by
  intro i sh act own
  have active : activeSheet (longGeometry B (base i)) sh=true := by
    have E := congrArg (fun t : Bool×Bool×Bool => t.2.1) (layout i)
    cases sh <;> first | rfl | exact E.trans act
  obtain ⟨a,e,b,q,W,Q,I,Sh,win⟩ :=
    outward_cleanup hp chart sep .stop rfl (.inl rfl) (by decide)
      out pay atEnd healthy op i sh active own
  have stopped := ring_stop hp (play y a) e (sep e) q (.inl Q) win
  dsimp only at stopped
  rw [I,Sh] at stopped
  apply hold_after (hp:=hp) (x:=y) (w:=tour++tail)
    (fun z => (readLane (Sheet.index sh) (z i).long).gate=false) a e (b++tail)
  · rw [W]; simp [List.append_assoc]
  · rw [stopped]
  · intro u z v E old
    exact ring_closed hp _ z i sh (sep z) old (fun r R J K =>
      noEnable u z v E r R (by rwa [J,K]))

/-- One genuine CLEAR tour drains mobile and retained bytes on every
active owner lane, provided the owner gates are closed on that tape. -/
theorem cleared {base y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (tour tail : List (Fin n))
    (out : BusyOnly hp base (fun j => S.getD j fall) len 7 y (.out 0) tour (.out len))
    (pay : Payload) (atEnd : project (fun j => S.getD j fall) (play y tour) len=.forward pay)
    (healthy : pay.fault=0) (op : pay.opcode.toNat=7)
    (layout : ∀ a b,tour++tail=a++b → ∀ i, Layout B base i=Layout B (play y a) i)
    (closed : ∀ a e b,tour++tail=a++e::b → ClosedOwner hp base (play y a) o.val)
    (noInject : ∀ a e b,tour++tail=a++e::b → NoOwnerInject hp base (play y a) e o.val) :
    DrainedOwner hp base (play y (tour++tail)) o.val := by
  intro i sh act own
  have baseAct : activeSheet (longGeometry B (base i)) sh=true := by
    have E := congrArg (fun t : Bool×Bool×Bool => t.2.1) (layout _ [] (List.append_nil _).symm i)
    cases sh <;> first | rfl | exact E.trans act
  obtain ⟨a,e,b,q,W,Q,I,Sh,win⟩ :=
    outward_cleanup hp chart sep .clear rfl (.inr rfl) (by decide)
      out pay atEnd healthy op i sh baseAct own
  have clear := ring_clear hp (play y a) e (sep e) q (.inl Q) win
  dsimp only at clear
  rw [I,Sh] at clear
  apply hold_after (hp:=hp) (x:=y) (w:=tour++tail)
    (fun z => Drained (readLane (Sheet.index sh) (z i).long)) a e (b++tail)
  · rw [W]; simp [List.append_assoc]
  · rw [clear]; exact ⟨rfl,rfl⟩
  · intro u z v E old
    have A : activeSheet (longGeometry B (play y u i)) sh=true := by
      have eq := congrArg (fun t : Bool×Bool×Bool => t.2.1) (layout u (z::v) E i)
      cases sh <;> first | rfl | exact eq.symm.trans baseAct
    exact ring_drained hp _ z i sh (sep z) old
      (fun r R J K => noInject u z v E r R (by rwa [J,K]))
      (.inl (closed u z v E i sh A own))

end L4.BStarCopyCleanupWindow
