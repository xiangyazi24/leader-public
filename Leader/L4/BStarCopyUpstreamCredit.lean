import Leader.L4.BStarCopyMarkedLedger

/-! Upstream count credit allows loss. Geometry and owner attribution
identify the actual line; a boundary hop may use only old credit. -/
namespace L4.BStarCopyUpstreamCredit
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongPackets BStarLongToken
open BStarLongPrep BStarLongCommandData BStarCopyFIFO BStarCopyInjection

structure Totals where
  arrivals : Nat
  upstream : Nat
  released : Nat

def Totals.Valid (t : Totals) : Prop := t.arrivals+t.upstream≤t.released

/-- A release increases stock and credit together; a crossing exchanges
one unit of old stock for one arrival. Other marks may lose stock. -/
inductive Step : Totals → Totals → Prop
  | release (t : Totals) : Step t ⟨t.arrivals,t.upstream+1,t.released+1⟩
  | cross (t : Totals) (occupied : 0<t.upstream) :
      Step t ⟨t.arrivals+1,t.upstream-1,t.released⟩
  | thin (t : Totals) (n : Nat) (loss : n≤t.upstream) :
      Step t ⟨t.arrivals,n,t.released⟩

theorem valid_step {t z : Totals} (before : t.Valid) (step : Step t z) : z.Valid := by
  cases step <;> unfold Totals.Valid at before ⊢ <;> dsimp only at * <;> omega

inductive Prefix : Totals → Prop
  | clear : Prefix ⟨0,0,0⟩
  | step {t z : Totals} : Prefix t → Step t z → Prefix z

theorem valid_prefix {t : Totals} (P : Prefix t) : t.Valid := by
  induction P with
  | clear => exact Nat.le_refl 0
  | step _ s ih => exact valid_step ih s

/-- The old occupied boundary sender pays for the arrival before
any release on this same mark is counted. -/
theorem before_cross {t : Totals} (P : Prefix t) (oldOccupied : 0<t.upstream) :
    t.arrivals<t.released := by
  have H := valid_prefix P
  unfold Totals.Valid at H
  omega

def mass (l : Lane) : Nat := if l.mobile=.empty then 0 else 1

def post (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : At Sheet) : Lane :=
  view (patchPair (patch g x) x) s

theorem mass_occupied (l : Lane) (h : l.mobile≠.empty) : mass l=1 := by simp [mass,h]

/-- Both ends of one selected nonretaining hop. Closed gates may
dispose of a tuple, so conservation is an inequality, not equality. -/
theorem local_nonretaining (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (u v : At Sheet) (c : DataClaim)
    (hs : c.source=u) (hd : c.destination=some v) (hh : c.kind=.hop)
    (sel : c∈orderedData g (reserved (round g x).prep)) (ne : u≠v)
    (keepNo : retains g v=false) :
    mass (post g x u)+mass (post g x v) ≤ mass (view x u)+mass (view x v) := by
  unfold post
  rw [sender_exact g x u v c hs hd hh sel ne,
    BStarLongCopyFence.receiver_exact g x u v c hs hd hh sel ne]
  by_cases su : (view x u).mobile=.empty
  · simp [hopEffects,su,typedLeaves]
  · by_cases gate : ((view x u).gate && (view x v).gate)=true
    · by_cases sv : (view x v).mobile=.empty
      · simp [hopEffects,su,sv,gate,keepNo,typedLeaves,Leaf.put,mass]
      · simp [hopEffects,su,sv,gate,typedLeaves]
    · simp [hopEffects,su,Bool.eq_false_iff.mpr gate,typedLeaves,Leaf.put,mass]

/-- A selected successful boundary hop spends exactly the old
source mobile. The newly received tuple is retained, not an
additional member of the upstream mobile stock. -/
theorem local_boundary_spend (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (u v : At Sheet) (c : DataClaim)
    (hs : c.source=u) (hd : c.destination=some v) (hh : c.kind=.hop)
    (sel : c∈orderedData g (reserved (round g x).prep)) (ne : u≠v)
    (openBoth : ((view x u).gate && (view x v).gate)=true)
    (occupied : (view x u).mobile≠.empty) (vacant : (view x v).mobile=.empty) :
    mass (view x u)=1 ∧ mass (post g x u)=0 := by
  refine ⟨mass_occupied _ occupied,?_⟩
  unfold post
  rw [sender_exact g x u v c hs hd hh sel ne]
  simp [hopEffects,openBoth,occupied,vacant,typedLeaves,Leaf.put,mass]

/-- The ambient full-mark count decomposes into the old sender
and the other upstream cells. The existence of this decomposition
for the joined row is an explicit environmental framing input. -/
theorem boundary_account {t : Totals} (others before after : Nat)
    (split : t.upstream=others+before) (spent : before=1 ∧ after=0) :
    Step t ⟨t.arrivals+1,others+after,t.released⟩ := by
  obtain ⟨rfl,rfl⟩ := spent
  have H : 0<t.upstream := by omega
  have E : others+0=t.upstream-1 := by omega
  rw [E]
  exact .cross t H

/-- Locally audited interior conservation, composed with the ambient
count of untouched lanes. Loss and service stutter remain allowed. -/
theorem interior_account {t : Totals} (other old new : Nat)
    (split : t.upstream=other+old) (noncreate : new≤old) :
    Step t ⟨t.arrivals,other+new,t.released⟩ :=
  .thin t _ (by omega)

/-- A literal winning INJECT adds exactly one unit to an empty source
slot. The prior module derives selection of this preparation from the
authenticated actual opcode and the same-lane exclusion. -/
theorem local_inject_gain (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (a : BStarLongPrep.Offer) (w : a∈(arbitration (round g x).prep).1)
    (isInject : a.claim.op=.inject) (data : BitVec 36)
    (enabled : (view x a.claim.lane).gate=true)
    (frozen : (view x a.claim.lane).frozen=.data data)
    (vacant : (view x a.claim.lane).mobile=.empty) :
    mass (view x a.claim.lane)=0 ∧ mass (post g x a.claim.lane)=1 := by
  refine ⟨by simp [mass,vacant],?_⟩
  unfold post
  rw [selected_prep_exact g x a w]
  simp [selectedEffects,isInject,effects,enabled,frozen,vacant,validPayload,typedLeaves,Leaf.put,mass]

theorem release_account {t : Totals} (others before after : Nat)
    (split : t.upstream=others+before) (gain : before=0 ∧ after=1) :
    Step t ⟨t.arrivals,others+after,t.released+1⟩ := by
  obtain ⟨rfl,rfl⟩ := gain
  have E : others+1=t.upstream+1 := by omega
  rw [E]
  exact .release t

/-- The upstream count proof discharges the old-credit premise of
the actual marked first-receiver adapter. The stock/count equations
refer to the very same old mark; no same-mark release is available. -/
theorem physical_first_from_credit {Label : Type} (digits : Label → BitVec 36)
    (plan : List Label) (s : BStarCopyMarkedLedger.Ledger Label)
    (pre : BStarCopyMarkedLedger.Prefix plan s) (tag : Label)
    (t : Totals) (account : Prefix t) (others : Nat)
    (aEq : t.arrivals=(s.cells 0).arrivals.length)
    (rEq : t.released=s.release.released.length)
    (g : Pair LongGeometry) (x : Pair (BitVec LW)) (u v : At Sheet) (c : DataClaim)
    (stock : t.upstream=others+mass (view x u))
    (hs : c.source=u) (hd : c.destination=some v) (hh : c.kind=.hop)
    (sel : c∈orderedData g (reserved (round g x).prep)) (ne : u≠v)
    (ret : retains g v=true) (gates : ((view x u).gate && (view x v).gate)=true)
    (input : (view x u).mobile=.data (digits tag))
    (R : Compatible digits (s.cells 0) (view x v)) (vacant : (s.cells 0).mobile=none) :
    let z := s.receiveFirst tag
    BStarCopyMarkedLedger.Prefix plan z ∧ Compatible digits (z.cells 0) (post g x v) := by
  have H : 0<t.upstream := by rw [stock]; simp [mass,input]
  have credit := before_cross account H
  rw [aEq,rEq] at credit
  exact BStarCopyMarkedLedger.physical_first digits plan s pre tag g x u v c hs hd hh sel
    ne ret gates input R vacant credit

end L4.BStarCopyUpstreamCredit
