import Leader.L4.BStarAcquireReturn
import Leader.L4.AllSizeS1Geometry
import Leader.L4.BStarDoorUnique

namespace L4.BStarAcquireDoorHistory
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongWork BStarLongEvents BStarLongCommandData
open BStarAcquireReturn

/-- The same selected reverse command that installs its reply also
erases the old reply. No normalization or observer can overwrite
this clear, regardless of raw scratch at either endpoint. -/
theorem reverse_consumes (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (d : AtK) (t : Token)
    (hd : C.destination=some d) (h : (C,.reverse t)∈gated g x) :
    readK (patchPair (longWork g x) x) d=.empty := by
  have H : (C,.reverse t)∈actualOffers g x := by
    unfold actualOffers BStarLongGrant.run
    dsimp only
    apply List.mem_map.mpr
    refine ⟨(C,.reverse t),?_,?_⟩
    · change (C,.reverse t)∈(gated g x).map (cancel (round g x).faults)
      exact List.mem_map.mpr ⟨(C,.reverse t),h,rfl⟩
    · unfold BStarLongGrant.update
      dsimp only
      split <;> rfl
  apply last_selected_lands g x C (.reverse t) d .empty [(C.source,t)] [] H
  · simp [selected,direct,hd]
  · simp

theorem joined_reverse_consumes (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (d : AtK) (pay : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g → C.destination=some d →
    readK raw C.source=.trail → readK raw d=.reply pay → ValidReply pay →
    readK (Pair.map LargeSite.long (largePair b x)) C.source=.reply pay ∧
    readK (Pair.map LargeSite.long (largePair b x)) d=.empty := by
  dsimp only
  intro hc hd hsrc hdst hv
  refine ⟨raw_reverse_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C d pay hc hd hsrc hdst hv,?_⟩
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have safe : d.side=.right → d.occurrence.val=0 →
      g.2.axes.h6=false ∨ LongDoorGuard.valid manifest raw.2=true :=
    fun _ hz => .inl (BStarAcquireJoinedHop.k0_dest g C d hc hd hz).2
  rw [joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x d safe]
  exact reverse_consumes g raw C d (.reply pay) hd (reverse_checked g raw C d pay hc hd hsrc hdst hv)

abbrev SiteAddr (n : Nat) := Fin n × Fin 11
def siteOf {n : Nat} (e : Fin n) (s : Side) : Fin n :=
  if s=.left then e else rightNeighbor e

def addr {n : Nat} (e : Fin n) (a : AtK) : SiteAddr n :=
  (siteOf e a.side,a.occurrence)

def readSite {n : Nat} (x : Fin n → BitVec LW) (q : SiteAddr n) : Token :=
  atSite (x q.1) q.2

theorem read_pair {n : Nat} (x : Fin n → BitVec LW) (e : Fin n) (q : AtK) :
    readSite x (addr e q)=readK (x e,x (rightNeighbor e)) q := by
  obtain ⟨s,j⟩ := q
  cases s <;> rfl

theorem read_post_pair {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (e : Fin n) (q : AtK) (hne : rightNeighbor e≠e) :
    let y := largePair b (x e,x (rightNeighbor e))
    AllSizeS1Geometry.step b x e (siteOf e q.side)=
      (if q.side=.left then y.1 else y.2) := by
  cases h : q.side <;> simp [siteOf,AllSizeS1Geometry.step,hne]

/-- At each nominated reverse hop the genuine old carrier is consumed
and the new carrier reads the same reply in the physical ring. The
edge and its forwarding claim are explicit witnesses; equal bytes
elsewhere are not a lineage rule. -/
theorem ring_reverse (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    {n : Nat} (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e : Fin n) (hne : rightNeighbor e≠e) (C : CommandClaim) (d : AtK) (pay : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let pair := (x e,x (rightNeighbor e))
    let g := Pair.map (longGeometry b) pair
    let old := fun i => (x i).long
    let new := fun i => (AllSizeS1Geometry.step b x e i).long
    C∈orderedCommands g → C.destination=some d →
    readSite old (addr e C.source)=.trail →
    readSite old (addr e d)=.reply pay → ValidReply pay →
    readSite new (addr e C.source)=.reply pay ∧ readSite new (addr e d)=.empty := by
  dsimp only
  intro hc hd hsrc hdst hv
  let xRaw : Fin n → BitVec LW := fun i => (x i).long
  have hs := (read_pair xRaw e C.source).symm.trans hsrc
  have hdRaw := (read_pair xRaw e d).symm.trans hdst
  have H := joined_reverse_consumes k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) C d pay hc hd hs hdRaw hv
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  have B (a : AtK) : readSite (fun i => (AllSizeS1Geometry.step b x e i).long) (addr e a)=
      readK (Pair.map LargeSite.long (largePair b (x e,x (rightNeighbor e)))) a := by
    obtain ⟨s,j⟩ := a
    change atSite (AllSizeS1Geometry.step b x e (siteOf e s)).long j=_
    rw [read_post_pair b x e ⟨s,j⟩ hne]
    cases s <;> rfl
  rw [B C.source,B d]
  exact H

theorem ring_untouched {n : Nat} {a : LargeParams} (b : LargeRows a) (x : Fin n→LargeSite a)
    (e i : Fin n) (h1 : i≠e) (h2 : i≠rightNeighbor e) :
    AllSizeS1Geometry.step b x e i=x i := by simp [AllSizeS1Geometry.step,h1,h2]

/-- A marked source incoming edge reads exactly its original right K0.
No reply from any other action in this pair can enter the source door
on this mark. The caller separately authenticates the old carrier. -/
theorem source_reply_decision (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (pay : Payload) (hh : g.2.axes.h6=true)
    (hv : LongDoorGuard.valid manifest raw.2=true)
    (phase : (BStarLongDoor.ctrlPhase.read raw.2).toNat=2)
    (op : (BStarLongDoor.ctrlOp.read raw.2).toNat=acquire)
    (k0 : readK raw (R 0)=.reply pay) (H : ValidReply pay) :
    (actualOffers g raw).filter BStarDoorUnique.doorAction =
      [(BStarCommitIssue.doorClaim,.door (.reply pay))] ∧
    BStarLongDoor.oldDoor raw.2 (.reply pay)=.write (BStarLongDoor.afterReply acquire pay raw.2) := by
  constructor
  · have E := BStarDoorUnique.actual_door_singleton g raw hh
    change atSite raw.2 0=.reply pay at k0
    rw [k0,valid_reply_binding _ _ _ H] at E
    exact E
  · simp [BStarLongDoor.oldDoor,hv,phase,op,H.1,H.2.1,arithKind,acquire]

/-- The word observer does not infer lineage from a matching payload.
Each hop carries a named physical source and destination and consumes
the exact old occurrence. Exterior raw edges can pad the word without
altering the named address. -/
def chosenOn {a : LargeParams} {n : Nat} (b : LargeRows a) (x : Fin n → LargeSite a)
    (e : Fin n) (C : CommandClaim) (d : AtK) : Prop :=
  rightNeighbor e≠e ∧
    C∈orderedCommands (Pair.map (longGeometry b) (x e,x (rightNeighbor e))) ∧
    C.destination=some d

inductive Trace {α : Type} {n : Nat} (next : α → Fin n → α)
    (read : α → SiteAddr n → Token) (chosen : α → Fin n → CommandClaim → AtK → Prop)
    (pay : Payload) : α → SiteAddr n → List (Fin n) → α → SiteAddr n → Prop
  | nil (x a) : Trace next read chosen pay x a [] x a
  | stay (x a e w y b) (noTouch : a.1≠e ∧ a.1≠rightNeighbor e)
      (hold : read (next x e) a=read x a)
      (suffix : Trace next read chosen pay (next x e) a w y b) :
      Trace next read chosen pay x a (e::w) y b
  | hop (x e w y b) (C : CommandClaim) (d : AtK)
      (actual : chosen x e C d)
      (trail : read x (addr e C.source)=.trail)
      (clear : read (next x e) (addr e d)=.empty)
      (land : read (next x e) (addr e C.source)=.reply pay)
      (suffix : Trace next read chosen pay (next x e) (addr e C.source) w y b) :
      Trace next read chosen pay x (addr e d) (e::w) y b

theorem Trace.reply {α : Type} {n : Nat} {next : α → Fin n → α}
    {read : α → SiteAddr n → Token} {chosen : α → Fin n → CommandClaim → AtK → Prop}
    {pay : Payload} {x y : α} {a b : SiteAddr n} {w : List (Fin n)}
    (T : Trace next read chosen pay x a w y b) (old : read x a=.reply pay) :
    read y b=.reply pay := by
  induction T with
  | nil => exact old
  | stay _ _ _ _ _ _ _ H _ ih => exact ih (H.trans old)
  | hop _ _ _ _ _ _ _ _ _ _ H _ ih => exact ih H

theorem trace_hop_bStar (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    {n : Nat} (x : Fin n→LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e : Fin n) (C : CommandClaim) (d : AtK) (pay : Payload) (hv : ValidReply pay) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let read := fun (y : Fin n→LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)) =>
      readSite (fun i => (y i).long)
    chosenOn b x e C d →
    read x (addr e C.source)=.trail →
    read x (addr e d)=.reply pay →
    Trace (AllSizeS1Geometry.step b) read (chosenOn b) pay
      x (addr e d) [e] (AllSizeS1Geometry.step b x e) (addr e C.source) := by
  dsimp only
  intro H S D
  have E := ring_reverse k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x e H.1 C d pay H.2.1 H.2.2 S D hv
  exact .hop _ _ _ _ _ C d H S E.2 E.1 (.nil _ _)

end L4.BStarAcquireDoorHistory
