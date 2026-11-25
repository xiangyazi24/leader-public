import Leader.L4.BStarCopyRightReleaseClass

namespace L4.BStarCopyRightInjectStep
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongPrep BStarLongCommandData BStarLongEvents BStarLongToken
open BStarLongDoor BStarCopyRightStrip BStarCopyRightRetained BStarCopyRightRetainedClassify
open BStarCopyRightMark BStarCopyRightDataSweep BStarCopyRightReady BStarCopyRightDeposit
open BStarCopyRightAuthority BStarCopyRightK2 BStarCopyRightK2Past BStarCopyRightMixed
open BStarCopyRightReleaseClass BStarCopyFIFO BStarCopyMarkedLedger BStarCopyFenceSaturation
open BStarClearanceDataChart BStarGeneratedBandScan BStarGeneratedOwner BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetChartIndex BStarSeparatingRail
open BStarAcquireForwardTrace BStarResetMarkAdapter BStarResetSchedule BStarSeparatorControl
open BStarCopyDownstream BStarClearancePhysical BStarClearanceMobileRing BStarCopyEntryGates

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

private theorem out_choices {len k : Nat} {d : Cursor}
    (lt : k<len) (A : Advance len (.out k) d) :
    d=.out k ∨ d=.out (k+1) := by
  cases A with
  | stay => exact .inl rfl
  | forward => exact .inr rfl
  | turn => exact (Nat.lt_irrefl _ lt).elim

/-- A classified selected release necessarily changes the actual old
cursor from k to k+1. A stay would leave forward at old K2, which
contradicts the literal old-source Trail. This proof does not assume
that injection writes data; even its error branch cannot repeat K2. -/
theorem release_advances {base x : X} {addr : Nat→Pos n} {len : Nat}
    {e baseAddr : Fin n} {seam tail : Nat} {m m' : Mode}
    (R : ReleaseAt hp x e baseAddr seam tail addr len m)
    (sep : e≠rightNeighbor e)
    (E : Event hp addr len x e m m')
    (next : Current hp base addr len (ring x e) m') :
    m'=.busy 10 (.out (R.k+1)) := by
  have ev := E
  rw [R.mode] at ev
  have shape : ∃ d, m'=.busy 10 d ∧ Advance len (.out R.k) d := by
    cases ev with
    | transit _ _ _ _ seen => exact ⟨_,rfl,single hp seen⟩
  obtain ⟨d,Nd,A⟩ := shape
  have after : Current hp base addr len (ring x e) (.busy 10 d) := Nd ▸ next
  have expect : d=.out (R.k+1) := by
    rcases out_choices R.strict A with stick|go
    · rw [stick] at after
      exfalso
      obtain ⟨c,f,source,act⟩ := R.advance
      have T := k2_departure_trail hp x e sep c f act (congrArg At.occurrence source)
      have A : address e c.source=addr R.k := by rw [R.ptr,source,←R.markAt]; rfl
      have forward := after.2.1.2.1
      change anyTag.F (atCursor (ring x e) (addr R.k)) at forward
      rw [←A,T] at forward
      exact (BStarSeparatorParked.forward_not_trail forward).elim
    · exact go
  exact Nd.trans (congrArg (Mode.busy 10) expect)

/-- Physical mark ledger transition in the original PC10 epoch.
Nonrelease is derived from actual prep provenance, not supplied.
On a genuine release, CutVacant is derived from owner-empty ISSUE10
and its own unvisited chart, and exact deposit_mark supplies labels.
Only the matched frozen operand and pending-plan invariant are
release-specific premises. -/
theorem checked_pc10_step {Tag : Type} (digits : Tag→BitVec 36) (atSource : Nat→Tag)
    {base origin : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (m : Mode)
    (G : GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle w m)
    (layout : ∀ a b,w=a++b → ∀ j,BStarLongFixedRouting.Layout B base j=
      BStarLongFixedRouting.Layout B (play origin a) j)
    (emptyAtIssue : ∀ a e b,w=a++e::b →
      BStarClearanceSource.Launch ((play origin a) (S.getD 0 fall).1).long
        ((ring (play origin a) e) (S.getD 0 fall).1).long →
      (ctrlOp.read ((play origin a) (S.getD 0 fall).1).long).toNat=10 →
      MobilesEmpty hp base (play origin a) o.val)
    (pc10 : pc (play origin w) (S.getD 0 fall).1=10)
    (root baseAddr e : Fin n) (width seam tail : Nat)
    (dest : Dest B base root width) (strip : Strip B base baseAddr seam tail)
    (C : Dest B (play origin w) root width) (U : Strip B (play origin w) baseAddr seam tail)
    (join : addr baseAddr 0=addr root (width-1))
    (ownerHead : dataOwner (oldH6 B base) (addr baseAddr 0) (rail seam 0)=o.val)
    (rdGate : ∀ j<width, (readLane (Sheet.index .rd) ((play origin w) (addr root j)).long).gate=true)
    (upGate : ∀ j, 0<j → j≤tail → (readLane (Sheet.index (rail seam j))
      ((play origin w) (addr baseAddr j)).long).gate=true)
    (s : Ledger Tag) (lab : Nat→Option Tag) (size : (planOf atSource seam tail).length=width)
    (P : OrderedPrefix (planOf atSource seam tail) s (stripWord tail lab))
    (old : RetainedMatches digits (play origin w) root width s)
    (matched : MobileMatches digits (play origin w) baseAddr seam tail lab)
    (capturePlan : ∀ R : ReleaseAt hp (play origin w) e baseAddr seam tail (fun t=>S.getD t fall) len m,
      (lanes (play origin w) (addr baseAddr R.i) .rs).frozen=.data (digits (atSource R.i)) ∧
      s.release.pending=(List.range' R.i (tail+1-R.i)).map atSource) :
    ∃ t labels, OrderedPrefix (planOf atSource seam tail) t (stripWord tail labels) ∧
      RetainedMatches digits (ring (play origin w) e) root width t ∧
      MobileMatches digits (ring (play origin w) e) baseAddr seam tail labels := by
  let y := play origin w
  have same := layout w [] (by simp)
  obtain ⟨R,which⟩ := classify_release hp chart sep w m G same pc10 root baseAddr e width seam tail
    dest strip join ownerHead
  rcases which with quiet|hasRelease
  · obtain ⟨t,ls,_,post,rs,us⟩ := data_mark hp digits y root baseAddr e width seam tail
      C U join (sep e) s _ size lab P old matched rdGate upGate R quiet
    exact ⟨t,ls,post,rs,us⟩
  · obtain ⟨release⟩ := hasRelease
    have act : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w (.busy 10 (.out release.k)) :=
      release.mode ▸ G
    have vacancy := generated_cut_vacant hp chart sep act true layout emptyAtIssue
    have start : Unvisited S fall len release.k true (addr baseAddr release.i) :=
      ⟨release.k,by omega,Nat.le_of_lt release.strict,release.ptr⟩
    have behind := all_behind_unvisited hp chart baseAddr seam tail release.i release.k strip release.range.1 start
    have rg : rail seam release.i=.rs := if_neg (by have := release.range.1; omega)
    have ip : 0<release.i := Nat.lt_of_lt_of_le U.seam_pos release.range.1
    have gate : (lanes y (addr baseAddr release.i) .rs).gate=true := by
      unfold lanes
      have E := upGate release.i ip release.range.2
      rwa [rg] at E
    have align := capturePlan release
    obtain ⟨t,_,End,H,Q⟩ := deposit_mark hp digits atSource y root baseAddr e width seam tail release.i .left
      C U join (sep e) s size lab P old matched rdGate R release.range.1 release.range.2 release.markAt release.only
      release.win gate align.1 S fall len release.k vacancy behind align.2
    exact ⟨t,_,End,H,Q⟩

end L4.BStarCopyRightInjectStep
