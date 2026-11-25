import Leader.L4.BStarCopyRightPostload

namespace L4.BStarCopyRightLoadToInject
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongToken BStarLongCommandData BStarLongEvents BStarLongDoor
open BStarCopyRightPostload BStarCopyRightCapture BStarCopyRightPreinject BStarCopyLoadHistory
open BStarAcquireVisitOrder BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireLiteralChain
open BStarResetChartTouch BStarClearanceDataChart BStarAcquireAnchors BStarResetMarkAdapter
open BStarLongCommand BStarSeparatingRail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

private theorem generated_append {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base addr len x a u b)
    (Q : GeneratedOwner hp base addr len (play x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

/-- Witnessed real phase cuts on a single actual tape. Every mark of
the middle tape is retained; its open outward busy orientations are
exactly PC9. The start and end modes force the successful 8/9 own
consumes and own launches on the witnessed GeneratedOwner tape. -/
structure OwnMiddle (base origin : X) (addr : Nat → Pos n) (len : Nat)
    (pre middle : List (Fin n)) : Prop where
  start8 : GeneratedOwner hp base addr len origin .idle pre (.busy 8 (.back 0))
  end10 : GeneratedOwner hp base addr len origin .idle (pre++middle) (.busy 10 (.out 0))
  actual : GeneratedOwner hp base addr len (play origin pre) (.busy 8 (.back 0)) middle (.busy 10 (.out 0))
  outward9 : ∀ a e z, middle=a++e::z → ∀ op j,
    Current hp base addr len (play origin (pre++a)) (.busy op (.out j)) → op=9

/-- Fixed-slot authentication from an original selected LOAD to the
immediate pre-INJECT cut. The replay is the stated raw word: LOAD,
remainder of PC8, own PC8→PC9→PC10 mid-interval, then original PC10
prefix. Caller does not supply matching bytes, per-mark freeze frame,
or an exclusion of repeated K2 stutters. -/
theorem original_to_inject {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead w8 middle w10 : List (Fin n)) (load : Fin n) (side : Side)
    (C : CommandClaim) (f : Payload) (k : Nat) (kl : k≤len)
    (loadLoc : address load C.source=S.getD k fall)
    (source : C.source=⟨side,2⟩)
    (selected : C∈orderedCommands (oldPair B (play origin lead) load))
    (noDoor : C.kind≠.door)
    (advanced : (C,.advance f)∈actualOffers (oldPair B (play origin lead) load)
      (((play origin lead) load).long,((play origin lead) (rightNeighbor load)).long))
    (inside : (geometry (oldPair B (play origin lead) load) side).inside=true)
    (own : dataOwner (oldH6 B base) (site load side) .rs=o.val)
    (before : GeneratedOwner hp base (fun t => S.getD t fall) len origin .idle lead (.busy 8 (.out k)))
    {z : Cursor}
    (loadEvent : Event hp (fun t => S.getD t fall) len (play origin lead) load
      (.busy 8 (.out k)) (.busy 8 z))
    (b8 : BusyOnly hp base (fun t => S.getD t fall) len 8 (ring (play origin lead) load) z w8 (.back 0))
    (M : OwnMiddle hp base origin (fun t => S.getD t fall) len ((lead++[load])++w8) middle)
    (b10 : BusyOnly hp base (fun t => S.getD t fall) len 10
      (play origin (((lead++[load])++w8)++middle)) (.out 0) w10 (.out k))
    (fiber : ∀ a b, ((((lead++[load])++w8)++middle)++w10)=a++b →
      ∀ v,BStarLongFixedRouting.Layout B base v=BStarLongFixedRouting.Layout B (play origin a) v) :
    ∃ (pre post : List (Fin n)) (launch : Fin n) (bank : Fin 3),
      lead=pre++launch::post ∧ launch=RearTrace.predecessor (S.getD 0 fall).1 ∧
      bank.val=(captures.read ((play origin pre) (S.getD 0 fall).1).long).toNat % 4 ∧
      (readLane (Sheet.index .rs)
        (play origin ((((lead++[load])++w8)++middle)++w10) (site load side)).long).frozen=
        oldBankPacket ((play origin lead) (site load side)).long bank := by
  let i := site load side
  have idx : S.getD k fall=(i,2) := by
    rw [←loadLoc,source]
  have k2 : C.source.occurrence=2 := congrArg At.occurrence source
  have past := load_enters_past hp load (sep load) C f k2 loadLoc advanced loadEvent (busy_start hp b8)
  have pre8 : play origin (lead++[load])=ring (play origin lead) load := by
    rw [BStarResetSchedule.run_append]; rfl
  obtain ⟨pre,post,launch,bank,L,D,bidx,freeze⟩ :=
    generated_freezes_bank hp chart sep before load side true C loadLoc own selected noDoor source inside
  have reached8 := BStarGeneratedTapeCuts.at_end hp before
  have G8 : GeneratedOwner hp base (fun t => S.getD t fall) len origin .idle (lead++[load]) (.busy 8 z) := by
    apply generated_append hp before
    exact .next reached8 loadEvent (.endpoint (busy_start hp b8))
  have F8 := frozen_busy_suffix hp chart sep i k kl idx own 8 (.inl rfl)
    (lead++[load]) pre8.symm G8 b8 (fun _ => past)
    (fun a e b eq => by
      have H := fiber ((lead++[load])++a) ((e::b)++middle++w10) (by simp [eq,List.append_assoc])
      rw [BStarResetSchedule.run_append,pre8] at H
      exact H)
  have F9 := rs_frozen_between hp chart sep ((lead++[load])++w8) middle (.busy 10 (.out 0))
    M.end10 i own
    (fun a e b eq => fiber (((lead++[load])++w8)++a) ((e::b)++w10) (by simp [eq,List.append_assoc]))
    (fun a e b eq op j I => by
      have pc := M.outward9 a e b eq op j I
      exact ⟨by omega,by omega,fun ne => (ne pc).elim⟩)
  have F10 := frozen_pc10_prefix hp chart sep i k kl idx own (((lead++[load])++w8)++middle)
    rfl M.end10 b10 (fun a e b eq => by
      have H := fiber ((((lead++[load])++w8)++middle)++a) (e::b) (by simp [eq,List.append_assoc])
      rw [BStarResetSchedule.run_append] at H
      exact H)
  rw [←BStarResetSchedule.run_append] at F10
  rw [←pre8,←BStarResetSchedule.run_append] at F8
  have orig : (readLane (Sheet.index .rs) (play origin (lead++[load]) i).long).frozen =
      oldBankPacket ((play origin lead) i).long bank := by
    rw [pre8]
    exact freeze
  have result := F10.trans (F9.trans (F8.trans orig))
  exact ⟨pre,post,launch,bank,L,D,bidx,result⟩

#print axioms original_to_inject
end L4.BStarCopyRightLoadToInject
