import Leader.L4.BStarCopyLeftFrozen
import Leader.L4.BStarCopyLeftPreinject

namespace L4.BStarCopyLeftLoadToInject
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongToken BStarLongCommandData BStarLongEvents BStarLongDoor
open BStarCopyLeftFrozen BStarCopyLeftPreinject BStarCopyLoadHistory
open BStarAcquireHistorySample BStarAcquireHistoryReturn BStarAcquireForwardTrace
open BStarCopyOwnedFrozen BStarCopyOperand
open BStarResetSchedule BStarSeparatorControl
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

def Past (k : Nat) : Cursor → Prop
  | .out j => k<j
  | .back _ => True

private theorem single {x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {z d : Cursor} (seen : Seen ring (project addr) anyTag len x z [e] d) :
    Advance len z d := by
  cases seen with
  | cons _ _ on _ tail => cases tail; exact on

private theorem past_event {x : X} {addr : Nat→Pos n} {len op k : Nat}
    {e : Fin n} {z d : Cursor} (old : Past k z)
    (E : Event hp addr len x e (.busy op z) (.busy op d)) : Past k d := by
  cases E with
  | transit _ _ _ _ N =>
    cases single hp N
    · exact old
    · unfold Past at *; omega
    · exact True.intro
    · exact True.intro
  | arrived_hold _ => exact True.intro

theorem frozen_busy_suffix {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (kl : k≤len)
    (atSource : S.getD k fall=(i,0))
    (own : dataOwner (oldH6 B base) i .ls=o.val)
    (op : Nat) (opBand : op=8 ∨ op=9)
    (lead : List (Fin n)) {x : X} {z d : Cursor} {w : List (Fin n)}
    (old : x=play origin lead)
    (history : GeneratedOwner hp base (fun t => S.getD t fall) len origin .idle lead (.busy op z))
    (busy : BusyOnly hp base (fun t => S.getD t fall) len op x z w d)
    (past : op=8 → Past k z)
    (layout : ∀ a e b, w=a++e::b →
      ∀ j, BStarLongFixedRouting.Layout B base j=BStarLongFixedRouting.Layout B (play x a) j) :
    (readLane (Sheet.index .ls) (play x w i).long).frozen=
      (readLane (Sheet.index .ls) (x i).long).frozen := by
  induction busy generalizing lead with
  | nil => rfl
  | @cons x z d fin e w I ev tail ih =>
    have same := layout [] e w rfl
    have F : FrozenSafe hp x e i .ls := by
      cases z with
      | back j => exact safe_returning hp chart same e i .ls j own I.2.1
      | out j =>
        have N : ∀ h : op=8, S.getD j fall≠(i,0) := by
          intro H E
          have eq8 := H
          have le := I.2.1.1
          have eq := (List.getD_inj (by have := chart.length; omega)
            (by have := chart.length; omega) chart.nodup).mp (E.trans atSource.symm)
          subst j
          exact Nat.lt_irrefl _ (past eq8)
        rw [old]
        exact ls_frozen_outward hp chart sep history (old ▸ I) (old ▸ same)
          e i own (by omega) (by omega) N (by omega)
    have frame := ring_frozen_frame hp x e i .ls (sep e) F
    have newly : ring x e=play origin (lead++[e]) := by
      rw [BStarResetSchedule.run_append,←old]; rfl
    have added := generated_append hp history
      (old ▸ GeneratedOwner.next I ev (.endpoint (busy_start hp tail)))
    exact (ih (lead++[e]) newly added (fun h => past_event hp (past h) ev)
      (fun a f b E => layout (e::a) f b (congrArg (List.cons e) E))).trans frame

open BStarCopyRightLoadToInject (OwnMiddle)

/-- Fixed-slot authentication from an original selected LOAD to the
immediate pre-INJECT cut. The replay is the stated raw word: LOAD,
remainder of PC8, own PC8→PC9→PC10 mid-interval, then original PC10
prefix. Caller does not supply matching bytes, per-mark freeze frame,
or an exclusion of repeated K5 stutters. -/
theorem original_to_inject {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead w8 middle w10 : List (Fin n)) (load : Fin n) (side : Side)
    (C : CommandClaim) (k j : Nat) (kl : k≤len) (jl : j≤len)
    (injectAddr : S.getD j fall=(site load side,5))
    (loadLoc : address load C.source=S.getD k fall)
    (source : C.source=⟨side,0⟩)
    (selected : C∈orderedCommands (oldPair B (play origin lead) load))
    (noDoor : C.kind≠.door)
    (inside : (geometry (oldPair B (play origin lead) load) side).inside=true)
    (own : dataOwner (oldH6 B base) (site load side) .ls=o.val)
    (before : GeneratedOwner hp base (fun t => S.getD t fall) len origin .idle lead (.busy 8 (.out k)))
    (loadEvent : Event hp (fun t => S.getD t fall) len (play origin lead) load
      (.busy 8 (.out k)) (.busy 8 (.out (k+1))))
    (b8 : BusyOnly hp base (fun t => S.getD t fall) len 8 (ring (play origin lead) load) (.out (k+1)) w8 (.back 0))
    (M : OwnMiddle hp base origin (fun t => S.getD t fall) len ((lead++[load])++w8) middle)
    (b10 : BusyOnly hp base (fun t => S.getD t fall) len 10
      (play origin (((lead++[load])++w8)++middle)) (.out 0) w10 (.out j))
    (fiber : ∀ a b, ((((lead++[load])++w8)++middle)++w10)=a++b →
      ∀ v,BStarLongFixedRouting.Layout B base v=BStarLongFixedRouting.Layout B (play origin a) v) :
    ∃ (pre post : List (Fin n)) (launch : Fin n) (bank : Fin 3),
      lead=pre++launch::post ∧ launch=RearTrace.predecessor (S.getD 0 fall).1 ∧
      bank.val=(captures.read ((play origin pre) (S.getD 0 fall).1).long).toNat / 16 % 4 ∧
      (readLane (Sheet.index .ls)
        (play origin ((((lead++[load])++w8)++middle)++w10) (site load side)).long).frozen=
        oldBankPacket ((play origin lead) (site load side)).long bank := by
  let i := site load side
  have idx : S.getD k fall=(i,0) := by
    rw [←loadLoc,source]
  have pre8 : play origin (lead++[load])=ring (play origin lead) load := by
    rw [BStarResetSchedule.run_append]; rfl
  obtain ⟨pre,post,launch,bank,L,D,bidx,freeze⟩ :=
    generated_freezes_bank hp chart sep before load side false C loadLoc own selected noDoor source inside
  have reached8 := BStarGeneratedTapeCuts.at_end hp before
  have G8 : GeneratedOwner hp base (fun t => S.getD t fall) len origin .idle (lead++[load]) (.busy 8 (.out (k+1))) := by
    apply generated_append hp before
    exact .next reached8 loadEvent (.endpoint (busy_start hp b8))
  have F8 := frozen_busy_suffix hp chart sep i k kl idx own 8 (.inl rfl)
    (lead++[load]) pre8.symm G8 b8 (fun _ => Nat.lt_succ_self _)
    (fun a e b eq => by
      have H := fiber ((lead++[load])++a) ((e::b)++middle++w10) (by simp [eq,List.append_assoc])
      rw [BStarResetSchedule.run_append,pre8] at H
      exact H)
  have F9 := ls_frozen_between hp chart sep ((lead++[load])++w8) middle (.busy 10 (.out 0))
    M.end10 i own
    (fun a e b eq => fiber (((lead++[load])++w8)++a) ((e::b)++w10) (by simp [eq,List.append_assoc]))
    (fun a e b eq op j I => by
      have pc := M.outward9 a e b eq op j I
      exact ⟨by omega,by omega,by omega,by omega⟩)
  have F10 := frozen_pc10_prefix hp chart sep i j jl injectAddr own (((lead++[load])++w8)++middle)
    rfl M.end10 b10 (fun a e b eq => by
      have H := fiber ((((lead++[load])++w8)++middle)++a) (e::b) (by simp [eq,List.append_assoc])
      rw [BStarResetSchedule.run_append] at H
      exact H)
  rw [←BStarResetSchedule.run_append] at F10
  rw [←pre8,←BStarResetSchedule.run_append] at F8
  have orig : (readLane (Sheet.index .ls) (play origin (lead++[load]) i).long).frozen =
      oldBankPacket ((play origin lead) i).long bank := by
    rw [pre8]
    exact freeze
  have result := F10.trans (F9.trans (F8.trans orig))
  exact ⟨pre,post,launch,bank,L,D,bidx,result⟩

end L4.BStarCopyLeftLoadToInject
