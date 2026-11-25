import Leader.L4.BStarSealModes
import Leader.L4.BStarSealWriterInterval
import Leader.L4.BStarCommitCenterExit

namespace L4.BStarSealSafeReplay
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongGrant BStarH6WordChart
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarSealOwnerFrame BStarAcquireVisitOrder BStarAcquireForwardTrace
open BStarAcquireLiteralChain BStarResetChartTouch BStarSealModes
open BStarAcquireAnchors BStarLongFiberOwner

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

def Safe (i : Fin n) (k : Nat) (m : Mode) (e : Fin n) : Prop :=
  (∀ a, m≠.busy releaseOp a) ∧ (e=i → Excluded k m)

/-- Same generated controller replay, recording only the exact two
tests needed to retain a sealed center. The recorded event and old
Current belong to the same literal old state and mark. -/
inductive Replay (base : X) (addr : Nat→Pos n) (len : Nat) (i : Fin n) (k : Nat) :
    X → Mode → List (Fin n) → Mode → Prop where
  | nil {x a} (I : Current hp base addr len x a) : Replay base addr len i k x a [] a
  | cons {x a b c e w}
      (I : Current hp base addr len x a) (E : Event hp addr len x e a b) (safe : Safe i k a e)
      (tail : Replay base addr len i k (step x e) b w c) :
      Replay base addr len i k x a (e::w) c

theorem generated {base x : X} {addr : Nat→Pos n} {len k : Nat} {i : Fin n}
    {w : List (Fin n)} {a b : Mode} (R : Replay hp base addr len i k x a w b) :
    GeneratedOwner hp base addr len x a w b := by
  induction R with
  | nil I => exact .endpoint I
  | cons I E _ _ ih => exact .next I E ih

theorem append {base x : X} {addr : Nat→Pos n} {len k : Nat} {i : Fin n}
    {u v : List (Fin n)} {a b c : Mode} (U : Replay hp base addr len i k x a u b)
    (V : Replay hp base addr len i k (play x u) b v c) :
    Replay hp base addr len i k x a (u++v) c := by
  induction U with
  | nil _ => exact V
  | cons I E S _ ih => exact .cons I E S (ih V)

private theorem generated_append {base x : X} {addr : Nat→Pos n} {len : Nat}
    {u v : List (Fin n)} {a b c : Mode} (U : GeneratedOwner hp base addr len x a u b)
    (V : GeneratedOwner hp base addr len (play x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction U with
  | endpoint _ => exact V
  | next I E _ ih => exact .next I E (ih V)

theorem before_mark {base x : X} {addr : Nat→Pos n} {len k : Nat} {i : Fin n}
    {w : List (Fin n)} {a b : Mode} (R : Replay hp base addr len i k x a w b) :
    ∀ u e v,w=u++e::v → ∃ m,
      GeneratedOwner hp base addr len x a u m ∧
      Current hp base addr len (play x u) m ∧ Safe i k m e := by
  induction R with
  | nil _ =>
    intro u e v W
    cases u <;> contradiction
  | @cons x a b c e w I E S R ih =>
    intro u f v W
    cases u with
    | nil =>
      have L := (List.cons.inj (show e::w=f::v from W)).1
      subst f
      exact ⟨a,.endpoint I,I,S⟩
    | cons g u =>
      obtain ⟨rfl,W'⟩ := List.cons.inj W
      obtain ⟨m,P,J,F⟩ := ih u f v W'
      exact ⟨m,.next I E P,J,F⟩

theorem bit_replay {base x : X} {addr : Nat→Pos n} {len k : Nat} {i : Fin n}
    {w : List (Fin n)} {a b : Cursor} (T : BusyOnly hp base addr len bitOp x a w b) :
    Replay hp base addr len i k x (.busy bitOp a) w (.busy bitOp b) := by
  induction T with
  | nil I => exact .nil I
  | @cons x z d b e w I E T ih =>
    have H := bit_safe k z
    exact .cons I E ⟨H.2,fun _=>H.1⟩ ih

theorem seal_replay {base x : X} {addr : Nat→Pos n} {len k : Nat} {i : Fin n}
    {w : List (Fin n)} {a b : Cursor} (T : BusyOnly hp base addr len sealOp x a w b)
    (P : Past k a) : Replay hp base addr len i k x (.busy sealOp a) w (.busy sealOp b) := by
  induction T with
  | nil I => exact .nil I
  | @cons x a z b e w I E T ih =>
    have advance : Advance len a z := by
      cases E with
      | transit _ _ _ _ seen =>
        cases seen with
        | cons _ _ H _ rest => cases rest; exact H
      | arrived_hold _ _ => exact .stay _
    have P' : Past k z := by
      intro j H
      cases advance with
      | stay => exact P j H
      | forward s =>
        have V := P s rfl
        have J := Cursor.out.inj H
        omega
      | turn => contradiction
      | reverse => contradiction
    have H := seal_after_center_safe k a P
    exact .cons I E ⟨H.2,fun _=>H.1⟩ (ih P')

theorem idle_safe_step (i e : Fin n) (k : Nat) :
    Safe i k .idle e := ⟨(idle_safe k).2,fun _=>(idle_safe k).1⟩

theorem foreign_idle_replay {base x : X} {addr : Nat→Pos n} {len k : Nat} {i : Fin n}
    {w : List (Fin n)} {b : Mode} (T : GeneratedOwner hp base addr len x .idle w b)
    (away : ∀ e∈w,rightNeighbor e≠(addr 0).1) :
    Replay hp base addr len i k x .idle w .idle := by
  induction w generalizing x b with
  | nil => exact .nil (BStarGeneratedTapeCuts.at_start hp T)
  | cons e w ih =>
    cases T with
    | next I E R =>
      have off := away e List.mem_cons_self
      cases E with
      | idle_hold h =>
        exact .cons I (.idle_hold h) (idle_safe_step i e k)
          (ih R (fun a A => away a (List.mem_cons_of_mem _ A)))
      | bad_issue own _ => exact (off (own ▸ RearTrace.right_predecessor (addr 0).1)).elim
      | launch own _ => exact (off (own ▸ RearTrace.right_predecessor (addr 0).1)).elim

private theorem of_busy {base x : X} {addr : Nat→Pos n} {len k op : Nat} {i : Fin n}
    {w : List (Fin n)} {a b : Cursor} (T : BusyOnly hp base addr len op x a w b)
    (safe : ∀ u e v z,w=u++e::v →
      Current hp base addr len (play x u) (.busy op z) → Safe i k (.busy op z) e) :
    Replay hp base addr len i k x (.busy op a) w (.busy op b) := by
  induction T with
  | nil I => exact .nil I
  | @cons x z z' b e w I E T ih =>
    exact .cons I E (safe [] e w z rfl I)
      (ih (fun u a v t P K => safe (e::u) a v t (congrArg (List.cons e) P) K))

private theorem same_outward {base x : X} {addr : Nat→Pos n} {len op k : Nat}
    {z : Cursor} (I : Current hp base addr len x (.busy op (.out k)))
    (J : Current hp base addr len x (.busy op z)) : z=.out k := by
  have F := I.2.1.2.1
  have L := I.2.1.1
  cases z with
  | out j =>
    have K := (BStarOwnerControlHistory.pointed_unique_forward _ len j J.2.1 J.2.2 k L).mp F
    exact congrArg Cursor.out K.symm
  | back j =>
    exact (BStarOwnerControlHistory.pointed_backward_no_forward _ len j J.2.1 k L F).elim

open BStarLongDoor BStarClearanceSource

/-- The uninterrupted launched COMMIT ending at its actual center
has the exact custody-safe replay certificate. This does not take
pointwise mode exclusions or terminal writer custody as input. -/
theorem precenter_commit_replay {base start : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (door i : Fin n) (w : List (Fin n)) (k : Nat) (L : k<len)
    (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (pc : (ctrlOp.read (start (S.getD 0 fall).1).long).toNat=commitOp)
    (launch : Launch (start (S.getD 0 fall).1).long ((step start door) (S.getD 0 fall).1).long)
    (T : BusyOnly hp base (fun j=>S.getD j fall) len commitOp (step start door) (.out 0) w (.out k)) :
    Replay hp base (fun j=>S.getD j fall) len i k (step start door)
      (.busy commitOp (.out 0)) w (.busy commitOp (.out k)) := by
  apply of_busy hp T
  intro u e v z E now
  refine ⟨commit_is_not_release z,?_⟩
  intro localMark op O impossible
  subst e
  have Z := (Mode.busy.inj impossible).2
  have OP := (Mode.busy.inj impossible).1
  subst z
  subst op
  obtain ⟨y,I,off⟩ := BStarCommitCenterExit.outgoing_modes_before_center
    hp C sep door i w k L idx head pc launch T u v E
  have Eq := same_outward hp now I
  subst y
  exact off commitOp O rfl

/-- A generated same-word replay plus these two per-mark safety facts
gives the exact all-prefix seal and writer conclusion. -/
theorem keeps_sealed {base origin x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val)
    (k : Nat) (kle : k≤len) (slot : S.getD k fall=(i,1))
    (lead w : List (Fin n)) (landed : play origin lead=x) (a b : Mode)
    (Lead : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead a)
    (R : Replay hp base (fun j=>S.getD j fall) len i k x a w b)
    (d : BStarLongPublication.Descriptor) (seed : BStarBitNoAbort.SealedCenter d (x i).long)
    (coh : BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (head : ∀ u e v,w=u++e::v → oldH6 B (play x u) i=true) :
    ∀ u v,w=u++v → BStarBitNoAbort.SealedCenter d (play x u i).long ∧
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports (play x u) i)=false := by
  apply BStarSealWriterInterval.every_sealed_prefix hp C sep i own k kle slot lead w landed d seed coh
  intro u e v W
  obtain ⟨m,P,I,F⟩ := before_mark hp R u e v W
  exact ⟨m,generated_append hp Lead (landed.symm ▸ P),I,head u e v W,F.1,F.2⟩

end L4.BStarSealSafeReplay
