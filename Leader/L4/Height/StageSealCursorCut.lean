import Leader.L4.Height.StageSealLaunchCut
import Leader.L4.BStarAcquireAckAncestry
import Leader.L4.BStarSeparatingProgress

namespace L4.Height.StageSealCursorCut
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarLongFixedRouting BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetChartService
open BStarSealBitDescriptor BStarAcquireHistoryReturn
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step
open BStarAcquireForwardTrace BStarSeparatingRail
open BStarSeparatingProgress BStarResetChartService BStarAcquireHistoryReturn BStarSealBitDescriptor BStarAcquireHistorySample

theorem first_consume {base x : X} {addr : Nat→Pos n} {len : Nat}
    {op : Nat} (diff : 2≠op) {j : Cursor} {m : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base addr len x (.busy op j) w m)
    (later : (ctrlOp.read (play x w (addr 0).1).long).toNat=2) :
    ∃ pre e tail, w=pre++e::tail ∧
      BusyOnly hp base addr len op x j pre (.back 0) ∧
      Event hp addr len (play x pre) e (.busy op (.back 0)) .idle := by
  generalize H : Mode.busy op j = initial at T
  induction T generalizing j with
  | @endpoint y m I =>
    rw [←H] at I
    have eq := I.1.2.2.2
    change (ctrlOp.read (y (addr 0).1).long).toNat=2 at later
    rw [later] at eq
    exact (diff eq).elim
  | @next y a e w b dest I E T ih =>
    subst a
    cases E with
    | consume _ own clean =>
      exact ⟨[],e,w,rfl,.nil I,.consume _ own clean⟩
    | transit _ z d live seen =>
      obtain ⟨pre,f,tail,W,L,F⟩ := ih (j:=d) later rfl
      exact ⟨e::pre,f,tail,congrArg (List.cons e) W,.cons I (.transit _ _ _ live seen) L,F⟩
    | arrived_hold _ ne =>
      obtain ⟨pre,f,tail,W,L,F⟩ := ih (j:=.back 0) later rfl
      exact ⟨e::pre,f,tail,congrArg (List.cons e) W,.cons I (.arrived_hold op ne) L,F⟩

private theorem advance {addr : Nat→Pos n} {len op : Nat} {x : X} {e : Fin n}
    {z d : Cursor} (E : Event hp addr len x e (.busy op z) (.busy op d)) : Advance len z d := by
  cases E with
  | arrived_hold _ _ => exact .stay _
  | transit _ _ _ _ S =>
    cases S with
    | cons _ _ A _ tail => cases tail; exact A

/-- Extract the actual departure from a specified outward position on a real completed
busy prefix. No chart labels, nomination, or healthy-payload hypotheses are used. -/
theorem split_outward {base x : X} {addr : Nat→Pos n} {len op a b : Nat}
    {w : List (Fin n)} (T : BusyOnly hp base addr len op x (.out a) w (.out b))
    (k : Nat) (L : a≤k) (R : k<b) :
    ∃ pre e post, w=pre++e::post ∧
      BusyOnly hp base addr len op x (.out a) pre (.out k) ∧
      Event hp addr len (play x pre) e (.busy op (.out k)) (.busy op (.out (k+1))) ∧
      BusyOnly hp base addr len op (step (play x pre) e) (.out (k+1)) post (.out b) := by
  generalize A : Cursor.out a = z at T
  generalize B' : Cursor.out b = dest at T
  induction T generalizing a with
  | nil _ =>
    have eq := Cursor.out.inj (A.trans B'.symm)
    omega
  | @cons x z d dest e w I E tail ih =>
    subst z
    have F := advance hp E
    cases F with
    | stay =>
      obtain ⟨pre,f,post,W,U,V,Z⟩ := ih L rfl B'
      exact ⟨e::pre,f,post,congrArg (List.cons e) W,.cons I E U,V,Z⟩
    | forward _ =>
      by_cases eq : a=k
      · subst a
        exact ⟨[],e,w,rfl,.nil I,E,B'.symm ▸ tail⟩
      · obtain ⟨pre,f,post,W,U,V,Z⟩ := ih (by omega) rfl B'
        exact ⟨e::pre,f,post,congrArg (List.cons e) W,.cons I E U,V,Z⟩
    | turn =>
      obtain ⟨l,h⟩ := busy_no_back_to_out hp tail ⟨b,B'.symm⟩
      cases h

end L4.Height.StageSealCursorCut
