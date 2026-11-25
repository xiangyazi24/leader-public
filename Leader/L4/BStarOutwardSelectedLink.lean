import Leader.L4.BStarSeparatorRing
import Leader.L4.BStarResetReleaseHistory
import Leader.L4.BStarOwnerLaunchOrigin

/-! Uniqueness of the actual selector on a strict outward cursor step.
The statement works for arbitrary generated payloads, including ADMIT. -/
namespace L4.BStarOutwardSelectedLink
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetMarkAdapter BStarSeparatingRail BStarResetChartService BStarResetChartTouch
open BStarSeparatorControl BStarSeparatorRing BStarLongDoor BStarResetRailRing
open BStarLongFixedRouting BStarSeparatingProgress BStarResetSchedule

/-- A strict outward advance cannot be fabricated by selecting no link
at the old cursor. The preceding link and a wholly quiet mark both keep
the old forward class at that slot. -/
theorem mark_selects {u v : BStarSeparatingRail.Rail} {len k : Nat} (M : Mark anyTag len u v)
    (old : Good anyTag len u (.out k)) (new : Good anyTag len v (.out (k+1))) :
    M.link k := by
  have h : k+1≤len := new.1
  apply Classical.byContradiction
  intro notLink
  have f : anyTag.F (v k) := by
    by_cases incoming : ∃ j, j+1=k ∧ M.link j
    · obtain ⟨j,E,J⟩ := incoming
      have T := (M.tf j J (old.2.2 _ (by omega)) (by rw [E]; exact old.2.1)).2
      rwa [E] at T
    · exact (M.idle k old.1 notLink (fun j E J => incoming ⟨j,E,J⟩)
        (fun E _ => False.elim (by omega))).2.2.1 old.2.1
  obtain ⟨pay,F⟩ := f
  have T := new.2.2 k (by omega)
  rw [T] at F
  contradiction

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- On an actual joined mark, the existential witness in `linkAt`
is therefore a command of this very physical pair. -/
theorem actual_selects {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (e : Fin n) (he : e≠rightNeighbor e)
    (op k : Nat) (wait : Waiting hp base (S.getD 0 fall).1 op x)
    (old : Good anyTag len (project (fun j => S.getD j fall) x) (.out k))
    (new : Good anyTag len (project (fun j => S.getD j fall)
      (AllSizeS1Geometry.step B x e)) (.out (k+1))) :
    linkAt hp x e (fun j => S.getD j fall) len k := by
  let M := mark_at hp C e he op wait (.out k) (by intro hz; cases hz) old
  exact mark_selects M old new

/-- On the very tape of a completed tour, each crossed outward index
has an old configuration with the genuine forward class and an actual
selected command to the next chart address. This uses an arbitrary
opcode, with no soundness claim about the payload's contents. -/
theorem completed_crossing {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n, e≠rightNeighbor e)
    (Q : X → Prop) (q : Q x)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (AllSizeS1Geometry.step B x e))
    (op k j : Nat) (start : k≤j) (hj : j<len)
    (wait : Waiting hp base (S.getD 0 fall).1 op x)
    (old : Good anyTag len (project (fun k => S.getD k fall) x) (.out k))
    (w : List (Fin n))
    (T : Seen (AllSizeS1Geometry.step B) (project (fun k => S.getD k fall))
      anyTag len x (.out k) w (.back 0)) :
    let step := AllSizeS1Geometry.step (n:=n) B
    let adr := fun k => S.getD k fall
    ∃ pre e tail, w=pre++e::tail ∧
      let a := BStarResetSchedule.run step x pre
      Q a ∧ Waiting hp base (adr 0).1 op a ∧
      Good anyTag len (project adr a) (.out j) ∧
      Good anyTag len (project adr (step a e)) (.out (j+1)) ∧
      linkAt hp a e adr len j := by
  dsimp only
  let step := AllSizeS1Geometry.step (n:=n) B
  let adr := fun k => S.getD k fall
  let root := (adr 0).1
  let I := fun a => Q a ∧ Waiting hp base root op a
  have keep : ∀ a e u, I a → u≠.back 0 →
      Good anyTag len (project adr a) u → I (step a e) := by
    intro a e u ia live G
    have qa := closed a ia.1 e
    obtain ⟨hdr,k0⟩ := root_header hp C ia.2.1
    have K : project adr a 0=atSite (a root).long 0 := by
      change atSite (a root).long (adr 0).2=_
      rw [k0]
    have ctrl := step_wait k₁ k₂ t₂ J₁ J₂ r c p c₁ hp a e root hdr
      ia.2.2.1 ia.2.2.2.1 (K ▸ before_receipt G live)
    have ph := congrArg (fun z : BitVec 2 × BitVec 9 => z.1.toNat) ctrl
    have oc := congrArg (fun z : BitVec 2 × BitVec 9 => z.2.toNat) ctrl
    exact ⟨qa,fiber _ qa,(BStarResetWaitRing.valid_of_control_eq _ _ ctrl).trans ia.2.2.1,
      ph.trans ia.2.2.2.1,oc.trans ia.2.2.2.2⟩
  obtain ⟨pre,e,tail,W,V,F,G⟩ :=
    BStarResetReleaseHistory.crossing step (project adr) anyTag len I keep x w
      k j start hj ⟨q,wait⟩ old T
  exact ⟨pre,e,tail,W,V.1,V.2,F,G,actual_selects hp C e (sep e) op j V.2 F G⟩

open BStarGeneratedOwner BStarOwnerLaunchOrigin

/-- The same extraction from the stronger generated busy history.
It retains the old and post-mark Current witnesses and the exact
uninterrupted busy suffix for the consumer of the arrival. -/
theorem busy_crossing {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n, e≠rightNeighbor e)
    {op k j : Nat} (start : k≤j) (hj : j<len) {w : List (Fin n)}
    (T : BusyOnly hp base (fun k => S.getD k fall) len op x (.out k) w (.back 0)) :
    let step := AllSizeS1Geometry.step (n:=n) B
    let adr := fun k => S.getD k fall
    ∃ pre e tail, w=pre++e::tail ∧
      let a := BStarResetSchedule.run step x pre
      BusyOnly hp base adr len op x (.out k) pre (.out j) ∧
      Current hp base adr len a (.busy op (.out j)) ∧
      Current hp base adr len (step a e) (.busy op (.out (j+1))) ∧
      linkAt hp a e adr len j ∧
      BusyOnly hp base adr len op (step a e) (.out (j+1)) tail (.back 0) := by
  dsimp only
  let adr := fun k => S.getD k fall
  let step := AllSizeS1Geometry.step (n:=n) B
  have initial {a : X} {z : Cursor} {word : List (Fin n)}
      (W : BusyOnly hp base adr len op a z word (.back 0)) :
      Current hp base adr len a (.busy op z) := by
    cases W with
    | nil I => exact I
    | cons I _ _ => exact I
  induction w generalizing x k with
  | nil => cases T
  | cons e w ih =>
    cases T with
    | cons I E suffix =>
      have saved := E
      cases E with
      | transit _ _ _ _ G =>
        cases G with
        | cons _ _ A _ U =>
          cases U
          cases A with
          | stay =>
            obtain ⟨pre,f,tail,W,seen,R,V,L,rest⟩ := ih start suffix
            exact ⟨e::pre,f,tail,congrArg (List.cons e) W,.cons I saved seen,R,V,L,rest⟩
          | forward =>
            by_cases K : k=j
            · subst k
              have V := initial suffix
              exact ⟨[],e,w,rfl,.nil I,I,V,actual_selects hp C e (sep e) op j I.1 I.2.1 V.2.1,suffix⟩
            · obtain ⟨pre,f,tail,W,seen,R,V,L,rest⟩ := ih (by omega) suffix
              exact ⟨e::pre,f,tail,congrArg (List.cons e) W,.cons I saved seen,R,V,L,rest⟩
          | turn => omega

/-- A busy ending of a recovered chart belongs to its actual own
launch. On that uninterrupted post-launch interval, extract the exact
old mark at each requested crossing, with no inference from identical
payload bytes and no changes to the intervening word. -/
theorem from_idle_crossing {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n, e≠rightNeighbor e)
    {op j : Nat} (hj : j<len) {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun k => S.getD k fall) len x .idle w (.busy op (.back 0))) :
    let step := AllSizeS1Geometry.step (n:=n) B
    let adr := fun k => S.getD k fall
    ∃ launchPre launchMark pre e tail,
      w=launchPre++launchMark::(pre++e::tail) ∧
      let old := BStarResetSchedule.run step x launchPre
      let launched := step old launchMark
      let a := BStarResetSchedule.run step launched pre
      launchMark=RearTrace.predecessor (adr 0).1 ∧
      BStarClearanceSource.Launch (old (adr 0).1).long (launched (adr 0).1).long ∧
      (ctrlOp.read (old (adr 0).1).long).toNat=op ∧
      BusyOnly hp base adr len op launched (.out 0) pre (.out j) ∧
      Current hp base adr len a (.busy op (.out j)) ∧
      Current hp base adr len (step a e) (.busy op (.out (j+1))) ∧
      linkAt hp a e adr len j ∧
      BusyOnly hp base adr len op (step a e) (.out (j+1)) tail (.back 0) := by
  dsimp only
  obtain ⟨s,post,f,W,D,L,P,F⟩ := from_idle hp T
  obtain ⟨pre,e,tail,E,seen,I,J,K,H⟩ := busy_crossing hp C sep (Nat.zero_le j) hj F
  exact ⟨s,f,pre,e,tail,W.trans (congrArg (fun t => s++f::t) E),D,L,P,seen,I,J,K,H⟩

#print axioms mark_selects
#print axioms actual_selects
#print axioms completed_crossing
#print axioms busy_crossing
#print axioms from_idle_crossing
end L4.BStarOutwardSelectedLink
