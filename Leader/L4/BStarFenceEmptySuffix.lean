import Leader.L4.BStarFenceBStarMean

namespace L4.BStarFenceEmptySuffix
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarH6WordChart BStarH6Ordinal BStarClearanceDataChart BStarGeneratedOwner
open BStarResetChartTouch BStarGeneratedBandScan
open BStarFenceShadow BStarFencePorts BStarFenceRightShadow BStarFenceLineGeometry
open BStarFenceSweepClock

theorem empty_advance {n l r : Nat} (L : Fin l→Fin n) (R : Fin r→Fin n)
    (e : Fin n) (z : Two (l:=l) (r:=r)) (E : Empty z) :
    BStarFenceSweepClock.Empty (Two.advance L R e z) := by
  constructor <;> intro j
  · change update L e z.left j=false
    simp [update,E.1]
  · change update R e z.right j=false
    simp [update,E.2]

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Read just the actual mobile data of the two timed FENCE lines. -/
def ownedLines (L R : Fin n) (l d r' : Nat) (x : X) : Two (l:=l+r') (r:=d+r') :=
  ⟨BStarFenceLeftShadow.leftOcc x L l r',rightOcc x R d r'⟩

/-- Once both physical lines have cleared they cannot refill on any
later generated FENCE mark, including the mark leaving opcode 11.
This is physical protection, not a consequence of a sticky ghost bit. -/
theorem empty_mark {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B q i)
    (closed : ∀ q,Q q→∀ e,Q (step q e))
    (idle : Current hp base (fun j => S.getD j fall) len x .idle)
    {l d r' : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l r')
    (RF : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1)
    (a : List (Fin n)) (e : Fin n) (fence : pc (play x a) (S.getD 0 fall).1=11) :
    let L := (S.getD 0 fall).1
    let R := (S.getD len fall).1
    BStarFenceSweepClock.Empty (ownedLines L R l d r' (play x a)) →
    BStarFenceSweepClock.Empty (ownedLines L R l d r' (play x (a++[e]))) := by
  dsimp only
  intro E
  let z := ownedLines (S.getD 0 fall).1 (S.getD len fall).1 l d r' (play x a)
  have self : z.below z := ⟨fun _ h=>h,fun _ h=>h⟩
  obtain ⟨m,hist,live,now⟩ := generated_word hp chart Q layout closed sep a .idle I idle
  have D := both_mark hp chart sep hist now (layout _ live) fence LF RF dp flags notShort e z self
  rw [BStarResetSchedule.run_append]
  exact empty_of_below D (empty_advance _ _ e z E)

/-- Every prefix of the uninterrupted post-empty FENCE suffix
stays empty. The prefix hypothesis concerns only the old states, so
the final mark may actually leave PC 11. -/
theorem empty_until_exit {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B q i)
    (closed : ∀ q,Q q→∀ e,Q (step q e))
    (idle : Current hp base (fun j => S.getD j fall) len x .idle)
    {l d r' : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l r')
    (RF : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1)
    (a w : List (Fin n))
    (fence : ∀ u e v,w=u++e::v → pc (play x (a++u)) (S.getD 0 fall).1=11) :
    let L := (S.getD 0 fall).1
    let R := (S.getD len fall).1
    BStarFenceSweepClock.Empty (ownedLines L R l d r' (play x a)) →
    BStarFenceSweepClock.Empty (ownedLines L R l d r' (play x (a++w))) := by
  dsimp only
  intro E
  induction w generalizing a with
  | nil => simpa using E
  | cons e w ih =>
    have h0 := fence [] e w rfl
    rw [List.append_nil] at h0
    have E' := empty_mark hp chart sep Q I layout closed idle LF RF dp flags notShort a e h0 E
    have K := ih (a++[e]) (fun u f v A=>by
      have D := fence (e::u) f v (by rw [A,List.cons_append])
      simpa only [List.append_assoc,List.singleton_append] using D) E'
    simpa only [List.append_assoc,List.singleton_append] using K

#print axioms empty_until_exit
#print axioms empty_mark
end L4.BStarFenceEmptySuffix
