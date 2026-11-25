import Leader.L4.DirtyFenceHeldMean
import Leader.L4.DirtyFenceOccurrence

namespace L4.DirtyFenceFixedCut
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarH6WordChart BStarH6Ordinal BStarClearanceDataChart BStarResetChartTouch
open BStarFenceShadow BStarFencePorts BStarFenceLineGeometry BStarFenceSweepClock
open BStarFenceLeftShadow (leftOcc)
open BStarFenceRightShadow (rightOcc)
open BStarClearanceSource (Held held_before)
open BStarClearanceIndexedSum (distance distance_idx)
open DirtyLeastForward (ringF ring_origin)
open L4.Height

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- The fixed cutoff is geometric. It does not require that the
first forward still exists, or that its high slot maps to a particular FENCE. -/
theorem prep_before_high {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    {j : Nat} (J : j≤len) (high : 6≤(S.getD j fall).2.val)
    {u : Pos n} (U : u∈S) {op : Prep} {target : Sheet}
    (P : target∈prepSites (longGeometry B (base u.1)) u.2 op) :
    distance S (S.getD j fall)<distance S u := by
  have lenS := chart.length
  obtain ⟨i,hi,E⟩ := List.mem_iff_getElem.mp U
  have K := (DirtyFencePrep.prep_cut _ _ _ _ P).1
  have hId : S.getD i fall=u := (List.getElem_eq_getD (h:=hi) fall).symm.trans E
  have lt : i<j := by
    by_cases H : i<j
    · exact H
    · exfalso
      have W := DirtyFenceOccurrence.chart_occurrence_mono hp chart head cont
        (by omega : j≤i) (by omega : i≤len)
      rw [hId] at W
      omega
  have jl : j<S.length := by omega
  rw [←List.getElem_eq_getD (h:=jl) fall,←E,distance_idx chart.nodup jl,distance_idx chart.nodup hi]
  omega

/-- A first high chart index always exists: terminal K10 is high.
All strictly earlier indices are prep-range, whether or not occupied. -/
theorem exists_first_high {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) :
    ∃ j, j≤len ∧ 6≤(S.getD j fall).2.val ∧
      ∀ i,i<j → (S.getD i fall).2.val≤5 := by
  let P := fun j => 6≤(S.getD j fall).2.val
  have least (k : Nat) : (∃ j,j≤k ∧ P j) →
      ∃ j,j≤k ∧ P j ∧ ∀ i,i<j → ¬P i := by
    classical
    induction k with
    | zero =>
        rintro ⟨j,J,H⟩
        exact ⟨j,J,H,fun i I => False.elim (by omega)⟩
    | succ k ih =>
        intro H
        by_cases K : ∃ j,j≤k ∧ P j
        · obtain ⟨j,L,M,N⟩ := ih K
          exact ⟨j,by omega,M,N⟩
        · obtain ⟨j,L,M⟩ := H
          refine ⟨j,L,M,?_⟩
          intro i I N
          exact K ⟨i,by omega,N⟩
  have last : P len := by
    dsimp only [P]
    rw [chart.terminal]
    change 6≤10
    decide
  obtain ⟨j,J,H,E⟩ := least len ⟨len,Nat.le_refl _,last⟩
  exact ⟨j,J,H,fun i I => by have N := E i I; change ¬6≤(S.getD i fall).2.val at N; omega⟩

theorem expected_from_high_cut
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B q i)
    (closed : ∀ q,Q q→∀ e,Q (step q e))
    {l d r' : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l r')
    (RF : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1)
    (hn : 0<n) (hl : 0<l+r') (lc : l+r'≤n) (rc : d+r'≤n)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    {j : Nat} (J : j≤len) (high : 6≤(S.getD j fall).2.val)
    (clearBefore : ∀ i,i<j → ¬ringF x (S.getD i fall)) :
    let Lroot := (S.getD 0 fall).1
    let Rroot := (S.getD len fall).1
    let phys := fun q : X => (⟨leftOcc q Lroot l r', rightOcc q Rroot d r'⟩ :
      Two (l:=l+r') (r:=d+r'))
    Height.IIDExpectedHittingTimeAtMost step (fun q=>¬Held (q Lroot).long ∨ Empty (phys q)) x
      (92*n*max (l+r') (d+r')) := by
  let cutoff := distance S (S.getD j fall)
  have onPrep (u : Pos n) (U : u∈S)
      (P : ∃ sh op,sh∈prepSites (longGeometry B (base u.1)) u.2 op) :
      cutoff<distance S u := by
    obtain ⟨_,_,H⟩ := P
    exact prep_before_high hp chart head cont J high U H
  have clear (u : Pos n) (U : u∈S) (far : cutoff<distance S u) : ¬ringF x u := by
    obtain ⟨i,hi,E⟩ := List.mem_iff_getElem.mp U
    have JS : j<S.length := by have := chart.length; omega
    have iS : S.getD i fall=u := (List.getElem_eq_getD (h:=hi) fall).symm.trans E
    change distance S (S.getD j fall)<distance S u at far
    rw [←iS,←List.getElem_eq_getD (h:=JS) fall,←List.getElem_eq_getD (h:=hi) fall,
      distance_idx chart.nodup JS,distance_idx chart.nodup hi] at far
    rw [←iS]
    exact clearBefore i (by omega)
  exact DirtyFenceHeldMean.expected_until_nonheld_or_empty hp chart sep Q I layout closed LF RF dp
    flags notShort hn hl lc rc cutoff onPrep clear

#print axioms prep_before_high
#print axioms exists_first_high
#print axioms expected_from_high_cut
end L4.DirtyFenceFixedCut
