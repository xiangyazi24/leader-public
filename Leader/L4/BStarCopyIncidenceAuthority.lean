import Leader.L4.BStarPostCutAttempt

namespace L4.BStarCopyIncidenceAuthority
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarCustodyCuts
open BStarBodyStageProvenance

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- The recovered attempt's prefix lies after cut A by exact word
ancestry, not by equality of the state or of the controller PC. -/
theorem after_cut {u pre : List (Fin n)} (v t reset middle : List (Fin n))
    (W : (u++v)++t=(pre++reset)++middle) (below : u.length≤pre.length) :
    ∃ suf, pre++reset=u++suf := by
  have U : ((u++v)++t).take u.length=u := by
    rw [List.append_assoc,List.take_append_of_le_length (Nat.le_refl u.length),List.take_length]
  have P : u.length≤(pre++reset).length := by simp; omega
  rw [W,List.take_append_of_le_length P] at U
  exact ⟨(pre++reset).drop u.length,by exact ((congrArg (· ++ (pre++reset).drop u.length) U.symm).trans (List.take_append_drop _ _)).symm⟩

/-- On every continuation of the actual recovered origin, all three
COPY incidences enjoy the same effective STAGE writer and selector
law from the shared first cut. Their responsible writers can be
different owners; this uses the all-center cut fact, not focal credit. -/
theorem all_three {base x : X} {u v : List (Fin n)}
    (F : CutFacts hp base x u v) (hh : ∃ i,oldH6 B base i=true)
    (o : Owners (oldH6 B base))
    (t pre reset middle : List (Fin n))
    (W : (u++v)++t=(pre++reset)++middle) (below : u.length≤pre.length) :
    ∀ w e i (j : Fin 3),
      BodyAuthority hp (play (play x (pre++reset)) w) e i
        (endpoint (oldH6 B base) hh o ⟨j.val,by omega⟩).1 := by
  obtain ⟨suf,E⟩ := after_cut v t reset middle W below
  intro w e i j
  let k : Fin 11 := ⟨j.val,by omega⟩
  let H := (endpoint (oldH6 B base) hh o k).1
  have hdr : oldH6 B base H=true := (endpoint_spec (oldH6 B base) hh o k).1
  have S : play (play x (pre++reset)) w=play x (u++(suf++w)) := by
    rw [E,←BStarResetSchedule.run_append step x (u++suf) w,List.append_assoc]
  rw [S]
  exact F.body (suf++w) e i H hdr

end L4.BStarCopyIncidenceAuthority
