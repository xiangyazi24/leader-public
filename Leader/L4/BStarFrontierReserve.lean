import Leader.L4.BStarNativeReceiptAligned
import Leader.L4.BStarPhysicalLiftAlignment

namespace L4.BStarFrontierReserve
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarPhysicalPairLaw BStarPhysicalIncrementLedger BStarIncrementLedger BStarReceiptKey
open BStarPhysicalLiftAlignment
set_option maxRecDepth 4096

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem revealed_at_count (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history : List (Fin n)) (e i : Fin n) (t : Nat) (bit : Bool)
    (R : reveal hp base hh x (ownerAt hp base hh) start history e=some ((i,t),bit)) :
    t=count start (tapeInc hp base hh x history) i history.length := by
  classical
  unfold reveal at R
  dsimp only at R
  split at R
  · have E := Option.some.inj R
    have keyEq := congrArg Prod.fst E
    have iEq := congrArg Prod.fst keyEq
    have tEq := congrArg Prod.snd keyEq
    dsimp only at iEq tEq
    rw [iEq] at tEq
    exact tEq.symm
  · contradiction

/-- Even a pre-cut reveal unrelated to the genuine epoch cannot occupy
an indexed tick above the chosen owner's stopped count: every reveal
by this observer is given the actual old-prefix count. -/
theorem reserved_below_cut (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history : List (Fin n)) (i : Fin n) (t : Nat) (bit : Bool)
    (R : firstRaw (reveal hp base hh x (ownerAt hp base hh) start) (i,t) [] history=some bit) :
    t≤count start (tapeInc hp base hh x history) i history.length := by
  obtain ⟨lead,e,tail,W,read⟩ := firstRaw_witness _ _ [] history bit R
  simp only [List.nil_append] at read
  rw [revealed_at_count hp base x hh start lead e i t bit read]
  have E := count_on_shared_prefix hp base hh x lead [] (e::tail) start i
  rw [List.append_nil,←W] at E
  rw [E]
  exact count_monotone _ _ _ (by rw [W]; simp)

theorem frontier_excludes_reserved (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history : List (Fin n)) (i : Fin n) (t G : Nat) (bit : Bool)
    (upper : count start (tapeInc hp base hh x history) i history.length≤G)
    (window : frontier G≤t) :
    firstRaw (reveal hp base hh x (ownerAt hp base hh) start) (i,t) [] history≠some bit := by
  intro reserved
  have limit := reserved_below_cut hp base x hh start history i t bit reserved
  have F := (frontier_spec G).1
  omega

/-- A literal read at or above the comparison frontier must occur at
or after the stop, even when the prefix contains inherited flags. -/
theorem window_read_after_cut (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history future lead rest : List (Fin n))
    (e i : Fin n) (t G : Nat) (bit : Bool)
    (upper : count start (tapeInc hp base hh x history) i history.length≤G)
    (window : frontier G≤t) (tape : history++future=lead++e::rest)
    (read : reveal hp base hh x (ownerAt hp base hh) start lead e=some ((i,t),bit)) :
    history.length≤lead.length := by
  by_cases lt : lead.length<history.length
  · exfalso
    have H : history <+: history++future := ⟨future,rfl⟩
    have hMark : (lead++[e]) <+: history++future :=
      ⟨rest,by simpa [List.append_assoc] using tape.symm⟩
    have hle : (lead++[e]).length≤history.length := by
      simp only [List.length_append,List.length_singleton]
      omega
    obtain ⟨w,split⟩ := List.prefix_of_prefix_length_le hMark H hle
    have cut : history=lead++e::w := by simpa [List.append_assoc] using split.symm
    have old := revealed_at_count hp base x hh start lead e i t bit read
    have same := count_on_shared_prefix hp base hh x lead [] (e::w) start i
    rw [List.append_nil,←cut] at same
    rw [same] at old
    have above := (frontier_spec G).1
    have bound := count_monotone start (tapeInc hp base hh x history) i (Nat.le_of_lt lt)
    omega
  · omega

end L4.BStarFrontierReserve
