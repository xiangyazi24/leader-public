import Leader.L4.Height.G9WirePart02
set_option Elab.async false

namespace L4.Height.G9Wire
open G9Spine L4.Compiler.Native Classical

section LiteralPublication

open AllSizeProtocol BStarTrace BStarLongWork BStarLongFixedRouting
open BStarH6WordChart BStarH6Ordinal BStarAcquireAnchors BStarAcquireLiteralChain
open BStarCustodyCuts BStarGrantWriterHistory BStarLongLayout BStarLongClaims BStarOperandBank
open BStarCycleGeometry

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "Site" => LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "Raw" => Fin n → Site
local notation "rows" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "step" => AllSizeS1Geometry.step rows
local notation "rawRun" => BStarResetSchedule.run step

/-- Read the selected native record at every indexed header of the fixed
physical layout. -/
noncomputable def literalClockCfg {h : Fin n → Bool} (hh : ∃ i, h i = true)
    (x : Raw) (i : Fin (total h)) : NativeRecord :=
  BStarNativePointwise.readRecord (r := r) x (atIndex hh i).val

/-- Every selected decoder output is in the native tick range, even when
the physical bytes originally contained an erroneous upper-half tick. -/
theorem decodeBank_wellFormed (hr : 1 ≤ r) (bank : Bank) (side : Fin 3) :
    Recover.StageTwo.WellFormedRecord (modulus r) (decodeBank r bank side) := by
  let tick := bank.digits side 0 % modulus r
  let err := bank.hdr side 0
  have hm : 16 ^ 1 ≤ modulus r := Nat.pow_le_pow_right (by decide) hr
  have hpos : 0 < modulus r := by omega
  have hhalf : 0 < modulus r / 2 := by omega
  change (if err && decide (modulus r / 2 ≤ tick) then 0 else tick) < modulus r ∧
    (err = true → (if err && decide (modulus r / 2 ≤ tick) then 0 else tick) < modulus r / 2)
  by_cases he : (err && decide (modulus r / 2 ≤ tick)) = true
  · simp only [if_pos he]
    exact ⟨hpos, fun _ => hhalf⟩
  · simp only [if_neg he]
    refine ⟨Nat.mod_lt _ hpos, ?_⟩
    intro herr
    have hnot : ¬ modulus r / 2 ≤ tick := by
      intro hle
      exact he (by simp [herr, hle])
    exact Nat.lt_of_not_ge hnot

/-- A clock chart begins with well-formed records by total decoding of the
actual selected banks. -/
theorem literalClockCfg_wellFormed (hr : 1 ≤ r)
    {h : Fin n → Bool} (hh : ∃ i, h i = true) (x : Raw) :
    Recover.StageTwo.WellFormed (modulus r) (literalClockCfg hh x) := by
  intro i
  unfold literalClockCfg BStarNativePointwise.readRecord
  exact decodeBank_wellFormed hr _ _

/-- The decoder supplies both snapshot bounds for every selected bank. -/
theorem literalClockCfg_banksBounded
    {h : Fin n → Bool} (hh : ∃ i, h i = true) (x : Raw) :
    ClockHead.ClockBanksBounded (heightMod r) (literalClockCfg hh x) := by
  let banks := fun i : Fin (total h) =>
    let j := (atIndex hh i).val
    BStarNativeDecodedPublication.centerView
      (BStarNativeSelectorOutput.visible x j (BStarOperandSites.sites (r := r) j))
  exact ClockHead.clockBanksBounded_decode r banks (fun _ => 1)

/-- Conjugate a physical header update by its canonical cyclic index. -/
theorem indexed_header_activate
    {h : Fin n → Bool} (hh : ∃ i, h i = true)
    (cfg : Header h → NativeRecord) (i : Fin (total h)) (bit : Bool) :
    (fun j => BStarNativePortGeometry.activate (r := r) hh cfg (atIndex hh i) bit
      (atIndex hh j)) =
      Recover.StageThree.activate (heightMod r) (modulus r) (total_pos h hh)
        (fun j => cfg (atIndex hh j)) i bit := by
  classical
  funext j
  by_cases he : j = i
  · subst j
    unfold BStarNativePortGeometry.activate Recover.StageThree.activate
    simp only
    rw [← BStarLogicalConjugacy.atIndex_center hh i, BStarLogicalConjugacy.atIndex_left,
      BStarLogicalConjugacy.atIndex_right]
  · have hne : atIndex hh j ≠ atIndex hh i := by
      intro same
      exact he ((index_atIndex hh j).symm.trans
        ((congrArg (index hh) same).trans (index_atIndex hh i)))
    simp only [BStarNativePortGeometry.activate, Recover.StageThree.activate, if_neg hne,
      if_neg he]

/-- One raw mark after the custody cut is silent or publishes exactly the
receipt-driven activation at its unique indexed header. -/
theorem indexed_literal_mark_logical {base initial : Raw}
    (u v tail : List (Fin n)) (cuts : CutFacts hp base initial u v)
    (hh : ∃ i, oldH6 rows base i = true) (sep : ∀ e : Fin n, e ≠ rightNeighbor e)
    (Q : Raw → Prop) (init : Q initial)
    (fiber : ∀ y, Q y → ∀ i, BStarLongFixedRouting.Layout rows base i = BStarLongFixedRouting.Layout rows y i)
    (closed : ∀ y e, Q y → Q (step y e)) (mark : Fin n) (hr : 3 ≤ r)
    (flags : ∀ i, (longGeometry rows (base i)).inside = decide (oldOrdinal rows base hh i < r) ∧
      (longGeometry rows (base i)).last = decide (oldOrdinal rows base hh i + 1 = r))
    (notShort : ∀ j, oldH6 rows base (rightNeighbor j) = true →
      r ≤ oldOrdinal rows base hh j + 1) :
    let old := rawRun initial ((u ++ v) ++ tail)
    let fresh := step old mark
    let m := total (oldH6 rows base)
    (NoPublication hp old mark mark ∧ literalClockCfg hh fresh = literalClockCfg hh old) ∨
      (¬ NoPublication hp old mark mark ∧
        ∃ (i : Fin m) (delta : Bool), (atIndex hh i).val = mark ∧
          literalClockCfg hh fresh =
            Recover.StageThree.activate (heightMod r) (modulus r)
              (total_pos (oldH6 rows base) hh) (literalClockCfg hh old) i delta) := by
  let old := rawRun initial ((u ++ v) ++ tail)
  let fresh := step old mark
  let h := oldH6 rows base
  let project := fun cfg : Header h → NativeRecord =>
    fun i : Fin (total h) => cfg (atIndex hh i)
  have hm := BStarNativePortGeometry.actual_mark_logical hp u v tail cuts hh sep Q init
    fiber closed mark hr flags notShort
  rcases hm with ⟨quiet, frame⟩ | ⟨pub, center, owner, receipt, location, _, _, moved⟩
  · exact Or.inl ⟨quiet, congrArg project frame⟩
  · let ports := fun j : Fin 3 =>
      (endpoint h hh owner ⟨j.val, Nat.lt_trans j.isLt (by decide : 3 < 11)⟩).1
    let bank := bankAt (r := r) old ports
    let delta := (nativeSpec r bank).1 && decide (receipt.argument.toNat % 2 = 1)
    let i := index hh center
    refine Or.inr ⟨pub, i, delta, ?_, ?_⟩
    · change (atIndex hh (index hh center)).val = mark
      rw [atIndex_index, location]
    · let before : Header h → NativeRecord := fun j =>
        BStarNativePointwise.readRecord (r := r) old j.val
      have moved' :
          (fun j : Header h => BStarNativePointwise.readRecord (r := r) fresh j.val) =
            BStarNativePortGeometry.activate (r := r) hh before center delta := moved
      change literalClockCfg hh fresh =
        Recover.StageThree.activate (heightMod r) (modulus r) (total_pos h hh)
          (fun j => before (atIndex hh j)) i delta
      refine (congrArg project moved').trans ?_
      have hi : atIndex hh i = center := atIndex_index hh center
      change (fun j => BStarNativePortGeometry.activate (r := r) hh before center delta
        (atIndex hh j)) = _
      rw [← hi]
      exact indexed_header_activate (r := r) hh before i delta

end LiteralPublication

/-- Choose the clock label certified by a single physical mark. The
publication relation determines the presence and site of a label, even
when the state update itself stutters. -/
theorem exists_publication_action {n m B M : Nat} {hm : 0 < m}
    (header : Fin m → Fin n) (hinj : Function.Injective header)
    (before fresh : Fin m → NativeRecord) (e : Fin n) (publication : Prop)
    (hmark : (¬ publication ∧ fresh = before) ∨
      (publication ∧ ∃ (i : Fin m) (b : Bool), header i = e ∧
        fresh = Recover.StageThree.activate B M hm before i b)) :
    ∃ action : Option (Fin m × Bool),
      (fresh = match action with
        | none => before
        | some v => Recover.StageThree.activate B M hm before v.1 v.2) ∧
      ∀ i, (∃ b, action = some (i,b)) ↔ e = header i ∧ publication := by
  rcases hmark with ⟨hn, hcfg⟩ | ⟨hp, j, b, hj, hcfg⟩
  · exact ⟨none, hcfg, fun i => by simp [hn]⟩
  · refine ⟨some (j,b), hcfg, fun i => ?_⟩
    constructor
    · rintro ⟨c, hc⟩
      have hij := congrArg Prod.fst (Option.some.inj hc)
      exact ⟨hj.symm.trans (congrArg header hij), hp⟩
    · rintro ⟨hi, _⟩
      have hij := hinj (hj.trans hi)
      exact ⟨b, by rw [hij]⟩

end L4.Height.G9Wire
