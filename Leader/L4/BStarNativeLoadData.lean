import Leader.L4.BStarNativeLoadReady
import Leader.L4.BStarNativeLoadBankWords
import Leader.L4.BStarNativeCanonicalSites

namespace L4.BStarNativeLoadData
open AllSizeProtocol BStarTrace BStarLongWork BStarLongLayout BStarLongArithmetic
open BStarNativeReceiptTape BStarNativeLoadTours BStarNativeZeroHead BStarLongSignatures
open BStarNumericChartCoverage BStarNativeCanonicalSites BStarH6WordChart
open BStarResetChartTouch BStarLongFixedRouting BStarGeneratedBandScan BStarGeneratedOwner
open BStarCopyRightStrip (addr)
open BStarNativeLoadReady BStarNativeLoadBankWords BStarAcquireVisitOrder BStarAcquireLiteralChain
open L4.Compiler.Native L4.Compiler.Digits

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

theorem pc_window {base x : X} {addr : Nat→Pos n} {len start count : Nat}
    {w : List (Fin n)} (T : NativeTape hp base addr len x start w count)
    (atStart : pc x (addr 0).1=start) :
    ∀ u v,w=u++v → start≤pc (run x u) (addr 0).1 ∧ pc (run x u) (addr 0).1≤start+count := by
  induction T with
  | @done x w op _ _ flat =>
    intro u v E
    rw [flat u v E,atStart]
    omega
  | @take x op pre tail e k _ flat _ hit rest ih =>
    intro a b E
    rcases List.append_eq_append_iff.mp E with ⟨v,F,H⟩|⟨v,F,H⟩
    · rcases v with _|⟨m,v⟩
      · simp only [List.append_nil] at F
        rw [F,hit.2.2.1]
        omega
      · have EM := List.cons.inj H.symm
        have hm : m=e := EM.1
        subst m
        have r := ih hit.2.2.2.1 v b EM.2.symm
        rw [F,BStarResetSchedule.run_append]
        change op≤pc (run (step (run x pre) e) v) (addr 0).1 ∧
          pc (run (step (run x pre) e) v) (addr 0).1≤op+(k+1)
        omega
    · rw [flat a v F,atStart]
      omega

/-- Derive the real fixed digit-site map from one literal LOAD tour. -/
theorem chart_sites {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (T : NativeTape hp base (fun j=>S.getD j fall) len x 13 w 395)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (BStarH6Ordinal.oldOrdinal B base hh i<r))
    (noShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r≤BStarH6Ordinal.oldOrdinal B base hh i+1) :
    ∃ L : (significantSites hp base (fun j=>S.getD j fall) len).length=r,
      ∀ j : Fin r,digitSite hp base (fun i=>S.getD i fall) len r L j=addr (S.getD len fall).1 j.val := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,⟨ds,A,_⟩⟩ := all_load_sweeps hp C sep T 0 0
  have L := significant_length hp C A flags noShort
  exact ⟨L,canonical_sites hp C A flags noShort L⟩

theorem words_on_tape {base x : X} {slot : Nat→Pos n} {len : Nat}
    {w : List (Fin n)} (site : Fin r→Fin n) (bank : Bank)
    (words : Fin 3 → Fin 9 → Word r)
    (V : ∀ q f, val (words q f)=bank.digits q f)
    (D : ∀ q f,∃ p e t,w=p++e::t ∧ Hit hp base slot len (run x p) e (loadOp q f) ∧
      ∀ j, num (step (run x p) e (site j)).long (loadNode q f)=(words q f j).val) :
    ∀ q f,∃ p e t,w=p++e::t ∧ Hit hp base slot len (run x p) e (loadOp q f) ∧
      ∀ s,wordAt (step (run x p) e) site (loadNode q f) s=bank.digits q f%16^r := by
  intro q f
  obtain ⟨p,e,t,W,H,E⟩ := D q f
  have M : bank.digits q f<16^r := V q f ▸ value_bound (words q f)
  exact ⟨p,e,t,W,H,word_from_nibbles _ site _ _ _ E ((V q f).trans (Nat.mod_eq_of_lt M).symm)⟩

#print axioms pc_window
#print axioms chart_sites
#print axioms words_on_tape
end L4.BStarNativeLoadData
