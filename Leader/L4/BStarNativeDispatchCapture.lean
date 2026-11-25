import Leader.L4.BStarCapturedCompilerInputs
import Leader.L4.BStarNativeReceiptTape

namespace L4.BStarNativeDispatchCapture
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongDoor BStarLongWork BStarLongToken
open BStarAcquireReadout BStarAcquireDigits BStarCaptureDoorHistory BStarAliasFold
open BStarLongArithmetic BStarLongCommand L4.Compiler.Native
open BStarGeneratedBandScan BStarCapturedCompilerInputs

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Transport the three actual ACK header aliases to every cut of
the same admitted live word. In particular no frame assumption is
made about continuations outside this scheduler word. -/
theorem retained (x : X) (root : Fin n) (w : List (Fin n))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (live : LiveWord hp root x w) (bank : Bank)
    (pins : ∀ q d, ((capturedHeader q d).read (x root).long).toNat=(bank.hdr q d).toNat) :
    ∀ u v,w=u++v → ∀ q d,
      ((capturedHeader q d).read (run x u root).long).toNat=(bank.hdr q d).toNat := by
  intro u v W q d
  have L : LiveWord hp root x u := by
    intro a e b E
    have D : w=a++e::(b++v) := by rw [W,E,List.append_assoc]; rfl
    exact live a e (b++v) D
  have H := (retain_blocks hp x root u sep L q).2
  let a : BitVec LW := (x root).long
  let b : BitVec LW := (run x u root).long
  change ((capturedHeader q d).read b).toNat=(bank.hdr q d).toNat
  change (headerBlock q).read b=(headerBlock q).read a at H
  rw [header_bit b q d, H, ←header_bit a q d]
  exact pins q d

open BStarLongFixedRouting BStarResetChartTouch BStarH6WordChart BStarResetMarkAdapter BStarAcquireVisitOrder BStarSeparatorControl BStarAcquireLiteralChain
open BStarGeneratedOwner BStarGeneratedTapeCuts BStarNativeReceiptTape

set_option maxRecDepth 4096

/-- A genuine owner trace entirely in PC13..408 is live for captures.
The only exceptional reflect branch ends at PC6, which contradicts
the actual next cut's compiler band. -/
theorem live_of_band {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {mode fin : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x mode w fin)
    (stable : ∀ u i,Layout B base i=Layout B (run x u) i)
    (band : CompilerBand hp x (S.getD 0 fall).1 w) :
    LiveWord hp (S.getD 0 fall).1 x w := by
  intro u e v W
  obtain ⟨_,_,rest⟩ := split hp u (e::v) (W ▸ T)
  have W' : w=(u++[e])++v := by rw [W,List.append_assoc]; rfl
  have bb := band (u++[e]) v W'
  rw [BStarResetSchedule.run_append] at bb
  let root := (S.getD 0 fall).1
  have lo : 13≤pc (step (run x u) e) root := bb.2.1
  have nxt : Band (step (run x u) e) root := ⟨Nat.le_trans (by decide) lo,bb.2.2⟩
  cases rest with
  | next I E T' =>
    cases T' with
    | endpoint J =>
      rcases reflect hp (x:=run x u) C (stable u) sep e _ _ I J E nxt with h|⟨_,h,_⟩
      · exact h
      · change pc (step (run x u) e) root=6 at h
        omega
    | next J _ _ =>
      rcases reflect hp (x:=run x u) C (stable u) sep e _ _ I J E nxt with h|⟨_,h,_⟩
      · exact h
      · change pc (step (run x u) e) root=6 at h
        omega

/-- The captured center bank selector is similarly retained up to any
legitimate compiler prefix, so the final publication is not granted
a fresh validity assumption. -/
theorem retained_legal (x : X) (root : Fin n) (w : List (Fin n))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (live : LiveWord hp root x w)
    (pin : ((capturedSelector 1).read (x root).long).toNat<3) :
    ∀ u v,w=u++v → ((capturedSelector 1).read (run x u root).long).toNat<3 := by
  intro u v W
  have L : LiveWord hp root x u := by
    intro a e b E
    have D : w=a++e::(b++v) := by rw [W,E,List.append_assoc]; rfl
    exact live a e (b++v) D
  exact (congrArg BitVec.toNat (retain_blocks hp x root u sep L 1).1).symm ▸ pin

end L4.BStarNativeDispatchCapture
