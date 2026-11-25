import Leader.L4.ShortMISPublicationHistoryLocal
import Leader.L4.ShortWriteFlight
import Leader.L4.ShortCommitFlight

namespace L4.ShortMISPublicationFlight
open AllSizeProtocol PhysicalCustody MISByteCodec
open ShortResetChart ShortResetCycle ShortResetMIS1Ring ShortResetForwardH2
open ShortMISEngine ShortMISSheetParked

set_option maxRecDepth 4096
variable {s n : Nat} {h : Fin n → Bool}

theorem write_active_congr (C : Chart h) (cmd : ShortWriteCentreWitness.Cmd)
    (d : Fin 8) (u v : Raw s n) (B : ∀ i, (u i).mis1 = (v i).mis1)
    (f : ShortWriteFlight.Flight) :
    ShortWriteFlight.Active C cmd d u f ↔ ShortWriteFlight.Active C cmd d v f := by
  cases f <;> simp only [ShortWriteFlight.Active, ShortCanonicalReverseChart.Returning,
    ShortCanonicalReverseChart.Rev, ShortCanonicalReverseChart.Wait,
    ShortHelloForward.ClearSuffix, TrailPrefix, bits, ShortEmptyOwnership.Clear, B]

theorem commit_active_congr (C : Chart h) (d : Fin 8) (u v : Raw s n)
    (B : ∀ i, (u i).mis1 = (v i).mis1) (f : ShortCommitFlight.Flight) :
    ShortCommitFlight.Active C d u f ↔ ShortCommitFlight.Active C d v f := by
  cases f <;> simp only [ShortCommitFlight.Active, ShortCanonicalReverseChart.Returning,
    ShortCanonicalReverseChart.Rev, ShortCanonicalReverseChart.Wait,
    ShortHelloForward.ClearSuffix, TrailPrefix, bits, ShortEmptyOwnership.Clear, B]

theorem write_actual_step (P : Params s n) (C : Chart P.h) (N : 9 < n)
    (x : Raw s n) (X : Cached P x)
    (geom : C.a+1<C.L ∧ ∀ k, k<C.L →
      (P.h (nextAt C.root k)=true ∧ C.route.port k=1 ↔ k=C.a))
    (cmd : ShortWriteCentreWitness.Cmd) (d : Fin 8) (D : descValid d.val=true)
    (e : Fin n) (f : ShortWriteFlight.Flight) (L : ShortWriteFlight.live f)
    (A : ShortWriteFlight.Active C cmd d (view P x) f) :
    ShortWriteFlight.Active C cmd d (view P (rawNext s x e))
      (ShortWriteFlight.next C cmd d (view P x) e f) ∧
      (∀ bad, f=.front C.a bad → e=nextAt C.root C.a →
        ShortWriteChartHop.advanceBad cmd d C (view P x) C.a bad=false →
        ShortWriteCentreWitness.CentreEffect cmd d (view P x) e) := by
  have Q := ShortWriteFlight.step_fixed (view P x) C N (view_header P x)
    (by simpa only [view_header] using geom) cmd d D e f L A
  exact ⟨(write_active_congr C cmd d _ (view P (rawNext s x e)) (view_next P x X e) _).mp Q.1, Q.2⟩

theorem commit_actual_step (P : Params s n) (C : Chart P.h) (N : 9 < n)
    (x : Raw s n) (X : Cached P x)
    (geom : C.a-1+1<C.L ∧ ∀ k, k+1<C.L →
      (P.h (rightNeighbor (nextAt C.root k))=true ∧
        C.route.port k=0 ∧ C.route.port (k+1)=1 ↔ k=C.a-1))
    (d : Fin 8) (D : descValid d.val=true)
    (e : Fin n) (f : ShortCommitFlight.Flight) (L : ShortCommitFlight.live f)
    (A : ShortCommitFlight.Active C d (view P x) f) :
    ShortCommitFlight.Active C d (view P (rawNext s x e))
      (ShortCommitFlight.next C d (view P x) e f) ∧
      (∀ p, f=.front (C.a-1) p → e=nextAt C.root (C.a-1) →
        ShortCommitChartHop.advance d C (view P x) (C.a-1) p=.applied →
        ShortCommitChartHop.Publication d (view P x) e) := by
  have Q := ShortCommitFlight.step_fixed (view P x) C N (view_header P x)
    (by simpa only [view_header] using geom) d D e f L A
  exact ⟨(commit_active_congr C d _ (view P (rawNext s x e)) (view_next P x X e) _).mp Q.1, Q.2⟩

#print axioms write_actual_step
#print axioms commit_actual_step
end L4.ShortMISPublicationFlight
