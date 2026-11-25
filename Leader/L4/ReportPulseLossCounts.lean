import Leader.L4.ReportPulseWarmup
import Leader.L4.ReportServiceMesh

namespace L4.ReportPulseLossCounts
open Height FourLossStickyClock ReportWindowCounts ReportLossArithmetic
open AdviceBandRadiusBudget AllSizeProtocol PhysicalCustody
open ReportByteRows ReportPulseRaw ReportPulseWarmup ReportPulseWait
variable {X : Type} {n m : Nat}

private theorem extend_count (step : X→Fin n→X) (Good : X→Prop)
    (stay : ∀ x e, Good x→Good (step x e)) (loss : X→List (Fin n)→Prop)
    (x : X) (G : Good x) (a b B K A : Nat) (fit : a+b≤B)
    (cap : ∀ y, Good y→K*badCount (loss y) b≤A*n^b) :
    K*badCount (windowBad step loss x a b) B≤A*n^B := by
  have H := window_bad_count step Good loss stay x G a b (B-(a+b)) K (A*n^b) cap
  have E : a+b+(B-(a+b))=B := by omega
  have F : a+(B-(a+b))+b=B := by omega
  rw [E] at H
  calc
    _ ≤ n^(a+(B-(a+b)))*(A*n^b) := H
    _ = A*(n^(a+(B-(a+b)))*n^b) := by ac_rfl
    _ = _ := by rw [←Nat.pow_add,F]

def warmMiss (raw : X→Fin n→X) (p : Params) (bytes : X→BitVec p.w)
    (x : X) (w : List (Fin n)) : Prop :=
  ¬(runWord (warmNext raw p bytes) (warmInit p bytes x) w).2=true

theorem warm_loss_count {raw : X→Fin n→X} {Q : X→Prop}
    (rho : Nat) (N : 0<n) (p : Params) (P : p.streak=trialJ rho)
    (pos : 0<p.streak) (a b : Fin m→Fin n) (A : ∀ i,rightNeighbor (a i)=b i)
    (D : ∀ i,a i≠b i) (bytes : Fin m→X→BitVec p.w)
    (F : ∀ i,Wire raw (b i) Q p (bytes i)) (stay : ∀ x e,Q x→Q (raw x e))
    (M : m≤9*trialH rho) (x : X) (G : Q x) :
    8*badCount (fun w=>∃ i,windowBad raw (warmMiss raw p (bytes i)) x 0 (n*hSize rho/2) w)
      (n*trialU rho) ≤ n^(n*trialU rho) := by
  let l := n*hSize rho/2
  let B := n*trialU rho
  let j := hSize rho/(6*(trialJ rho+2))
  have Fit : j*(3*n*(p.streak+2))≤l := by
    dsimp [j]
    rw [P,←warm_blocks (n:=n) N]
    exact Nat.div_mul_le_self _ _
  have L : 0+l≤B := by
    have H : hSize rho≤trialU rho := by have := warm_gap_large rho; omega
    simp only [Nat.zero_add]
    exact Nat.le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_left n H)
  let loss := fun i : Fin m => windowBad raw (warmMiss raw p (bytes i)) x 0 l
  have per (i : Fin m) : 2^j*badCount (loss i) B≤n^B := by
    apply Nat.le_trans (extend_count raw Q stay _ x G 0 l B (2^j) 1 L ?_)
    · simp
    · intro y Y
      unfold warmMiss; simpa only [Nat.one_mul] using wire_warm_tail (F i) (a i) (A i) (D i) pos y Y l j Fit
  have U := ReportServiceMesh.scaled_union loss B (2^j) (n^B) per
  have E : 8*m≤2^j := Nat.le_trans (Nat.mul_le_mul_left 8 M) (Nat.le_of_lt (warm_loss_lt rho))
  apply Nat.le_of_mul_le_mul_left _ (Nat.pow_pos (by decide) : 0<2^j)
  calc
    2^j*(8*badCount (fun w=>∃ i,loss i w) B) = 8*(2^j*badCount (fun w=>∃ i,loss i w) B) := by ac_rfl
    _ ≤ 8*(m*n^B) := Nat.mul_le_mul_left _ U
    _ ≤ 2^j*n^B := by rw [←Nat.mul_assoc]; exact Nat.mul_le_mul_right _ E

def pulseMiss (raw : X→Fin n→X) (paints : X→Fin n→Bool)
    (x : X) (w : List (Fin n)) : Prop :=
  ¬(runWord (monitor raw paints) (x,false) w).2=true

private theorem local_miss (raw : X→Fin n→X) (paints : X→Fin n→Bool)
    (x : X) (A b : Nat)
    (H : L4.IIDExpectedHittingTimeAtMost (monitor raw paints) (fun y=>y.2=true) (x,false) A) :
    b*badCount (pulseMiss raw paints x) b≤A*n^b := by
  have U := miss_count raw paints x A b H
  have E : badCount (pulseMiss raw paints x) b = wordSum (fun w =>
      if (runWord (monitor raw paints) (x,false) w).2=true then 0 else 1) b := by
    unfold badCount
    apply wordSum_congr_fun
    intro w
    unfold pulseMiss
    by_cases P : (runWord (monitor raw paints) (x,false) w).2=true <;> simp [P]
  rw [E]
  exact U

/-- Each index selects one literal inward-rounded middle window; its
starting state is the actual raw state on the original tape. -/
theorem middle_loss_count (raw : X→Fin n→X) (Q : X→Prop)
    (stay : ∀ x e,Q x→Q (raw x e)) (rho : Nat) (N : 0<n)
    (x : X) (G : Q x) (a b : Fin m→Nat) (paints : Fin m→X→Fin n→Bool)
    (fit : ∀ i,a i+b i≤n*trialU rho)
    (size : ∀ i,n*trialU rho≤10*b i)
    (M : m≤10*trialH rho*trialJ rho)
    (means : ∀ i y,Q y→L4.IIDExpectedHittingTimeAtMost
      (monitor raw (paints i)) (fun y=>y.2=true) (y,false) (4*n*2^(trialJ rho))) :
    8*badCount (fun w=>∃ i,windowBad raw (pulseMiss raw (paints i)) x (a i) (b i) w)
      (n*trialU rho) ≤ n^(n*trialU rho) := by
  let B := n*trialU rho
  let A := 10*(4*n*2^(trialJ rho))
  let loss := fun i : Fin m => windowBad raw (pulseMiss raw (paints i)) x (a i) (b i)
  have per (i : Fin m) : B*badCount (loss i) B≤A*n^B := by
    apply extend_count raw Q stay _ x G _ _ _ _ _ (fit i)
    intro y Y
    calc
      _ ≤ (10*b i)*badCount (pulseMiss raw (paints i) y) (b i) :=
        Nat.mul_le_mul_right _ (size i)
      _ ≤ A*n^(b i) := by
        rw [show A*n^(b i) = 10*((4*n*2^(trialJ rho))*n^(b i)) by dsimp [A]; ac_rfl]
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 10 (local_miss raw _ y _ (b i) (means i y Y))
  have U := ReportServiceMesh.scaled_union loss B B (A*n^B) per
  have K : 8*(m*A)≤B := by
    calc
      _ ≤ 8*((10*trialH rho*trialJ rho)*A) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ M)
      _ = n*(8*(400*trialH rho*trialJ rho*2^(trialJ rho))) := by
        unfold A
        rw [show 400=10*10*4 by decide]
        ac_rfl
      _ ≤ B := Nat.mul_le_mul_left _ (Nat.le_of_lt (miss_loss_lt rho))
  apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos N (by have := warm_gap_large rho; omega) : 0<B)
  calc
    B*(8*badCount (fun w=>∃ i,loss i w) B) = 8*(B*badCount (fun w=>∃ i,loss i w) B) := by ac_rfl
    _ ≤ 8*(m*(A*n^B)) := Nat.mul_le_mul_left _ U
    _ ≤ B*n^B := by rw [show 8*(m*(A*n^B))=(8*(m*A))*n^B by ac_rfl]; exact Nat.mul_le_mul_right _ K

open ReportServiceMesh ReportResetRawHooks

def sheetParams (d : Sheet) (s : Nat) : Params :=
  match d with
  | .first => P1 s
  | .second => P2 s

def sheetBytes {s n : Nat} (d : Sheet) (b : Fin n) :
    Raw s n→BitVec (sheetParams d s).w :=
  match d with
  | .first => fun x=>(x b).report1
  | .second => fun x=>(x b).report2

def frozenHeader {s n : Nat} (d : Sheet) (b : Fin n) (x : Raw s n) : Prop :=
  match d with
  | .first => (oldHeaders (rows s) (x b)).h4=true
  | .second => (oldHeaders (rows s) (x b)).h5=true

theorem sheet_warm_loss_count {s n m : Nat} (d : Sheet) (N : 0<n)
    (Q : Raw s n→Prop) (stay : ∀ x e,Q x→Q (rawNext s x e))
    (a b : Fin m→Fin n) (A : ∀ i,rightNeighbor (a i)=b i) (D : ∀ i,a i≠b i)
    (freeze : ∀ i y,Q y→frozenHeader d (b i) y)
    (M : m≤9*trialH (meshRadius d s)) (x : Raw s n) (G : Q x) :
    8*badCount
      (fun w=>∃ i,windowBad (rawNext s) (warmMiss (rawNext s) (sheetParams d s) (sheetBytes d (b i))) x
        0 (n*hSize (meshRadius d s)/2) w) (n*trialU (meshRadius d s))
      ≤ n^(n*trialU (meshRadius d s)) := by
  apply warm_loss_count _ N _ _ _ a b A D _ _ stay M x G
  · cases d <;> rfl
  · cases d
    · exact streak_pos s
    · exact streak_pos (radiusTwo s)
  · intro i
    cases d
    · exact wire1 (b i) Q stay (freeze i)
    · exact wire2 (b i) Q stay (freeze i)

/-- Inward-rounded starts and lengths for the two designated windows. -/
def middleStart (B : Nat) (late : Bool) : Nat :=
  if late then ceilDiv (3*B) 5 else ceilDiv B 5

def middleEnd (B : Nat) (late : Bool) : Nat :=
  if late then 4*B/5 else 2*B/5

def middleLength (B : Nat) (late : Bool) : Nat :=
  middleEnd B late - middleStart B late

theorem middle_layout (B : Nat) (G : 20≤B) (late : Bool) :
    middleStart B late+middleLength B late≤B ∧ B≤10*middleLength B late := by
  have H := middle_windows B G
  cases late
  · have S := H.1
    simp only [middleStart,middleEnd,middleLength,Bool.false_eq_true,if_false] at ⊢
    unfold ceilDiv at *
    omega
  · have S := H.2
    simp only [middleStart,middleEnd,middleLength,if_true] at ⊢
    unfold ceilDiv at *
    omega

theorem sheet_middle_loss_count {s n m : Nat} (d : Sheet) (N : 0<n)
    (Q : Raw s n→Prop) (stay : ∀ x e,Q x→Q (rawNext s x e))
    (a b : Fin m→Fin n) (A : ∀ i,rightNeighbor (a i)=b i) (D : ∀ i,a i≠b i)
    (freeze : ∀ i y,Q y→frozenHeader d (b i) y)
    (M : m≤10*trialH (meshRadius d s)*trialJ (meshRadius d s))
    (B20 : 20≤n*trialU (meshRadius d s)) (late : Fin m→Bool) (x : Raw s n) (G : Q x) :
    let B := n*trialU (meshRadius d s)
    8*badCount (fun w=>∃ i,windowBad (rawNext s)
      (pulseMiss (rawNext s) (countedPaint (b i) (sheetParams d s) (sheetBytes d (b i)))) x
      (middleStart B (late i)) (middleLength B (late i)) w) B ≤ n^B := by
  dsimp only
  apply middle_loss_count (rawNext s) Q stay _ N x G _ _ _
    (fun i=>(middle_layout _ B20 (late i)).1) (fun i=>(middle_layout _ B20 (late i)).2) M
  intro i y Y
  cases d
  · exact report1_mean (a i) (b i) (A i) (D i) Q stay (freeze i) y Y
  · exact report2_mean (a i) (b i) (A i) (D i) Q stay (freeze i) y Y

end L4.ReportPulseLossCounts
