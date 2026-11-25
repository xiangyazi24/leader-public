import Leader.L4.ReportClosePulsePositions
import Leader.L4.ReportPulseFixedPair

namespace L4.ReportPulseJointLoss
open AdviceBandRadiusBudget ReportLossArithmetic FourLossStickyClock
open ReportPulseFixedPair ReportPulseJointCount ReportPulseRecode
open ReportPulseWinsSkeleton ReportPulseRounds ReportPulseWarmup ReportPulseWait ReportByteRows ReportPulseRaw

variable {G X : Type} [DecidableEq G] {n : Nat}

/-- Actual original-tape close event with separate old-pair evaluations.
Each gate's required clean cut lies before its own counted paint. The
same gate can occur twice; the first literal paint supplies its clean cut
for the second count. -/
def closeAt (raw : X→Fin n→X) (put : G×Bool→Fin n) (p : Params)
    (bytes : G→X→BitVec p.w) (x : X) (g h : G) (i j : Nat)
    (w : List (Fin n)) : Prop :=
  ∃ u v tail e f,
    w=((u++[e])++(v++[f]))++tail ∧ u.length=i ∧ u.length+1+v.length=j ∧
    countedPaint (put (g,true)) p (bytes g) (u.foldl raw x) e=true ∧
    countedPaint (put (h,true)) p (bytes h) (((u++[e])++v).foldl raw x) f=true ∧
    (∃ pre rest,u=pre++rest ∧ cleanAt raw p (bytes g) x pre) ∧
    (g≠h → ∃ pre rest,(u++[e])++v=pre++rest ∧ cleanAt raw p (bytes h) x pre)

omit [DecidableEq G] in
theorem closeAt_lt (raw : X→Fin n→X) (put : G×Bool→Fin n) (p : Params)
    (bytes : G→X→BitVec p.w) (x : X) (g h : G) (i j : Nat)
    (w : List (Fin n)) (H : closeAt raw put p bytes x g h i j w) :
    i<j ∧ j<w.length := by
  obtain ⟨u,v,tail,e,f,E,I,J,_⟩ := H
  rw [E]
  simp only [List.length_append,List.length_cons,List.length_nil] at *
  omega

/-- The close loss for a finite census of relevant gates. Its event is
existence of two chronological old-pair completion marks within the
physical distance bound, with the stated actual warm-cut certificates. -/
def closeLoss {m : Nat} (rho : Nat) (gate : Fin m→G)
    (raw : X→Fin n→X) (put : G×Bool→Fin n) (p : Params)
    (bytes : G→X→BitVec p.w) (x : X) (w : List (Fin n)) : Prop :=
  ∃ a b i j, i<n*trialU rho ∧ j<n*trialU rho ∧
    j-i≤3*n*hSize rho ∧ closeAt raw put p bytes x (gate a) (gate b) i j w

theorem actual_close_loss {m : Nat} (rho : Nat) (gate : Fin m→G)
    (raw : X→Fin n→X) (put : G×Bool→Fin n) (inj : Function.Injective put)
    (p : Params) (bytes : G→X→BitVec p.w) (Q : X→Prop)
    (W : ∀ g, Wire raw (put (g,true)) Q p (bytes g))
    (Adj : ∀ g, L4.rightNeighbor (put (g,false))=put (g,true))
    (x : X) (Good : Q x) (s : Phase G)
    (I : ∀ g,s g=phaseOf (readClock p (bytes g) x).phase)
    (S : p.streak=trialJ rho) (J : 0<p.streak) (N : 0<n)
    (Many : m≤9*trialH rho) (L : 2≤n*trialU rho) (K : 2*p.streak≤n*trialU rho) :
    8*badCount (closeLoss rho gate raw put p bytes x) (n*trialU rho)≤n^(n*trialU rho) := by
  let B := n*trialU rho
  let fixed : (Fin m×Fin m×Fin B×Fin (3*n*hSize rho+1))→List (Fin n)→Prop :=
    fun (a,b,i,k) w =>
      ∃ j : Fin B, j.val=i.val+k.val ∧
        closeAt raw put p bytes x (gate a) (gate b) i.val j.val w
  -- For the finite pin family, an out-of-range or equal second pin has
  -- no credited words. A genuine chosen offset determines it uniquely.
  apply ReportClosePulsePositions.deployed_close_count rho m N Many L fixed
  · intro w H
    obtain ⟨a,b,i,j,IB,JB,D,Hit⟩ := H
    have IJ := (closeAt_lt raw put p bytes x _ _ i j w Hit).1
    refine ⟨(a,b,⟨i,IB⟩,⟨j-i,by omega⟩),⟨j,JB⟩,?_,Hit⟩
    dsimp
    omega
  · rintro ⟨a,b,i,k⟩
    classical
    by_cases R : i.val+k.val<B
    · let j : Fin B := ⟨i.val+k.val,R⟩
      by_cases E : i=j
      · have Empty : ∀ w, fixed (a,b,i,k) w → False := by
          intro w T
          obtain ⟨j',J',Hit⟩ := T
          have EQ : j'=j := Fin.ext J'
          subst j'
          have Bad := (closeAt_lt raw put p bytes x _ _ i.val j.val w Hit).1
          rw [E] at Bad
          exact (Nat.lt_irrefl _) Bad
        have Z := badCount_mono (Q:=fun _=>False) Empty B
        have F : badCount (n:=n) (fun _=>False) B=0 := by simp [badCount,Height.wordSum_const_zero]
        rw [F] at Z
        change 2^(2*trialJ rho)*badCount (fixed (a,b,i,k)) B≤n^(B-2)
        rw [Nat.eq_zero_of_le_zero Z,Nat.mul_zero]
        exact Nat.zero_le _
      · have T := fixed_pair_actual (fixed (a,b,i,k)) put inj s bytes W Adj J
          x Good I i j (gate a) (gate b) E K (by
            intro w W'
            obtain ⟨j',J',Hit⟩ := W'
            have EQ : j'=j := Fin.ext J'
            subst j'
            exact Hit)
        simpa only [actualCount,badCount,S] using T
    · have Empty : ∀ w, fixed (a,b,i,k) w → False := by
        intro w T
        obtain ⟨j',J',_⟩ := T
        exact R (J' ▸ j'.isLt)
      have Z := badCount_mono (Q:=fun _=>False) Empty B
      have F : badCount (n:=n) (fun _=>False) B=0 := by simp [badCount,Height.wordSum_const_zero]
      rw [F] at Z
      change 2^(2*trialJ rho)*badCount (fixed (a,b,i,k)) B≤n^(B-2)
      rw [Nat.eq_zero_of_le_zero Z,Nat.mul_zero]
      exact Nat.zero_le _

end L4.ReportPulseJointLoss
