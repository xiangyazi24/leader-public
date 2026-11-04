import Leader.PPL.Modes.ConstructWindowEncounterCount


namespace PPL.Modes.Lemma5


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability


/--
A one-n block for the weighted scheduler base.


Applying the public RawCounts bound to 3*n gives
  (3*n+2)^(3*n) <= 8*(3*n)^(3*n).
Taking the cube comparison in Nat yields the deliberately weaker but
convenient one-block estimate below.
-/
private theorem encounterScale_oneBlock
    (n : Nat) (hn3 : 3 <= n) :
    (n * 3 + 2) ^ n <= 3 * (n * 3) ^ n := by
  have hbase :=
    addTwo_pow_self_le_eight_mul_pow_self
      (n * 3) (by omega)
  have hcube :
      ((n * 3 + 2) ^ n) ^ 3 <=
        8 * (((n * 3) ^ n) ^ 3) := by
    simpa only [Nat.pow_mul] using hbase
  by_cases hgood :
      (n * 3 + 2) ^ n <= 3 * (n * 3) ^ n
  · exact hgood
  · have hlt :
        3 * (n * 3) ^ n < (n * 3 + 2) ^ n := by
      omega
    have hle :
        3 * (n * 3) ^ n <= (n * 3 + 2) ^ n :=
      Nat.le_of_lt hlt
    have hcubed :
        (3 * (n * 3) ^ n) ^ 3 <=
          ((n * 3 + 2) ^ n) ^ 3 :=
      Nat.pow_le_pow_left hle 3
    have hbad :
        27 * (((n * 3) ^ n) ^ 3) <=
          8 * (((n * 3) ^ n) ^ 3) := by
      calc
        27 * (((n * 3) ^ n) ^ 3) =
            (3 * (n * 3) ^ n) ^ 3 := by
          have h3 : (3 : Nat) ^ 3 = 27 := by
            decide
          calc
            27 * (((n * 3) ^ n) ^ 3) =
                3 ^ 3 * (((n * 3) ^ n) ^ 3) := by
              rw [h3]
            _ =
                (3 * (n * 3) ^ n) ^ 3 :=
              (Nat.mul_pow 3 ((n * 3) ^ n) 3).symm
        _ <= ((n * 3 + 2) ^ n) ^ 3 := hcubed
        _ <= 8 * (((n * 3) ^ n) ^ 3) := hcube
    have hy : 0 < (n * 3) ^ n :=
      Nat.pow_pos (by omega)
    have hy3 : 0 < ((n * 3) ^ n) ^ 3 :=
      Nat.pow_pos hy
    omega


/--
Symbolic corner bound for the only large concrete cases that made kernel
decide recurse through enormous powers in the original draft.


For psi=3 and c=3, D=72 and K=193. Twenty-four three-blocks give the
2^72 scheduler-ratio envelope. The remaining coefficient is handled from
3^5 <= 2^8, leaving only the small bound n^2 * 27 <= 2^11 for n <= 8.
-/
private theorem encounterScale_cornerPsi3
    (n : Nat) (hn3 : 3 <= n) (hn8 : n <= 8) :
    n * n * (3 * n + 2) ^ (72 * n) <=
      2 * n ^ (72 * n) *
        (4 ^ 193 * 3 ^ (72 * n - 193)) := by
  have hblock :
      (3 * n + 2) ^ (3 * n) <=
        8 * (3 * n) ^ (3 * n) :=
    addTwo_pow_self_le_eight_mul_pow_self
      (3 * n) (by omega)


  have hpowRaw :=
    Nat.pow_le_pow_left hblock 24
  have hpow :
      (3 * n + 2) ^ ((3 * n) * 24) <=
        8 ^ 24 * (3 * n) ^ ((3 * n) * 24) := by
    simpa only [Nat.mul_pow, Nat.pow_mul]
      using hpowRaw


  have hExp : (3 * n) * 24 = 72 * n := by
    omega


  have h8 :
      8 ^ 24 = 2 ^ 72 := by
    calc
      8 ^ 24 = (2 ^ 3) ^ 24 := by
        rfl
      _ = 2 ^ (3 * 24) :=
        (Nat.pow_mul 2 3 24).symm
      _ = 2 ^ 72 := by
        rfl


  have hN :
      (3 * n + 2) ^ (72 * n) <=
        2 ^ 72 *
          (3 ^ (72 * n) * n ^ (72 * n)) := by
    calc
      (3 * n + 2) ^ (72 * n) =
          (3 * n + 2) ^ ((3 * n) * 24) := by
        rw [hExp]
      _ <=
          8 ^ 24 * (3 * n) ^ ((3 * n) * 24) :=
        hpow
      _ =
          8 ^ 24 * (3 * n) ^ (72 * n) := by
        rw [hExp]
      _ =
          2 ^ 72 *
            (3 ^ (72 * n) * n ^ (72 * n)) := by
        rw [h8, Nat.mul_pow]


  have h35 :
      (3 : Nat) ^ 5 <= 2 ^ 8 := by
    decide


  have h190Raw :=
    Nat.pow_le_pow_left h35 38
  have h190 :
      3 ^ 190 <= 2 ^ 304 := by
    rw [← Nat.pow_mul, ← Nat.pow_mul] at h190Raw
    exact h190Raw


  have h193 :
      3 ^ 193 <= 27 * 2 ^ 304 := by
    calc
      3 ^ 193 =
          3 ^ 3 * 3 ^ 190 := by
        rw [← Nat.pow_add]
      _ <=
          3 ^ 3 * 2 ^ 304 :=
        Nat.mul_le_mul_left (3 ^ 3) h190
      _ =
          27 * 2 ^ 304 := by
        rfl


  have hnn :
      n * n <= 64 := by
    have hh := Nat.mul_le_mul hn8 hn8
    simpa using hh


  have hcoefN :
      n * n * 27 <= 2 ^ 11 := by
    have hh :=
      Nat.mul_le_mul_right 27 hnn
    exact Nat.le_trans hh (by decide)


  have hcoef :
      n * n * 2 ^ 72 * 3 ^ 193 <=
        2 * 4 ^ 193 := by
    have h4 :
        4 ^ 193 = 2 ^ 386 := by
      calc
        4 ^ 193 = (2 ^ 2) ^ 193 := by
          rfl
        _ = 2 ^ (2 * 193) :=
          (Nat.pow_mul 2 2 193).symm
        _ = 2 ^ 386 := by
          rfl
    have hright :
        2 ^ 387 = 2 * 4 ^ 193 := by
      rw [h4]
      simpa using
        (Nat.pow_add 2 1 386)
    calc
      n * n * 2 ^ 72 * 3 ^ 193 <=
          n * n * 2 ^ 72 *
            (27 * 2 ^ 304) :=
        Nat.mul_le_mul_left
          (n * n * 2 ^ 72) h193
      _ =
          (n * n * 27) *
            (2 ^ 72 * 2 ^ 304) := by
        ac_rfl
      _ <=
          2 ^ 11 *
            (2 ^ 72 * 2 ^ 304) :=
        Nat.mul_le_mul_right
          (2 ^ 72 * 2 ^ 304) hcoefN
      _ =
          2 ^ 11 * 2 ^ (72 + 304) := by
        exact
          congrArg
            (fun x : Nat => 2 ^ 11 * x)
            (Nat.pow_add 2 72 304).symm
      _ =
          2 ^ (11 + (72 + 304)) :=
        (Nat.pow_add 2 11 (72 + 304)).symm
      _ =
          2 ^ 387 := by
        rfl
      _ =
          2 * 4 ^ 193 :=
        hright


  have hTK : 193 <= 72 * n := by
    omega


  have h3split :
      3 ^ (72 * n) =
        3 ^ (72 * n - 193) * 3 ^ 193 := by
    calc
      3 ^ (72 * n) =
          3 ^ ((72 * n - 193) + 193) := by
        apply congrArg (fun z : Nat => 3 ^ z)
        exact (Nat.sub_add_cancel hTK).symm
      _ =
          3 ^ (72 * n - 193) * 3 ^ 193 :=
        Nat.pow_add 3 (72 * n - 193) 193


  have hNscaled :=
    Nat.mul_le_mul_left (n * n) hN


  calc
    n * n * (3 * n + 2) ^ (72 * n) <=
        n * n *
          (2 ^ 72 *
            (3 ^ (72 * n) * n ^ (72 * n))) :=
      hNscaled
    _ =
        (n * n * 2 ^ 72 * 3 ^ 193) *
          (n ^ (72 * n) *
            3 ^ (72 * n - 193)) := by
      rw [h3split]
      generalize hA72 : (2 : Nat) ^ 72 = A72
      generalize hB193 : (3 : Nat) ^ 193 = B193
      generalize hCtail :
        (3 : Nat) ^ (72 * n - 193) = Ctail
      generalize hNT : n ^ (72 * n) = NT
      rw [← Nat.mul_assoc
        (n * n) A72 ((Ctail * B193) * NT)]
      rw [Nat.mul_comm Ctail B193]
      rw [Nat.mul_assoc B193 Ctail NT]
      rw [Nat.mul_comm Ctail NT]
      rw [← Nat.mul_assoc
        ((n * n) * A72) B193 (NT * Ctail)]
    _ <=
        (2 * 4 ^ 193) *
          (n ^ (72 * n) *
            3 ^ (72 * n - 193)) :=
      Nat.mul_le_mul_right
        (n ^ (72 * n) *
          3 ^ (72 * n - 193)) hcoef
    _ =
        2 * n ^ (72 * n) *
          (4 ^ 193 *
            3 ^ (72 * n - 193)) := by
      generalize hA193 : (4 : Nat) ^ 193 = A193
      generalize hNT : n ^ (72 * n) = NT
      generalize hCtail :
        (3 : Nat) ^ (72 * n - 193) = Ctail
      rw [Nat.mul_assoc 2 A193 (NT * Ctail)]
      rw [← Nat.mul_assoc A193 NT Ctail]
      rw [Nat.mul_comm A193 NT]
      rw [Nat.mul_assoc NT A193 Ctail]
      rw [← Nat.mul_assoc 2 NT (A193 * Ctail)]




/--
Pure-Nat scale comparison left open by Lemma5EncounterCount.


At kappa = 16*c*psi, write
  P = psi*2^psi,
  D = c*P,
  T = n*D,
  K = a+1 = 4*(c-1)*P+1.


The (3n+2)^T/n^T ratio is handled in n-blocks. Three n-blocks
cost at most 8, and one n-block costs at most 3. The remaining 3^K
factor is converted to dyadic scale in five-step blocks via
3^5 <= 2^8. The only two parameter corners where this coarse integer
envelope loses one bit are (c,psi)=(3,2),(3,3); there n is bounded by
4 and 8 respectively. The small cases remain kernel arithmetic, while
the two formerly-recursive n=7,8 cases use the symbolic corner bound above.
-/
theorem lemma5iiEncounterScaleArithmetic :
    Lemma5iiEncounterScaleArithmetic := by
  unfold Lemma5iiEncounterScaleArithmetic
  intro n psi kappa c hn3 hpsi hc hkappa hnpow
  dsimp only


  by_cases hsmall :
      And (c = 3) (Or (psi = 2) (psi = 3))
  · rcases hsmall with ⟨hc3, hp2 | hp3⟩
    · subst c
      subst psi
      rw [hkappa]
      have hn : Or (n = 3) (n = 4) := by
        omega
      rcases hn with hn3' | hn4
      · subst n
        decide
      · subst n
        decide
    · subst c
      subst psi
      rw [hkappa]
      have hn :
          Or (n = 3)
            (Or (n = 4)
              (Or (n = 5)
                (Or (n = 6)
                  (Or (n = 7) (n = 8))))) := by
        omega
      rcases hn with hn3' | hn
      · subst n
        decide
      · rcases hn with hn4 | hn
        · subst n
          decide
        · rcases hn with hn5 | hn
          · subst n
            decide
          · rcases hn with hn6 | hn
            · subst n
              decide
            · rcases hn with hn7 | hn8
              · subst n
                have hT7 :
                    lemma5iiHorizon 7 3 (16 * 3 * 3) =
                      72 * 7 := by
                  decide
                have hK3 :
                    lemma5iiEncounterCap 3 3 + 1 =
                      193 := by
                  decide
                rw [hT7, hK3]
                exact
                  encounterScale_cornerPsi3
                    7 (by decide) (by decide)
              · subst n
                have hT8 :
                    lemma5iiHorizon 8 3 (16 * 3 * 3) =
                      72 * 8 := by
                  decide
                have hK3 :
                    lemma5iiEncounterCap 3 3 + 1 =
                      193 := by
                  decide
                rw [hT8, hK3]
                exact
                  encounterScale_cornerPsi3
                    8 (by decide) (by decide)
  · have hlarge : Or (4 <= c) (4 <= psi) := by
      by_cases hc4 : 4 <= c
      · exact Or.inl hc4
      · have hc3eq : c = 3 := by
          omega
        by_cases hpsi4 : 4 <= psi
        · exact Or.inr hpsi4
        · have hp23 : Or (psi = 2) (psi = 3) := by
            omega
          exact False.elim
            (hsmall (And.intro hc3eq hp23))


    let P : Nat := psi * 2 ^ psi
    let D : Nat := c * P
    let T : Nat := lemma5iiHorizon n psi kappa
    let a : Nat := lemma5iiEncounterCap psi c
    let K : Nat := a + 1


    have hT : T = n * D := by
      dsimp [T, lemma5iiHorizon]
      rw [hkappa]
      have hnum :
          n * (16 * c * psi) =
            (n * c * psi) * 16 := by
        ac_rfl
      rw [hnum]
      have hdiv :
          (n * c * psi) * 16 / 16 =
            n * c * psi := by
        exact
          Nat.mul_div_left
            (n * c * psi) (by decide)
      rw [hdiv]
      dsimp [D, P]
      ac_rfl


    have ha :
        a = 4 * (c - 1) * P := by
      dsimp
        [a, lemma5iiEncounterCap,
          lotteryL7Horizon, P]
      ac_rfl


    have hK :
        K = 4 * (c - 1) * P + 1 := by
      dsimp [K]
      rw [ha]


    let B : Nat := n * 3
    let N : Nat := B + 2


    have hblock3 :
        N ^ (n * 3) <=
          8 * B ^ (n * 3) := by
      simpa [N, B] using
        (addTwo_pow_self_le_eight_mul_pow_self
          (n * 3) (by omega))


    have hblock1 :
        N ^ n <= 3 * B ^ n := by
      simpa [N, B] using
        (encounterScale_oneBlock n hn3)


    let qD : Nat := D / 3
    let rD : Nat := D % 3


    have hrD : rD < 3 := by
      dsimp [rD]
      exact Nat.mod_lt D (by decide)


    have hDqr :
        D = 3 * qD + rD := by
      have hd := Nat.mod_add_div D 3
      dsimp [qD, rD]
      omega


    have hTqr :
        T = (n * 3) * qD + n * rD := by
      rw [hT, hDqr, Nat.mul_add]
      ac_rfl


    have hpow3raw :=
      Nat.pow_le_pow_left hblock3 qD
    have hpow3 :
        N ^ ((n * 3) * qD) <=
          8 ^ qD * B ^ ((n * 3) * qD) := by
      simpa only [Nat.mul_pow, Nat.pow_mul]
        using hpow3raw


    have hpow1raw :=
      Nat.pow_le_pow_left hblock1 rD
    have hpow1 :
        N ^ (n * rD) <=
          3 ^ rD * B ^ (n * rD) := by
      simpa only [Nat.mul_pow, Nat.pow_mul]
        using hpow1raw


    have hraw :
        N ^ T <=
          (8 ^ qD * 3 ^ rD) * B ^ T := by
      have hboth :=
        Nat.mul_le_mul hpow3 hpow1
      calc
        N ^ T =
            N ^ ((n * 3) * qD) *
              N ^ (n * rD) := by
          rw [hTqr, Nat.pow_add]
        _ <=
            (8 ^ qD * B ^ ((n * 3) * qD)) *
              (3 ^ rD * B ^ (n * rD)) := hboth
        _ =
            (8 ^ qD * 3 ^ rD) * B ^ T := by
          rw [hTqr, Nat.pow_add]
          ac_rfl


    have h8q :
        8 ^ qD = 2 ^ (3 * qD) := by
      rw [show (8 : Nat) = 2 ^ 3 by decide,
        ← Nat.pow_mul]


    have h3rD :
        3 ^ rD <= 2 ^ (2 * rD) := by
      calc
        3 ^ rD <= 4 ^ rD :=
          Nat.pow_le_pow_left (by decide) rD
        _ = 2 ^ (2 * rD) := by
          rw [show (4 : Nat) = 2 ^ 2 by decide,
            ← Nat.pow_mul]


    have hcoefD :
        8 ^ qD * 3 ^ rD <=
          2 ^ (D + rD) := by
      calc
        8 ^ qD * 3 ^ rD =
            2 ^ (3 * qD) * 3 ^ rD := by
          rw [h8q]
        _ <=
            2 ^ (3 * qD) * 2 ^ (2 * rD) :=
          Nat.mul_le_mul_left _ h3rD
        _ = 2 ^ (3 * qD + 2 * rD) := by
          rw [Nat.pow_add]
        _ = 2 ^ (D + rD) := by
          apply congrArg (fun z : Nat => 2 ^ z)
          omega


    have hratio :
        N ^ T <=
          2 ^ (D + rD) *
            (3 ^ T * n ^ T) := by
      calc
        N ^ T <=
            (8 ^ qD * 3 ^ rD) * B ^ T :=
          hraw
        _ <=
            2 ^ (D + rD) * B ^ T :=
          Nat.mul_le_mul_right (B ^ T) hcoefD
        _ =
            2 ^ (D + rD) *
              (3 ^ T * n ^ T) := by
          dsimp [B]
          rw [Nat.mul_pow]
          ac_rfl


    have hnn0 :=
      Nat.mul_le_mul hnpow hnpow
    have hnn :
        n * n <= 2 ^ (2 * psi) := by
      calc
        n * n <=
            (2 ^ psi) * (2 ^ psi) := hnn0
        _ = 2 ^ (psi + psi) := by
          rw [Nat.pow_add]
        _ = 2 ^ (2 * psi) := by
          apply congrArg (fun z : Nat => 2 ^ z)
          omega


    have hcoefNN :
        (n * n) * 2 ^ (D + rD) <=
          2 ^ (2 * psi + D + rD) := by
      calc
        (n * n) * 2 ^ (D + rD) <=
            2 ^ (2 * psi) * 2 ^ (D + rD) :=
          Nat.mul_le_mul_right
            (2 ^ (D + rD)) hnn
        _ =
            2 ^ (2 * psi + (D + rD)) := by
          exact
            (Nat.pow_add
              2 (2 * psi) (D + rD)).symm
        _ =
            2 ^ (2 * psi + D + rD) := by
          apply congrArg (fun z : Nat => 2 ^ z)
          omega


    have hratioScaled :=
      Nat.mul_le_mul_left (n * n) hratio


    have hleft :
        n * n * N ^ T <=
          2 ^ (2 * psi + D + rD) *
            3 ^ T * n ^ T := by
      calc
        n * n * N ^ T <=
            (n * n) *
              (2 ^ (D + rD) *
                (3 ^ T * n ^ T)) :=
          hratioScaled
        _ =
            ((n * n) * 2 ^ (D + rD)) *
              (3 ^ T * n ^ T) := by
          ac_rfl
        _ <=
            2 ^ (2 * psi + D + rD) *
              (3 ^ T * n ^ T) :=
          Nat.mul_le_mul_right
            (3 ^ T * n ^ T) hcoefNN
        _ =
            2 ^ (2 * psi + D + rD) *
              3 ^ T * n ^ T := by
          ac_rfl


    have h3split :
        3 ^ T <=
          3 ^ (T - K) * 3 ^ K := by
      by_cases hKT : K <= T
      · calc
          3 ^ T =
              3 ^ ((T - K) + K) := by
            apply congrArg (fun z : Nat => 3 ^ z)
            omega
          _ =
              3 ^ (T - K) * 3 ^ K :=
            Nat.pow_add 3 (T - K) K
          _ <=
              3 ^ (T - K) * 3 ^ K :=
            Nat.mul_le_mul
              (Nat.pow_le_pow_right
                (by decide : 0 < (3 : Nat))
                (Nat.le_refl (T - K)))
              (Nat.pow_le_pow_right
                (by decide : 0 < (3 : Nat))
                (Nat.le_refl K))
      · have hTK : T <= K := by
          omega
        have hsub : T - K = 0 := by
          omega
        rw [hsub, Nat.pow_zero, Nat.one_mul]
        exact
          Nat.pow_le_pow_right (by decide) hTK


    let e : Nat := c - 1
    let Q : Nat := e * P


    have he2 : 2 <= e := by
      dsimp [e]
      omega


    have hcE : c = e + 1 := by
      dsimp [e]
      omega


    have hDalt :
        D = Q + P := by
      dsimp [D, Q]
      rw [hcE, Nat.add_mul, Nat.one_mul]


    have hKalt :
        K = 4 * Q + 1 := by
      calc
        K = 4 * (c - 1) * P + 1 := hK
        _ = 4 * Q + 1 := by
          dsimp [Q, e]
          ac_rfl


    have hsmallMargin :
        5 * P + 10 * psi + 11 <=
          3 * Q := by
      rcases hlarge with hc4 | hpsi4
      · have he3 : 3 <= e := by
          dsimp [e]
          omega
        have hp4 : 4 <= 2 ^ psi := by
          have hp : 2 ^ 2 <= 2 ^ psi :=
            Nat.pow_le_pow_right
              (by decide : 0 < (2 : Nat)) hpsi
          simpa using hp
        have hP4 : 4 * psi <= P := by
          calc
            4 * psi = psi * 4 := by
              ac_rfl
            _ <= psi * 2 ^ psi :=
              Nat.mul_le_mul_left psi hp4
            _ = P := by
              rfl
        have h4P :
            16 * psi <= 4 * P := by
          have hh :=
            Nat.mul_le_mul_left 4 hP4
          calc
            16 * psi = 4 * (4 * psi) := by
              omega
            _ <= 4 * P := hh
        have h10 :
            10 * psi + 11 <= 4 * P := by
          have hlin :
              10 * psi + 11 <= 16 * psi := by
            omega
          exact Nat.le_trans hlin h4P
        have hleftMargin :
            5 * P + 10 * psi + 11 <=
              9 * P := by
          omega
        have hcoef : 9 <= 3 * e := by
          omega
        have hrightMargin :
            9 * P <= 3 * Q := by
          calc
            9 * P <= (3 * e) * P :=
              Nat.mul_le_mul_right P hcoef
            _ = 3 * Q := by
              dsimp [Q]
              ac_rfl
        exact
          Nat.le_trans hleftMargin hrightMargin
      · have hp16 : 16 <= 2 ^ psi := by
          have hp : 2 ^ 4 <= 2 ^ psi :=
            Nat.pow_le_pow_right
              (by decide : 0 < (2 : Nat)) hpsi4
          simpa using hp
        have hP16 :
            16 * psi <= P := by
          calc
            16 * psi = psi * 16 := by
              ac_rfl
            _ <= psi * 2 ^ psi :=
              Nat.mul_le_mul_left psi hp16
            _ = P := by
              rfl
        have h10 :
            10 * psi + 11 <= P := by
          have hlin :
              10 * psi + 11 <=
                16 * psi := by
            omega
          exact Nat.le_trans hlin hP16
        have hleftMargin :
            5 * P + 10 * psi + 11 <=
              6 * P := by
          omega
        have hcoef : 6 <= 3 * e := by
          omega
        have hrightMargin :
            6 * P <= 3 * Q := by
          calc
            6 * P <= (3 * e) * P :=
              Nat.mul_le_mul_right P hcoef
            _ = 3 * Q := by
              dsimp [Q]
              ac_rfl
        exact
          Nat.le_trans hleftMargin hrightMargin


    have hmargin :
        5 * D + 10 * psi + 13 <=
          2 * K := by
      rw [hDalt, hKalt]
      omega


    let qK : Nat := K / 5
    let rK : Nat := K % 5


    have hrK : rK < 5 := by
      dsimp [rK]
      exact Nat.mod_lt K (by decide)


    have hKqr :
        K = 5 * qK + rK := by
      have hk := Nat.mod_add_div K 5
      dsimp [qK, rK]
      omega


    have hqBound :
        2 * psi + D + rD <=
          1 + 2 * qK := by
      omega


    have h35 :
        (3 : Nat) ^ 5 <= 2 ^ 8 := by
      decide


    have hpow5raw :=
      Nat.pow_le_pow_left h35 qK
    have hpow5 :
        3 ^ (5 * qK) <=
          2 ^ (8 * qK) := by
      simpa only [Nat.pow_mul] using hpow5raw


    have h3rK :
        3 ^ rK <= 2 ^ (2 * rK) := by
      calc
        3 ^ rK <= 4 ^ rK :=
          Nat.pow_le_pow_left (by decide) rK
        _ = 2 ^ (2 * rK) := by
          rw [show (4 : Nat) = 2 ^ 2 by decide,
            ← Nat.pow_mul]


    have h3K :
        3 ^ K <=
          2 ^ (8 * qK + 2 * rK) := by
      calc
        3 ^ K =
            3 ^ (5 * qK + rK) := by
          rw [hKqr]
        _ =
            3 ^ (5 * qK) * 3 ^ rK := by
          rw [Nat.pow_add]
        _ <=
            2 ^ (8 * qK) * 2 ^ (2 * rK) :=
          Nat.mul_le_mul hpow5 h3rK
        _ =
            2 ^ (8 * qK + 2 * rK) := by
          rw [Nat.pow_add]


    have hExp :
        (2 * psi + D + rD) +
            (8 * qK + 2 * rK) <=
          1 + 2 * K := by
      omega


    have hscale :
        2 ^ (2 * psi + D + rD) * 3 ^ K <=
          2 * 4 ^ K := by
      calc
        2 ^ (2 * psi + D + rD) * 3 ^ K <=
            2 ^ (2 * psi + D + rD) *
              2 ^ (8 * qK + 2 * rK) :=
          Nat.mul_le_mul_left _ h3K
        _ =
            2 ^
              ((2 * psi + D + rD) +
                (8 * qK + 2 * rK)) := by
          exact
            (Nat.pow_add
              2
              (2 * psi + D + rD)
              (8 * qK + 2 * rK)).symm
        _ <=
            2 ^ (1 + 2 * K) :=
          Nat.pow_le_pow_right (by decide) hExp
        _ = 2 * 4 ^ K := by
          rw [Nat.pow_add, Nat.pow_mul]


    have h3scaled :
        2 ^ (2 * psi + D + rD) *
              3 ^ T * n ^ T <=
          2 ^ (2 * psi + D + rD) *
              (3 ^ (T - K) * 3 ^ K) * n ^ T := by
      have hmul :=
        Nat.mul_le_mul_left
          (2 ^ (2 * psi + D + rD)) h3split
      have hmul' :=
        Nat.mul_le_mul_right (n ^ T) hmul
      simpa only [Nat.mul_assoc] using hmul'


    have hfinal :
        n * n * N ^ T <=
          2 * n ^ T *
            (4 ^ K * 3 ^ (T - K)) := by
      calc
        n * n * N ^ T <=
            2 ^ (2 * psi + D + rD) *
              3 ^ T * n ^ T := hleft
        _ <=
            2 ^ (2 * psi + D + rD) *
              (3 ^ (T - K) * 3 ^ K) *
                n ^ T := h3scaled
        _ =
            (2 ^ (2 * psi + D + rD) * 3 ^ K) *
              n ^ T * 3 ^ (T - K) := by
          ac_rfl
        _ <=
            (2 * 4 ^ K) *
              n ^ T * 3 ^ (T - K) := by
          have hs :=
            Nat.mul_le_mul_right
              (n ^ T * 3 ^ (T - K)) hscale
          simpa only [Nat.mul_assoc] using hs
        _ =
            2 * n ^ T *
              (4 ^ K * 3 ^ (T - K)) := by
          ac_rfl


    simpa only
      [N, B, T, K, a, Nat.mul_comm n 3]
      using hfinal


end PPL.Modes.Lemma5


#print axioms PPL.Modes.Lemma5.lemma5iiEncounterScaleArithmetic


