import Leader.L4.Height.QuietBridge
import Leader.L4.Height.RepairStrict
import Leader.L4.Height.ClockMeanAlt

namespace L4.Height.Recover.CoverThree

open Classical
open L4.Compiler.Native
open L4.Height

set_option maxRecDepth 8192
set_option maxHeartbeats 40000000

noncomputable section

structure ClockChain (α : Type) (n m : Nat) (B M : Nat) (hm : 0 < m) where
  next : α → Fin n → α
  cfg : α → Fin m → NativeRecord
  act : α → Fin n → Option (Fin m × Bool)
  lastAct : α → Option (Fin m)
  cfg_next : ∀ x e, cfg (next x e) =
    match act x e with
    | none => cfg x
    | some p => StageThree.activate B M hm (cfg x) p.1 p.2
  last_next : ∀ x e, lastAct (next x e) = (act x e).map Prod.fst

def ClockChain.served
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (i : Fin m) (x : α) : Prop :=
  C.lastAct x = some i

def Src
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (D : Nat) (x : α) : Prop :=
  StageThree.Quiet M hm (C.cfg x) ∧
    StageThree.Frozen M D hm (C.cfg x) ∧
      StageTwo.WellFormed M (C.cfg x)

def Tgt
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (x : α) : Prop :=
  (∀ i, (C.cfg x i).err = false) ∧
    StageThree.Quiet M hm (C.cfg x)

/-! ## Transport of scheduler words to native activations -/

def activationList
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) :
    α → List (Fin n) → List (StageThree.Activation m)
  | _, [] => []
  | x, e :: u =>
      match C.act x e with
      | none => activationList C (C.next x e) u
      | some p => p :: activationList C (C.next x e) u

theorem cfg_runWord
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) :
    ∀ (x : α) (u : List (Fin n)),
      C.cfg (L4.Height.runWord C.next x u) =
        StageThree.runActivations B M hm (C.cfg x)
          (activationList C x u) := by
  intro x u
  induction u generalizing x with
  | nil =>
      rfl
  | cons e u ih =>
      change
        C.cfg (L4.Height.runWord C.next (C.next x e) u) =
          StageThree.runActivations B M hm (C.cfg x)
            (activationList C x (e :: u))
      rw [ih (C.next x e)]
      cases hact : C.act x e with
      | none =>
          have hc := C.cfg_next x e
          simp only [hact] at hc
          simp only [activationList, hact]
          rw [hc]
      | some p =>
          rcases p with ⟨i, delta⟩
          have hc := C.cfg_next x e
          simp only [hact] at hc
          simp only [activationList, hact, StageThree.runActivations]
          rw [hc]

private theorem source_next
    {α : Type} {n m B M D : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M)
    (x : α) (e : Fin n) (hx : Src C D x) :
    Src C D (C.next x e) := by
  unfold Src at hx ⊢
  cases hact : C.act x e with
  | none =>
      have hc := C.cfg_next x e
      simp only [hact] at hc
      rw [hc]
      exact hx
  | some p =>
      rcases p with ⟨i, delta⟩
      have hc := C.cfg_next x e
      simp only [hact] at hc
      have hs := stable_trace_of hM hm
        (quiet_preserved_holds (B := B) (D := D) hM hm)
        (C.cfg x) [(i, delta)] hx.1 hx.2.1 hx.2.2
      have hq :
          StageThree.Quiet M hm
            (StageThree.activate B M hm (C.cfg x) i delta) := by
        simpa [StageThree.runActivations] using hs.2.1
      have hf :
          StageThree.Frozen M D hm
            (StageThree.activate B M hm (C.cfg x) i delta) := by
        simpa [StageThree.runActivations] using hs.2.2.1
      have hw :
          StageTwo.WellFormed M
            (StageThree.activate B M hm (C.cfg x) i delta) := by
        simpa [StageThree.runActivations] using hs.2.2.2
      rw [hc]
      exact ⟨hq, hf, hw⟩

private theorem source_run
    {α : Type} {n m B M D : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M) :
    ∀ (x : α), Src C D x → ∀ u : List (Fin n),
      Src C D (L4.Height.runWord C.next x u) := by
  intro x hx u
  induction u generalizing x with
  | nil =>
      simpa [L4.Height.runWord] using hx
  | cons e u ih =>
      have hn := source_next C hM x e hx
      simpa [L4.Height.runWord] using
        (ih (C.next x e) hn)

private theorem error_false_next
    {α : Type} {n m B M D : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (x : α) (e : Fin n) (hx : Src C D x)
    (j : Fin m) (hj : (C.cfg x j).err = false) :
    (C.cfg (C.next x e) j).err = false := by
  cases hact : C.act x e with
  | none =>
      have hc := C.cfg_next x e
      simp only [hact] at hc
      rw [hc]
      exact hj
  | some p =>
      rcases p with ⟨i, delta⟩
      have hc := C.cfg_next x e
      simp only [hact] at hc
      cases hpost : (C.cfg (C.next x e) j).err with
      | false =>
          rfl
      | true =>
          have hp :
              (StageThree.activate B M hm (C.cfg x) i delta j).err = true := by
            rw [← hc]
            exact hpost
          have hold := StageThree.error_monotone hm
            (C.cfg x) i delta hx.1 hx.2.1 j hp
          have hbad := hold.1
          rw [hj] at hbad
          cases hbad

private theorem error_false_run
    {α : Type} {n m B M D : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M) :
    ∀ (x : α), Src C D x → ∀ (u : List (Fin n)) (j : Fin m),
      (C.cfg x j).err = false →
      (C.cfg (L4.Height.runWord C.next x u) j).err = false := by
  intro x hx u
  induction u generalizing x with
  | nil =>
      intro j hj
      simpa [L4.Height.runWord] using hj
  | cons e u ih =>
      intro j hj
      have hn := source_next C hM x e hx
      have hj' := error_false_next C x e hx j hj
      simpa [L4.Height.runWord] using
        (ih (C.next x e) hn j hj')

private theorem error_true_info_next
    {α : Type} {n m B M D : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (x : α) (e : Fin n) (hx : Src C D x)
    (j : Fin m) (hpost : (C.cfg (C.next x e) j).err = true) :
    (C.cfg x j).err = true ∧
      StageThree.signedVal M (C.cfg (C.next x e) j) =
        StageThree.signedVal M (C.cfg x j) := by
  cases hact : C.act x e with
  | none =>
      have hc := C.cfg_next x e
      simp only [hact] at hc
      rw [hc] at hpost ⊢
      exact ⟨hpost, rfl⟩
  | some p =>
      rcases p with ⟨i, delta⟩
      have hc := C.cfg_next x e
      simp only [hact] at hc
      rw [hc] at hpost ⊢
      exact StageThree.error_monotone hm
        (C.cfg x) i delta hx.1 hx.2.1 j hpost

private theorem error_true_info_run
    {α : Type} {n m B M D : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M) :
    ∀ (x : α), Src C D x → ∀ (u : List (Fin n)) (j : Fin m),
      (C.cfg (L4.Height.runWord C.next x u) j).err = true →
      (C.cfg x j).err = true ∧
        StageThree.signedVal M
            (C.cfg (L4.Height.runWord C.next x u) j) =
          StageThree.signedVal M (C.cfg x j) := by
  intro x hx u
  induction u generalizing x with
  | nil =>
      intro j hpost
      change
        (C.cfg x j).err = true ∧
          StageThree.signedVal M (C.cfg x j) =
            StageThree.signedVal M (C.cfg x j)
      exact ⟨hpost, rfl⟩
  | cons e u ih =>
      intro j hpost
      have hn := source_next C hM x e hx
      have htail := ih (C.next x e) hn j (by
        simpa [L4.Height.runWord] using hpost)
      have hstep := error_true_info_next C x e hx j htail.1
      exact ⟨hstep.1, htail.2.trans hstep.2⟩

/-! ## Prefix states and monotonic correctness -/

private theorem take_add_cover {β : Type}
    (u : List β) (a b : Nat) :
    u.take (a + b) = u.take a ++ (u.drop a).take b := by
  induction a generalizing u with
  | zero => simp
  | succ a ih =>
      cases u with
      | nil => simp
      | cons e u =>
          simp only [Nat.succ_add, List.take_succ_cons,
            List.drop_succ_cons, List.cons_append]
          exact congrArg (List.cons e) (ih u)

private theorem drop_add_cover {β : Type}
    (u : List β) (a b : Nat) :
    u.drop (a + b) = (u.drop a).drop b := by
  induction a generalizing u with
  | zero => simp
  | succ a ih =>
      cases u with
      | nil => simp
      | cons e u =>
          simp only [Nat.succ_add, List.drop_succ_cons]
          exact ih u

private theorem thru_runWord_append_cover
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (x : α)
    (u v : Thru.Word n) :
    Thru.runWord next x (u ++ v) =
      Thru.runWord next (Thru.runWord next x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih =>
      simp only [List.cons_append, Thru.runWord]
      exact ih (next x e)

private theorem thru_runAt_add_cover
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (x : α)
    (u : Thru.Word n) (a b : Nat) :
    Thru.runWord next x (u.take (a + b)) =
      Thru.runWord next
        (Thru.runWord next x (u.take a))
        ((u.drop a).take b) := by
  rw [take_add_cover, thru_runWord_append_cover]

private theorem thru_run_eq_window
    {α : Type} {n : Nat}
    (next : α → Fin n → α) :
    ∀ (x : α) (u : List (Fin n)),
      Thru.runWord next x u = L4.Height.runWord next x u := by
  intro x u
  induction u generalizing x with
  | nil => rfl
  | cons e u ih =>
      simp only [Thru.runWord, L4.Height.runWord, List.foldl_cons]
      exact ih (next x e)

def stateAt
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (x : α) (u : List (Fin n)) (t : Nat) : Fin m → NativeRecord :=
  C.cfg (L4.Height.runWord C.next x (u.take t))

private theorem source_at
    {α : Type} {n m B M D : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M)
    (x : α) (hx : Src C D x) (u : List (Fin n)) (t : Nat) :
    Src C D (L4.Height.runWord C.next x (u.take t)) :=
  source_run C hM x hx (u.take t)

private theorem state_correct_mono
    {α : Type} {n m B M D : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M)
    (x : α) (hx : Src C D x) (u : List (Fin n))
    (j : Fin m) (t t' : Nat) (htt : t ≤ t')
    (_ht' : t' ≤ u.length)
    (hc : (stateAt C x u t j).err = false) :
    (stateAt C x u t' j).err = false := by
  let mid := (u.drop t).take (t' - t)
  have hadd : t + (t' - t) = t' := Nat.add_sub_of_le htt
  have htake := take_add_cover u t (t' - t)
  rw [hadd] at htake
  have hrun :
      L4.Height.runWord C.next x (u.take t') =
        L4.Height.runWord C.next
          (L4.Height.runWord C.next x (u.take t)) mid := by
    rw [htake, L4.Height.runWord_append]
  have hsrcT := source_at C hM x hx u t
  have hcorr := error_false_run C hM
    (L4.Height.runWord C.next x (u.take t)) hsrcT mid j hc
  unfold stateAt
  rw [hrun]
  exact hcorr

def ClearedBy
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (x : α) (u : List (Fin n)) (i : Fin m) (t : Nat) : Prop :=
  u.length ≤ t ∨ (stateAt C x u t i).err = false

private theorem cleared_mono
    {α : Type} {n m B M D : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M)
    (x : α) (hx : Src C D x) (u : List (Fin n))
    (i : Fin m) (t t' : Nat) (htt : t ≤ t')
    (hc : ClearedBy C x u i t) :
    ClearedBy C x u i t' := by
  unfold ClearedBy at hc ⊢
  rcases hc with hlate | hcorrect
  · exact Or.inl (Nat.le_trans hlate htt)
  · by_cases hlate' : u.length ≤ t'
    · exact Or.inl hlate'
    · have ht' : t' ≤ u.length := by omega
      exact Or.inr
        (state_correct_mono C hM x hx u i t t' htt ht' hcorrect)

/-! ## A strictly later service is an actual activation -/

private theorem wait_lt_length_hit_thru
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop) :
    ∀ (x : α) (u : Thru.Word n),
      Thru.wait next A x u < u.length →
      A (Thru.runWord next x
        (u.take (Thru.wait next A x u))) := by
  intro x u
  induction u generalizing x with
  | nil =>
      intro h
      simp [Thru.wait] at h
  | cons e u ih =>
      intro h
      by_cases hx : A x
      · have hw := Thru.wait_of_hit next A x hx (e :: u)
        simpa [hw, Thru.runWord] using hx
      · rw [Thru.wait_cons_of_not next A x hx e u] at h ⊢
        have ht : Thru.wait next A (next x e) u < u.length := by
          simp only [List.length_cons] at h
          omega
        have htail := ih (next x e) ht
        simpa [Thru.runWord] using htail

private theorem serviceTime_served
    {α : Type} {n m : Nat}
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (u : Thru.Word n)
    (i : Fin m) (t : Nat)
    (hS : L4.Height.serviceTime next x served u i t < u.length) :
    served i
      (Thru.runWord next x
        (u.take (L4.Height.serviceTime next x served u i t))) := by
  have heq := L4.Height.serviceTime_eq_requested
    next x served u i t
  let y := Thru.runWord next x (u.take (t + 1))
  let v := u.drop (t + 1)
  let w := Thru.wait next (served i) y v
  have hformula :
      L4.Height.serviceTime next x served u i t = t + 1 + w := by
    simpa [y, v, w] using heq
  have hw : w < v.length := by
    have hvlen : v.length = u.length - (t + 1) := by
      simp [v]
    rw [hformula] at hS
    omega
  have hhit := wait_lt_length_hit_thru next (served i) y v hw
  have hrun :
      Thru.runWord next x (u.take ((t + 1) + w)) =
        Thru.runWord next y (v.take w) := by
    simpa [y, v] using thru_runAt_add_cover next x u (t + 1) w
  rw [hformula]
  rw [hrun]
  exact hhit

private theorem act_of_served_next
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (x : α) (e : Fin n) (i : Fin m)
    (hs : C.served i (C.next x e)) :
    ∃ delta, C.act x e = some (i, delta) := by
  have hmapped : (C.act x e).map Prod.fst = some i := by
    rw [← C.last_next x e]
    exact hs
  cases hact : C.act x e with
  | none =>
      simp [hact] at hmapped
  | some p =>
      rcases p with ⟨j, delta⟩
      have hj : j = i := by
        simpa [hact] using hmapped
      subst j
      exact ⟨delta, rfl⟩

private theorem served_prefix_activation
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) :
    ∀ (q : Nat) (x : α) (u : List (Fin n)) (i : Fin m),
      0 < q → q ≤ u.length →
      C.served i
        (L4.Height.runWord C.next x (u.take q)) →
      ∃ delta,
        C.cfg (L4.Height.runWord C.next x (u.take q)) =
          StageThree.activate B M hm
            (C.cfg (L4.Height.runWord C.next x (u.take (q - 1))))
            i delta := by
  intro q
  induction q with
  | zero =>
      intro x u i hq
      omega
  | succ q ih =>
      intro x u i hq hlen hs
      cases u with
      | nil =>
          simp at hlen
      | cons e u =>
          cases q with
          | zero =>
              have hs' : C.served i (C.next x e) := by
                simpa [L4.Height.runWord] using hs
              obtain ⟨delta, hact⟩ := act_of_served_next C x e i hs'
              have hc := C.cfg_next x e
              simp only [hact] at hc
              refine ⟨delta, ?_⟩
              simpa [L4.Height.runWord] using hc
          | succ q =>
              have hlen' : Nat.succ q ≤ u.length := by
                simp only [List.length_cons] at hlen
                omega
              have hs' :
                  C.served i
                    (L4.Height.runWord C.next (C.next x e)
                      (u.take (Nat.succ q))) := by
                simpa [L4.Height.runWord] using hs
              obtain ⟨delta, hd⟩ :=
                ih (C.next x e) u i (by omega) hlen' hs'
              refine ⟨delta, ?_⟩
              simpa [L4.Height.runWord] using hd

private theorem serviceTime_activation
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (x : α) (u : List (Fin n)) (i : Fin m) (t : Nat)
    (hS : L4.Height.serviceTime C.next x C.served u i t < u.length) :
    ∃ delta,
      stateAt C x u (L4.Height.serviceTime C.next x C.served u i t) =
        StageThree.activate B M hm
          (stateAt C x u
            (L4.Height.serviceTime C.next x C.served u i t - 1))
          i delta := by
  let q := L4.Height.serviceTime C.next x C.served u i t
  have hsThru := serviceTime_served C.next x C.served u i t hS
  have hsWindow :
      C.served i
        (L4.Height.runWord C.next x (u.take q)) := by
    have heq := thru_run_eq_window C.next x (u.take q)
    rw [← heq]
    simpa [q] using hsThru
  have hpos : 0 < q := by
    have ha := L4.Height.serviceTime_after C.next x C.served u i t
    dsimp [q]
    omega
  have hle : q ≤ u.length := by
    dsimp [q]
    omega
  obtain ⟨delta, hd⟩ :=
    served_prefix_activation C q x u i hpos hle hsWindow
  refine ⟨delta, ?_⟩
  simpa [stateAt, q] using hd

/-! ## The finite-word clearing process -/

private theorem clear_process_word
    {α : Type} {n m B M D : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M)
    (x : α) (hx : Src C D x) (u : List (Fin n)) :
    StageThree.ClearProcess M hm (C.cfg x)
      (fun i t => L4.Height.serviceTime C.next x C.served u i t)
      (ClearedBy C x u) := by
  refine {
    service_after := ?_
    service_mono := ?_
    correct_mono := ?_
    poll := ?_
  }
  · intro i t
    exact L4.Height.serviceTime_after C.next x C.served u i t
  · intro i t t' htt
    exact L4.Height.serviceTime_mono C.next x C.served u i t t' htt
  · intro i t t' htt hc
    exact cleared_mono C hM x hx u i t t' htt hc
  · intro site t herr hdeps
    let q := L4.Height.serviceTime C.next x C.served u site t
    by_cases hlate : u.length ≤ q
    · exact Or.inl hlate
    · have hqLen : q < u.length := by omega
      have htq : t < q := by
        dsimp [q]
        exact L4.Height.serviceTime_after C.next x C.served u site t
      let pre := q - 1
      have htpre : t ≤ pre := by
        dsimp [pre]
        omega
      have hpreLen : pre ≤ u.length := by
        dsimp [pre]
        omega
      have hqLe : q ≤ u.length := by omega
      have hsrcPre := source_at C hM x hx u pre
      by_cases hsiteFalse : (stateAt C x u pre site).err = false
      · have hfinal := state_correct_mono C hM x hx u site
          pre q (by omega) hqLe hsiteFalse
        exact Or.inr hfinal
      · have hsiteTrue : (stateAt C x u pre site).err = true := by
          cases hv : (stateAt C x u pre site).err with
          | false => exact False.elim (hsiteFalse hv)
          | true => rfl
        obtain ⟨delta, hstep⟩ :=
          serviceTime_activation C x u site t (by simpa [q] using hqLen)
        have hdomain := clockDomain_of_wellFormed hM
          (stateAt C x u pre) hsrcPre.2.2
        have hhigher :
            ∀ v, StageThree.Neighbor hm site v →
              StageThree.signedVal M (stateAt C x u pre site) <
                StageThree.signedVal M (stateAt C x u pre v) →
              (stateAt C x u pre v).err = false := by
          intro v hneighbor hlt
          cases hv : (stateAt C x u pre v).err with
          | false => rfl
          | true =>
              have huInfo := error_true_info_run C hM x hx
                (u.take pre) site (by simpa [stateAt] using hsiteTrue)
              have hvInfo := error_true_info_run C hM x hx
                (u.take pre) v (by simpa [stateAt] using hv)
              have hlt0 :
                  StageThree.signedVal M (C.cfg x site) <
                    StageThree.signedVal M (C.cfg x v) := by
                rw [← huInfo.2, ← hvInfo.2]
                exact hlt
              have hedge :
                  StageThree.DepEdge M hm (C.cfg x) site v := by
                unfold StageThree.DepEdge
                exact ⟨hneighbor, herr, hvInfo.1, hlt0⟩
              have hct := hdeps v hedge
              have hvt : (stateAt C x u t v).err = false := by
                rcases hct with htooLate | hcorrect
                · omega
                · exact hcorrect
              have hvPre := state_correct_mono C hM x hx u v
                t pre htpre hpreLen hvt
              rw [hvPre] at hv
              cases hv
        have hclear := StageThree.clears_on_poll (B := B) hm
          (stateAt C x u pre) site delta hdomain
          hsrcPre.1 hsrcPre.2.1 hsiteTrue hhigher
        have hfinal : (stateAt C x u q site).err = false := by
          rw [hstep]
          simpa [pre] using hclear
        exact Or.inr hfinal

/-! ## Strict path times and the sharp `4^h` moment -/

def timeFold {m : Nat} (S : Fin m → Nat → Nat) :
    Nat → List (Fin m) → Nat
  | t, [] => t
  | t, i :: is => timeFold S (S i t) is

private theorem timeFold_append {m : Nat}
    (S : Fin m → Nat → Nat) :
    ∀ t xs ys,
      timeFold S t (xs ++ ys) =
        timeFold S (timeFold S t xs) ys := by
  intro t xs
  induction xs generalizing t with
  | nil => intro ys; rfl
  | cons i is ih =>
      intro ys
      simp only [List.cons_append, timeFold]
      exact ih (S i t) ys

private theorem clearSeq_eq_timeFold_reverse {m : Nat}
    (S : Fin m → Nat → Nat) :
    ∀ t path,
      StageThree.clearSeqTime S t path =
        timeFold S t path.reverse := by
  intro t path
  induction path generalizing t with
  | nil => rfl
  | cons i path ih =>
      simp only [StageThree.clearSeqTime, List.reverse_cons]
      rw [timeFold_append, ih]
      rfl

private theorem timeFold_service_cover
    {α : Type} {n m : Nat}
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (u : Thru.Word n) :
    ∀ sites t,
      timeFold (L4.Height.serviceTime next x served u) t sites =
        t + L4.Height.strictSeq next (sites.map served)
          (Thru.runWord next x (u.take t)) (u.drop t) := by
  intro sites
  induction sites with
  | nil =>
      intro t
      simp [timeFold, L4.Height.strictSeq]
  | cons i is ih =>
      intro t
      simp only [timeFold, List.map_cons]
      rw [ih]
      let y := Thru.runWord next x (u.take t)
      let v := u.drop t
      let d := L4.Height.strictDelay next (served i) y v
      have hS :
          L4.Height.serviceTime next x served u i t = t + d := by
        rfl
      rw [hS]
      have hr := thru_runAt_add_cover next x u t d
      have hd := drop_add_cover u t d
      rw [hr, hd]
      change
        (t + d) + L4.Height.strictSeq next (is.map served)
            (Thru.runWord next y (v.take d)) (v.drop d) =
          t + L4.Height.strictSeq next
            (served i :: is.map served) y v
      rw [L4.Height.strictSeq_cons_formula]
      simp only [d]
      omega

def pathQueries
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (path : List (Fin m)) :
    List (α → Prop) :=
  path.reverse.map C.served

noncomputable def pathWait
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (x : α)
    (path : List (Fin m)) (u : Thru.Word n) : Nat :=
  L4.Height.strictSeq C.next (pathQueries C path) x u

private theorem clearSeq_service_eq_pathWait
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (x : α) (u : Thru.Word n) (path : List (Fin m)) :
    StageThree.clearSeqTime
        (L4.Height.serviceTime C.next x C.served u) 0 path =
      pathWait C x path u := by
  rw [clearSeq_eq_timeFold_reverse]
  rw [timeFold_service_cover]
  simp [pathWait, pathQueries, Thru.runWord]

/-- Only the first query needs an unconditional scheduler step. Subsequent
queries use ordinary sequential waiting. -/
noncomputable def headSeq {α : Type} {n : Nat}
    (next : α → Fin n → α) :
    List (α → Prop) → α → Thru.Word n → Nat
  | [], _, _ => 0
  | _ :: _, _, [] => 0
  | A :: As, x, e :: u =>
      Nat.succ (Thru.seqWait next (A :: As) (next x e) u)

def QueryExclusive {α : Type} (A B : α → Prop) : Prop :=
  ∀ x, A x → ¬ B x

private theorem min_succ_succ_cover (a b : Nat) :
    Nat.min (Nat.succ a) (Nat.succ b) =
      Nat.succ (Nat.min a b) := by
  simpa only [Nat.succ_eq_add_one] using
    (Nat.add_min_add_right a b 1)

private theorem headSeq_eq_seqWait_of_head_not
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (As : List (α → Prop)) (x : α) (u : Thru.Word n)
    (hnot : ¬ A x) :
    headSeq next (A :: As) x u =
      Thru.seqWait next (A :: As) x u := by
  cases u with
  | nil =>
      simp [headSeq, Thru.seqWait_nil]
  | cons e u =>
      simp only [headSeq]
      rw [Thru.seqWait_cons_step next A As x hnot e u]
      simp only [Nat.one_add]

private theorem queryCompose_min_eq_seqWait
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (As : List (α → Prop))
    (tail : α → Thru.Word n → Nat)
    (hTail : ∀ y v, A y →
      Nat.min (tail y v) v.length =
        Thru.seqWait next As y v) :
    ∀ x u,
      Nat.min (L4.Height.queryCompose next A tail x u) u.length =
        Thru.seqWait next (A :: As) x u := by
  intro x u
  induction u generalizing x with
  | nil =>
      simp [L4.Height.queryCompose, Thru.seqWait_nil]
  | cons e u ih =>
      by_cases hx : A x
      · simp only [L4.Height.queryCompose, if_pos hx]
        rw [Thru.seqWait_cons_of_hit next A As x hx (e :: u)]
        exact hTail x (e :: u) hx
      · simp only [L4.Height.queryCompose, if_neg hx,
          List.length_cons, Nat.one_add]
        rw [min_succ_succ_cover]
        rw [Thru.seqWait_cons_step next A As x hx e u]
        simp only [Nat.one_add]
        exact congrArg Nat.succ (ih (next x e))

private theorem strictSeq_min_eq_headSeq
    {α : Type} {n : Nat}
    (next : α → Fin n → α) :
    ∀ (queries : List (α → Prop)),
      queries.Pairwise QueryExclusive →
      ∀ x u,
        Nat.min (L4.Height.strictSeq next queries x u) u.length =
          headSeq next queries x u := by
  intro queries
  induction queries with
  | nil =>
      intro _hpair x u
      simp [L4.Height.strictSeq, headSeq]
  | cons A As ih =>
      intro hpair x u
      have hp := List.pairwise_cons.mp hpair
      cases u with
      | nil =>
          simp [L4.Height.strictSeq, headSeq]
      | cons e u =>
          simp only [L4.Height.strictSeq, headSeq,
            List.length_cons, Nat.one_add]
          rw [min_succ_succ_cover]
          apply congrArg Nat.succ
          apply queryCompose_min_eq_seqWait
          intro y v hAy
          calc
            Nat.min (L4.Height.strictSeq next As y v) v.length =
                headSeq next As y v := ih hp.2 y v
            _ = Thru.seqWait next As y v := by
              cases As with
              | nil =>
                  have hzero : Thru.seqWait next [] y v = 0 := by
                    calc
                      Thru.seqWait next [] y v =
                          Thru.seqWait next [fun _ : α => True] y v :=
                        (Thru.seqWait_cons_of_hit next
                          (fun _ : α => True) [] y trivial v).symm
                      _ = Thru.wait next (fun _ : α => True) y v :=
                        Thru.seqWait_single next (fun _ : α => True) y v
                      _ = 0 := Thru.wait_of_hit next
                        (fun _ : α => True) y trivial v
                  simpa [headSeq] using hzero.symm
              | cons B Bs =>
                  exact headSeq_eq_seqWait_of_head_not
                    next B Bs y v (hp.1 B (by simp) y hAy)

private theorem served_exclusive
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    {i j : Fin m} (hij : i ≠ j) :
    QueryExclusive (C.served i) (C.served j) := by
  intro y hi hj
  unfold ClockChain.served at hi hj
  have he : (some i : Option (Fin m)) = some j := hi.symm.trans hj
  have hij' : i = j := by
    cases he
    rfl
  exact hij hij'

private theorem depPath_pairwise_signed {m M : Nat} (hm : 0 < m)
    (s : Fin m → NativeRecord) :
    ∀ path, StageThree.DepPath M hm s path →
      path.Pairwise (fun a b =>
        StageThree.signedVal M (s a) < StageThree.signedVal M (s b)) := by
  intro path
  cases path with
  | nil =>
      intro _hpath
      simp
  | cons u rest =>
      induction rest generalizing u with
      | nil =>
          intro _hpath
          simp
      | cons v rest ih =>
          intro hpath
          change
            StageThree.DepEdge M hm s u v ∧
              StageThree.DepPath M hm s (v :: rest) at hpath
          have htail := ih (u := v) hpath.2
          apply List.pairwise_cons.mpr
          constructor
          · intro w hw
            simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact hpath.1.2.2.2
            · have hp := List.pairwise_cons.mp htail
              have ha := hpath.1.2.2.2
              have hb := hp.1 w hw
              omega
          · exact htail

private theorem pathQueries_pairwise_exclusive
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (s : Fin m → NativeRecord) (path : List (Fin m))
    (hpath : StageThree.DepPath M hm s path) :
    (pathQueries C path).Pairwise QueryExclusive := by
  have hinc := depPath_pairwise_signed hm s path hpath
  have hrev :
      path.reverse.Pairwise (fun a b =>
        StageThree.signedVal M (s b) < StageThree.signedVal M (s a)) := by
    rw [List.pairwise_reverse]
    exact hinc
  have hne : path.reverse.Pairwise (fun a b => a ≠ b) := by
    apply hrev.imp
    intro a b hab
    intro heq
    subst b
    omega
  unfold pathQueries
  rw [List.pairwise_map]
  exact hne.imp (fun hab => served_exclusive C hab)

private theorem one_plus_exp_le_two (q L : Nat) (hL : 1 ≤ L) :
    2 ^ ((1 + q) / L) ≤ 2 * 2 ^ (q / L) := by
  by_cases hOne : L = 1
  · subst L
    simp only [Nat.div_one, Nat.add_comm 1 q, Nat.pow_succ]
    omega
  · have hsplit := Thru.div_add_le 1 q L hL
    have hlarge : 1 < L := by omega
    have hzero : 1 / L = 0 := Nat.div_eq_of_lt hlarge
    have hdiv : (1 + q) / L ≤ q / L + 1 := by
      simpa only [hzero, Nat.zero_add] using hsplit
    have hp := Nat.pow_le_pow_right
      (by omega : 0 < (2 : Nat)) hdiv
    calc
      2 ^ ((1 + q) / L) ≤ 2 ^ (q / L + 1) := hp
      _ = 2 * 2 ^ (q / L) := by
        rw [Nat.pow_succ]
        omega

private theorem seqWait_moment_sharp_raw
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (L : Nat) (hL : 1 ≤ L)
    (A : α → Prop) (As : List (α → Prop))
    (hMoment : ∀ Q, Q ∈ A :: As → ∀ y,
      Thru.MomentAt next Q L y) :
    ∀ x t,
      Thru.wordSum
          (fun u => 2 ^ (Thru.seqWait next (A :: As) x u / L)) t ≤
        2 * 4 ^ As.length * n ^ t := by
  induction As generalizing A with
  | nil =>
      intro x t
      have hfirst := Thru.momentAt_raw next A L x
        (hMoment A (by simp) x) t
      simpa [Thru.seqWait_single] using hfirst
  | cons B Bs ih =>
      intro x t
      have hMomentTail :
          ∀ Q, Q ∈ B :: Bs → ∀ y,
            Thru.MomentAt next Q L y := by
        intro Q hQ y
        exact hMoment Q (by simp [hQ]) y
      have hTail : ∀ y r,
          Thru.wordSum
              (fun u =>
                2 ^ (Thru.seqWait next (B :: Bs) y u / L)) r ≤
            (2 * 4 ^ Bs.length) * n ^ r :=
        ih (A := B) hMomentTail
      have hC : 1 ≤ 2 * 4 ^ Bs.length := by
        have hp : 0 < (4 : Nat) ^ Bs.length :=
          Nat.pow_pos (by decide)
        omega
      have hsplit := Thru.splitCost_sum_le next A (B :: Bs) L
        (2 * 4 ^ Bs.length) hTail hC 0 x t
      have hsplit' :
          Thru.wordSum (Thru.splitCost next A (B :: Bs) L 0 x) t ≤
            (2 * 4 ^ Bs.length) *
              Thru.wordSum
                (fun u => 2 ^ (Thru.wait next A x u / L)) t := by
        simpa using hsplit
      have hpoint : ∀ u,
          2 ^ (Thru.seqWait next (A :: B :: Bs) x u / L) ≤
            2 * Thru.splitCost next A (B :: Bs) L 0 x u := by
        intro u
        simpa using
          (Thru.seqExp_le_splitCost next A (B :: Bs) L hL 0 x u)
      have hpref :
          Thru.wordSum
              (fun u =>
                2 ^ (Thru.seqWait next (A :: B :: Bs) x u / L)) t ≤
            2 * Thru.wordSum
              (Thru.splitCost next A (B :: Bs) L 0 x) t := by
        calc
          Thru.wordSum
              (fun u =>
                2 ^ (Thru.seqWait next (A :: B :: Bs) x u / L)) t ≤
            Thru.wordSum
              (fun u =>
                2 * Thru.splitCost next A (B :: Bs) L 0 x u) t :=
              Thru.wordSum_mono _ _ hpoint t
          _ = 2 * Thru.wordSum
              (Thru.splitCost next A (B :: Bs) L 0 x) t :=
            Thru.wordSum_mul_left _ _ _
      have hfirst := Thru.momentAt_raw next A L x
        (hMoment A (by simp) x) t
      calc
        Thru.wordSum
            (fun u =>
              2 ^ (Thru.seqWait next (A :: B :: Bs) x u / L)) t ≤
          2 * Thru.wordSum
            (Thru.splitCost next A (B :: Bs) L 0 x) t := hpref
        _ ≤ 2 * ((2 * 4 ^ Bs.length) *
              Thru.wordSum
                (fun u => 2 ^ (Thru.wait next A x u / L)) t) :=
          Nat.mul_le_mul_left 2 hsplit'
        _ ≤ 2 * ((2 * 4 ^ Bs.length) * (2 * n ^ t)) :=
          Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_left (2 * 4 ^ Bs.length) hfirst)
        _ = 2 * 4 ^ (B :: Bs).length * n ^ t := by
          simp only [List.length_cons]
          have hFour : (2 : Nat) * 2 = 4 := by decide
          rw [Nat.pow_succ, ← hFour]
          ac_rfl

private theorem sum_ofFn_const_cover (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero =>
      simp [List.ofFn_zero]
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

private theorem headSeq_moment_raw
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (L : Nat) (hL : 1 ≤ L)
    (A : α → Prop) (As : List (α → Prop))
    (hMoment : ∀ Q, Q ∈ A :: As → ∀ y,
      Thru.MomentAt next Q L y) :
    ∀ x t,
      Thru.wordSum
          (fun u => 2 ^ (headSeq next (A :: As) x u / L)) t ≤
        4 ^ (A :: As).length * n ^ t := by
  intro x t
  cases t with
  | zero =>
      simp only [Thru.wordSum, headSeq, Nat.zero_div,
        Nat.pow_zero, Nat.mul_one]
      have hp : 0 < (4 : Nat) ^ (A :: As).length :=
        Nat.pow_pos (by decide)
      omega
  | succ t =>
      have hEach : ∀ e : Fin n,
          Thru.wordSum
              (fun v =>
                2 ^ (headSeq next (A :: As) x (e :: v) / L)) t ≤
            4 ^ (A :: As).length * n ^ t := by
        intro e
        have hpoint : ∀ v,
            2 ^ (headSeq next (A :: As) x (e :: v) / L) ≤
              2 * 2 ^
                (Thru.seqWait next (A :: As) (next x e) v / L) := by
          intro v
          simpa only [headSeq, Nat.one_add] using
            (one_plus_exp_le_two
              (Thru.seqWait next (A :: As) (next x e) v) L hL)
        have hsum := Thru.wordSum_mono
          (fun v =>
            2 ^ (headSeq next (A :: As) x (e :: v) / L))
          (fun v =>
            2 * 2 ^
              (Thru.seqWait next (A :: As) (next x e) v / L))
          hpoint t
        rw [Thru.wordSum_mul_left] at hsum
        have hseq := seqWait_moment_sharp_raw next L hL A As
          hMoment (next x e) t
        calc
          Thru.wordSum
              (fun v =>
                2 ^ (headSeq next (A :: As) x (e :: v) / L)) t ≤
            2 * Thru.wordSum
              (fun v =>
                2 ^
                  (Thru.seqWait next (A :: As) (next x e) v / L)) t := hsum
          _ ≤ 2 * (2 * 4 ^ As.length * n ^ t) :=
            Nat.mul_le_mul_left 2 hseq
          _ = 4 ^ (A :: As).length * n ^ t := by
            simp only [List.length_cons]
            have hFour : (2 : Nat) * 2 = 4 := by decide
            rw [Nat.pow_succ, ← hFour]
            ac_rfl
      simp only [Thru.wordSum]
      calc
        (List.ofFn (fun e : Fin n =>
          Thru.wordSum
              (fun v =>
                2 ^ (headSeq next (A :: As) x (e :: v) / L)) t)).sum ≤
          (List.ofFn (fun _ : Fin n =>
            4 ^ (A :: As).length * n ^ t)).sum := by
              apply Thru.ofFn_sum_le
              exact hEach
        _ = n * (4 ^ (A :: As).length * n ^ t) :=
          sum_ofFn_const_cover n _
        _ = 4 ^ (A :: As).length * n ^ Nat.succ t := by
          rw [Nat.pow_succ]
          ac_rfl

private theorem headSeq_moment_all_scales
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (L : Nat)
    (queries : List (α → Prop))
    (hMoment : ∀ Q, Q ∈ queries → ∀ y,
      Thru.MomentAt next Q L y)
    (x : α) (t : Nat) :
    Thru.wordSum
        (fun u => 2 ^ (Nat.min (headSeq next queries x u) t / L)) t ≤
      4 ^ queries.length * n ^ t := by
  cases queries with
  | nil =>
      simp [headSeq, Thru.wordSum_const_one]
  | cons A As =>
      by_cases hL : 1 ≤ L
      · have hraw := headSeq_moment_raw next L hL A As
          hMoment x t
        have hpoint : ∀ u,
            2 ^ (Nat.min (headSeq next (A :: As) x u) t / L) ≤
              2 ^ (headSeq next (A :: As) x u / L) := by
          intro u
          have hd :
              Nat.min (headSeq next (A :: As) x u) t / L ≤
                headSeq next (A :: As) x u / L :=
            Nat.div_le_div_right (c := L) (Nat.min_le_left _ _)
          exact Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) hd
        exact Nat.le_trans
          (Thru.wordSum_mono _ _ hpoint t) hraw
      · have hzero : L = 0 := by omega
        subst L
        simp only [Nat.div_zero, Nat.pow_zero]
        rw [Thru.wordSum_const_one]
        have hp : 1 ≤ 4 ^ (A :: As).length := by
          have hpos : 0 < (4 : Nat) ^ (A :: As).length :=
            Nat.pow_pos (by decide)
          omega
        simpa only [Nat.one_mul] using
          (Nat.mul_le_mul_right (n ^ t) hp)

/-! ## Exactly `3^h` padded path codes -/

def allCodes : Nat → List (List (Fin 3))
  | 0 => [[]]
  | h + 1 =>
      (allCodes h).map (fun ds => (0 : Fin 3) :: ds) ++
      ((allCodes h).map (fun ds => (1 : Fin 3) :: ds) ++
       (allCodes h).map (fun ds => (2 : Fin 3) :: ds))

private theorem allCodes_length (h : Nat) :
    (allCodes h).length = 3 ^ h := by
  induction h with
  | zero => rfl
  | succ h ih =>
      simp only [allCodes, List.length_append, List.length_map, ih]
      rw [Nat.pow_succ]
      omega

private theorem allCodes_complete :
    ∀ (h : Nat) (ds : List (Fin 3)),
      ds.length = h → ds ∈ allCodes h := by
  intro h
  induction h with
  | zero =>
      intro ds hd
      cases ds with
      | nil => simp [allCodes]
      | cons d ds =>
          simp only [List.length_cons] at hd
          omega
  | succ h ih =>
      intro ds hd
      cases ds with
      | nil => simp at hd
      | cons d ds =>
          have htail : ds.length = h := by
            simp only [List.length_cons] at hd
            omega
          have hmem := ih ds htail
          have hv : d.val = 0 ∨ d.val = 1 ∨ d.val = 2 := by
            omega
          rcases hv with hzero | hone | htwo
          · have he : d = (0 : Fin 3) := Fin.ext hzero
            subst d
            simp only [allCodes, List.mem_append]
            exact Or.inl (List.mem_map.mpr ⟨ds, hmem, rfl⟩)
          · have he : d = (1 : Fin 3) := Fin.ext hone
            subst d
            simp only [allCodes, List.mem_append]
            exact Or.inr (Or.inl
              (List.mem_map.mpr ⟨ds, hmem, rfl⟩))
          · have he : d = (2 : Fin 3) := Fin.ext htwo
            subst d
            simp only [allCodes, List.mem_append]
            exact Or.inr (Or.inr
              (List.mem_map.mpr ⟨ds, hmem, rfl⟩))

private theorem allCodes_member_length :
    ∀ (h : Nat) (ds : List (Fin 3)),
      ds ∈ allCodes h → ds.length = h := by
  intro h
  induction h with
  | zero =>
      intro ds hds
      simp [allCodes] at hds
      subst ds
      rfl
  | succ h ih =>
      intro ds hds
      simp only [allCodes, List.mem_append] at hds
      rcases hds with hleft | hrest
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hleft
        have ht := ih r hr
        simpa only [List.length_cons] using congrArg Nat.succ ht
      · rcases hrest with hmid | hright
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hmid
          have ht := ih r hr
          simpa only [List.length_cons] using congrArg Nat.succ ht
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hright
          have ht := ih r hr
          simpa only [List.length_cons] using congrArg Nat.succ ht

def candidatePath {m : Nat} (hm : 0 < m) :
    Fin m → List (Fin 3) → List (Fin m)
  | _, [] => []
  | i, d :: ds =>
      if d.val = 0 then [i]
      else if d.val = 1 then
        i :: candidatePath hm (left hm i) ds
      else
        i :: candidatePath hm (right hm i) ds

private theorem candidatePath_length_le {m : Nat} (hm : 0 < m) :
    ∀ (i : Fin m) (ds : List (Fin 3)),
      (candidatePath hm i ds).length ≤ ds.length := by
  intro i ds
  induction ds generalizing i with
  | nil =>
      exact Nat.le_refl 0
  | cons d ds ih =>
      simp only [candidatePath]
      split
      · simp
      · split
        · simpa only [List.length_cons] using
            Nat.succ_le_succ (ih (left hm i))
        · simpa only [List.length_cons] using
            Nat.succ_le_succ (ih (right hm i))

private theorem pathQueries_length
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (path : List (Fin m)) :
    (pathQueries C path).length = path.length := by
  unfold pathQueries
  simp only [List.length_map, List.length_reverse]

noncomputable def candidateWait
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (x : α)
    (i : Fin m) (ds : List (Fin 3)) : Thru.Word n → Nat :=
  fun u => headSeq C.next
    (pathQueries C (candidatePath hm i ds)) x u

noncomputable def clearFunctions
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (x : α) (h : Nat) :
    List (Thru.Word n → Nat) :=
  (List.finRange m).flatMap (fun i =>
    (allCodes h).map (candidateWait C x i))

private theorem flatMap_length_cover {β γ : Type}
    (xs : List β) (f : β → List γ) (r : Nat)
    (hf : ∀ y, y ∈ xs → (f y).length = r) :
    (xs.flatMap f).length = xs.length * r := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_cons]
      rw [hf y (by simp)]
      rw [ih (by
        intro z hz
        exact hf z (by simp [hz]))]
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

theorem clearFunctions_length
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (x : α) (h : Nat) :
    (clearFunctions C x h).length = m * 3 ^ h := by
  unfold clearFunctions
  rw [flatMap_length_cover _ _ (3 ^ h) (by
    intro i hi
    simp only [List.length_map, allCodes_length])]
  simp only [List.length_finRange]

private theorem candidate_moment
    {α : Type} {n m B M L : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (x : α)
    (hMom : ∀ i y, Thru.MomentAt C.next (C.served i) L y)
    (h t : Nat) (W : Thru.Word n → Nat)
    (hW : W ∈ clearFunctions C x h) :
    Thru.wordSum (fun u => 2 ^ (Nat.min (W u) t / L)) t ≤
      4 ^ h * n ^ t := by
  unfold clearFunctions at hW
  rw [List.mem_flatMap] at hW
  obtain ⟨i, hi, hWi⟩ := hW
  obtain ⟨ds, hds, rfl⟩ := List.mem_map.mp hWi
  have hdsLen : ds.length = h := allCodes_member_length h ds hds
  have hQueries :
      ∀ Q, Q ∈ pathQueries C (candidatePath hm i ds) → ∀ y,
        Thru.MomentAt C.next Q L y := by
    intro Q hQ y
    unfold pathQueries at hQ
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hQ
    exact hMom j y
  have hs := headSeq_moment_all_scales C.next L
    (pathQueries C (candidatePath hm i ds)) hQueries x t
  have hlenPath := candidatePath_length_le hm i ds
  have hlenQueries :
      (pathQueries C (candidatePath hm i ds)).length ≤ h := by
    rw [pathQueries_length]
    rw [hdsLen] at hlenPath
    exact hlenPath
  have hp :
      4 ^ (pathQueries C (candidatePath hm i ds)).length ≤ 4 ^ h :=
    Nat.pow_le_pow_right (by decide : 0 < (4 : Nat)) hlenQueries
  exact Nat.le_trans hs (Nat.mul_le_mul_right (n ^ t) hp)

private theorem le_maxWait_of_mem {n : Nat}
    (W : Thru.Word n → Nat) :
    ∀ Ws, W ∈ Ws → ∀ u, W u ≤ Thru.maxWait Ws u := by
  intro Ws hW u
  induction Ws with
  | nil => cases hW
  | cons V Vs ih =>
      simp only [List.mem_cons] at hW
      simp only [Thru.maxWait]
      rcases hW with rfl | htail
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

/-! ## Every static dependency path has a padded ternary code -/

private theorem dep_path_code {m M : Nat} (hm : 0 < m)
    (s : Fin m → NativeRecord) :
    ∀ (u : Fin m) (rest : List (Fin m)) (h : Nat),
      StageThree.DepPath M hm s (u :: rest) →
      (u :: rest).length ≤ h →
      ∃ ds : List (Fin 3),
        ds.length = h ∧ candidatePath hm u ds = u :: rest := by
  intro u rest
  induction rest generalizing u with
  | nil =>
      intro h _hpath hlen
      have hh : 1 ≤ h := by
        simp only [List.length_cons, List.length_nil] at hlen
        omega
      let tail := List.replicate (h - 1) (0 : Fin 3)
      refine ⟨(0 : Fin 3) :: tail, ?_, ?_⟩
      · simp only [List.length_cons, List.length_replicate, tail]
        omega
      · simp [candidatePath]
  | cons v rest ih =>
      intro h hpath hlen
      change
        StageThree.DepEdge M hm s u v ∧
          StageThree.DepPath M hm s (v :: rest) at hpath
      have hh : 1 ≤ h := by
        simp only [List.length_cons] at hlen
        omega
      have htailLen : (v :: rest).length ≤ h - 1 := by
        simp only [List.length_cons] at hlen ⊢
        omega
      obtain ⟨ds, hds, hdec⟩ :=
        ih (u := v) (h := h - 1) hpath.2 htailLen
      rcases hpath.1.1 with hv | hv
      · subst v
        refine ⟨(1 : Fin 3) :: ds, ?_, ?_⟩
        · simp only [List.length_cons, hds]
          omega
        · simpa [candidatePath] using congrArg (List.cons u) hdec
      · subst v
        refine ⟨(2 : Fin 3) :: ds, ?_, ?_⟩
        · simp only [List.length_cons, hds]
          omega
        · simpa [candidatePath] using congrArg (List.cons u) hdec

private theorem dep_path_from_code {m M : Nat} (hm : 0 < m)
    (s : Fin m → NativeRecord) (u : Fin m)
    (path : List (Fin m)) (h : Nat)
    (hpath : StageThree.DepPathFrom M hm s u path)
    (hlen : path.length ≤ h) :
    ∃ ds : List (Fin 3),
      ds.length = h ∧ ds ∈ allCodes h ∧
        candidatePath hm u ds = path := by
  rcases hpath with ⟨rest, rfl, hdep⟩
  obtain ⟨ds, hds, hdec⟩ :=
    dep_path_code hm s u rest h hdep hlen
  exact ⟨ds, hds, allCodes_complete h ds hds, hdec⟩

private theorem candidateWait_mem
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (x : α)
    (h : Nat) (i : Fin m) (ds : List (Fin 3))
    (hds : ds ∈ allCodes h) :
    candidateWait C x i ds ∈ clearFunctions C x h := by
  unfold clearFunctions
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_finRange i, ?_⟩
  exact List.mem_map.mpr ⟨ds, hds, rfl⟩

/-! ## Strict stage-three cover -/

/-- Dependency-path clearance as a strict stage cover with the requested
`m * 3^(D+1)` queries and `4^(D+1)` per-query moment constant. -/
theorem clear_cover
    {α : Type} {n m B M L D : Nat} (hm : 0 < m)
    (C : ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M)
    (_hD : D = m / 2)
    (hMom : ∀ i y, Thru.MomentAt C.next (C.served i) L y) :
    StageCoverStrict C.next (Src C D) (Tgt C)
      L (m * 3 ^ (D + 1)) (4 ^ (D + 1)) := by
  unfold StageCoverStrict
  intro x hx
  let Ws := clearFunctions C x (D + 1)
  refine ⟨Ws, ?_, ?_, ?_⟩
  · dsimp [Ws]
    exact clearFunctions_length C x (D + 1)
  · intro W hW t
    dsimp [Ws] at hW
    exact candidate_moment C x hMom (D + 1) t W hW
  · intro u k hmax hk
    have hproc := clear_process_word C hM x hx u
    have hsrcK := source_at C hM x hx u k
    change
      (∀ i, (stateAt C x u k i).err = false) ∧
        StageThree.Quiet M hm (stateAt C x u k)
    constructor
    · intro site
      by_cases herr : (C.cfg x site).err = true
      · obtain ⟨path, hpath, hplen, hcleared⟩ :=
          StageThree.clear_time hm (C.cfg x) hx.2.1
            (fun i t =>
              L4.Height.serviceTime C.next x C.served u i t)
            0 (ClearedBy C x u) hproc site herr
        obtain ⟨rest, hpathEq, hdep⟩ := hpath
        have hpathFrom :
            StageThree.DepPathFrom M hm (C.cfg x) site path :=
          ⟨rest, hpathEq, hdep⟩
        obtain ⟨ds, hdsLen, hdsMem, hdecode⟩ :=
          dep_path_from_code hm (C.cfg x) site path
            (D + 1) hpathFrom hplen
        let W := candidateWait C x site ds
        have hWmem : W ∈ Ws := by
          dsimp [Ws, W]
          exact candidateWait_mem C x (D + 1) site ds hdsMem
        have hWle := le_maxWait_of_mem W Ws hWmem u
        have hWuLe : W u ≤ k := Nat.le_trans hWle hmax
        have hWuLt : W u < u.length := Nat.lt_of_le_of_lt hWuLe hk
        have hpair := pathQueries_pairwise_exclusive C (C.cfg x) path hdep
        have hmin :
            Nat.min (pathWait C x path u) u.length = W u := by
          dsimp [pathWait, W, candidateWait]
          rw [hdecode]
          exact strictSeq_min_eq_headSeq C.next
            (pathQueries C path) hpair x u
        have hpathLt : pathWait C x path u < u.length := by
          by_cases hlt : pathWait C x path u < u.length
          · exact hlt
          · have hge : u.length ≤ pathWait C x path u := by omega
            have hm :
                Nat.min (pathWait C x path u) u.length = u.length :=
              Nat.min_eq_right hge
            have heq : u.length = W u := hm.symm.trans hmin
            omega
        have hpathEq : pathWait C x path u = W u := by
          have hle : pathWait C x path u ≤ u.length := Nat.le_of_lt hpathLt
          have hm :
              Nat.min (pathWait C x path u) u.length =
                pathWait C x path u := Nat.min_eq_left hle
          exact hm.symm.trans hmin
        have hqle :
            StageThree.clearSeqTime
                (L4.Height.serviceTime C.next x C.served u) 0 path ≤ k := by
          calc
            StageThree.clearSeqTime
                (L4.Height.serviceTime C.next x C.served u) 0 path =
              pathWait C x path u :=
                clearSeq_service_eq_pathWait C x u path
            _ = W u := hpathEq
            _ ≤ k := hWuLe
        rcases hcleared with hlate | hcorrect
        · exact False.elim
            ((Nat.not_le_of_gt hk) (Nat.le_trans hlate hqle))
        · exact state_correct_mono C hM x hx u site
            (StageThree.clearSeqTime
              (L4.Height.serviceTime C.next x C.served u) 0 path)
            k hqle (Nat.le_of_lt hk) hcorrect
      · have herrFalse : (C.cfg x site).err = false := by
          cases hv : (C.cfg x site).err with
          | false => rfl
          | true => exact False.elim (herr hv)
        have hc := error_false_run C hM x hx (u.take k) site herrFalse
        simpa [stateAt] using hc
    · exact hsrcK.1

/-- The requested native legitimacy follows immediately from the target. -/
theorem legitimate_of_target
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (x : α)
    (hx : Tgt C x) :
    StageThree.Legitimate M hm (C.cfg x) :=
  StageThree.legitimate_of_correct_quiet hm (C.cfg x) hx.1 hx.2

end

end L4.Height.Recover.CoverThree

