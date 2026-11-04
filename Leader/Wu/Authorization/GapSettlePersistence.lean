import Leader.Wu.Authorization.GapSettleVariants
import Leader.Wu.Authorization.GenerationDrain

/-!
# R7 persistence (P): replacement invariant and endpoint measure

Hidden premise of thesis Lemma 4.1.4 for the frozen R7 protocol
(`PPLLAuthPStarVariant.transition hψ 0 sVplusETL8 gapSettleDeferCleanWitness`),
part **P** (persistence).

The literal P ("some complete greatest-ID representative survives every
interaction") is false: the EpisodeCap example and the stale-CLEAN certificate
already refute it, and the complete small graphs refute it on every one of the
four stored graphs (see `run/verification/pstar/claude-pinv/`).  This file
states the replacement that survived the finite checks, in n-independent
pair/ring form:

* `RepAt` — a complete representative of a word `w` on `ψ` consecutive
  carriers (carriers may be separated by holes; one common provenance colour).
* **Payload ledger.**  Every main-path payload `(k, b)` written by an R7 row
  is either a payload already present on the served pair or the resident
  payload `(label, bit)` of the generating cell.  Lifted to the ring, the
  number of *garbage* carriers (payloads that no physical group can generate)
  never increases.  The ring lift is proved here for every `n`; the R7 pair
  obligation is stated as `PairGarbageLedgerStatement`; its two payload
  writers (GENSIG, Step1) are proved not to create garbage.
* **Endpoint return.**  Persistence is replaced by an endpoint statement:
  from every leaderless configuration reached after a representative of the
  maximal word existed, a finite word of interactions reaches either a fresh
  representative of that word or a leader.  `ReturnFromSeedsStatement` is the
  form the finite checks support (seed-reachable configurations);
  `ReturnStatement` (arbitrary configurations) is a stronger conjecture.

Unproved statements are `def ... : Prop` targets, never axioms.
-/

set_option autoImplicit false

namespace PPLLAuthPStarPInvariant

open PPLL PPLLRepair PPLLAuthF PPLLAuthSeam PPLLAuthPStarVariant

/-! ## The R7 protocol on unbounded cells -/

/-- An R7 cell: the authenticated state, its EpisodeCap counter and its latch. -/
abbrev Cell (ψ : Nat) := (AuthState ψ × Fin 3) × Nat

/-- The frozen R7 row on unbounded cells (κ = 0, `sVplusETL8`,
`gapSettleDeferCleanWitness`).  The bounded adapter `transition` used by the
stored graphs returns exactly this pair whenever reification succeeds. -/
def r7Row {ψ : Nat} (hψ : ψ > 0) (a b : Cell ψ) : Cell ψ × Cell ψ :=
  let r := stepA hψ 0 sVplusETL8 gapSettleDeferCleanWitness
    a.1.1 b.1.1 a.1.2 b.1.2 a.2 b.2
  (((r.1.1.1, r.1.2.1), r.2.1), ((r.1.1.2, r.1.2.2), r.2.2))

/-- R7 as a population protocol on the directed ring. -/
abbrev r7Protocol {ψ : Nat} (hψ : ψ > 0) : PopulationProtocol where
  Q := Cell ψ
  Y := Bool
  transition := r7Row hψ
  output := fun a => a.1.1.core.leader

/-- The authenticated state of a cell. -/
abbrev Cell.st {ψ : Nat} (a : Cell ψ) : AuthState ψ := a.1.1

/-! ## Generic locality on the ring (all `n`, any protocol) -/

/-- An interaction at edge `e` leaves every cell other than `e` and its right
neighbour unchanged. -/
theorem step_apply_of_ne (P : PopulationProtocol) {n : Nat} (ring : DirectedRing n)
    (C : P.Configuration n) (e k : Fin n) (hke : k ≠ e)
    (hkr : k ≠ ring.rightNeighbor e) :
    P.step ring C e k = C k := by
  simp only [PopulationProtocol.step, if_neg hke, if_neg hkr]

/-- The initiator cell after an interaction. -/
theorem step_apply_left (P : PopulationProtocol) {n : Nat} (ring : DirectedRing n)
    (C : P.Configuration n) (e : Fin n) :
    P.step ring C e e = (P.transition (C e) (C (ring.rightNeighbor e))).1 := by
  simp only [PopulationProtocol.step, if_pos rfl]

/-- The responder cell after an interaction (needs two distinct cells). -/
theorem step_apply_right (P : PopulationProtocol) {n : Nat} (ring : DirectedRing n)
    (hn : 1 < n) (C : P.Configuration n) (e : Fin n) :
    P.step ring C e (ring.rightNeighbor e) =
      (P.transition (C e) (C (ring.rightNeighbor e))).2 := by
  have hne : ring.rightNeighbor e ≠ e := PPLLAuthGenDrain.bneighbor_ne ring hn e
  simp [PopulationProtocol.step, hne]

/-- Pointwise-equal `Fin`-indexed lists have equal sums. -/
private theorem sum_ofFn_congr : ∀ {m : Nat} (f g : Fin m → Nat),
    (∀ i, f i = g i) → (List.ofFn f).sum = (List.ofFn g).sum := by
  intro m
  induction m with
  | zero => intros; simp
  | succ m ih =>
    intro f g h
    rw [List.ofFn_succ, List.ofFn_succ, List.sum_cons, List.sum_cons,
      h 0, ih (fun j => f j.succ) (fun j => g j.succ) (fun j => h j.succ)]

/-- Additive accounting for a change at one index (no subtraction).  Same
argument as `PPLLAuthHoleRouting.path_sum_swap_single`, restated here so this
file does not import the hole-routing development. -/
private theorem sum_swap_single : ∀ {m : Nat} (f g : Fin m → Nat) (i : Fin m),
    (∀ j, j ≠ i → f j = g j) →
      (List.ofFn f).sum + g i = (List.ofFn g).sum + f i := by
  intro m
  induction m with
  | zero => intro f g i _; exact Fin.elim0 i
  | succ m ih =>
    intro f g i h
    rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
    by_cases hi : i = 0
    · subst i
      have ht : (List.ofFn (fun j : Fin m => f j.succ)).sum =
          (List.ofFn (fun j : Fin m => g j.succ)).sum := by
        apply sum_ofFn_congr
        intro j
        apply h
        intro hz
        have hv := congrArg Fin.val hz
        simp at hv
      omega
    · have hip : 0 < i.val := by
        have hn : i.val ≠ 0 := fun hv => hi (Fin.ext hv)
        omega
      let j : Fin m := ⟨i.val - 1, by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have ht := ih (fun a : Fin m => f a.succ) (fun a : Fin m => g a.succ) j (by
        intro a ha
        apply h
        intro hz
        apply ha
        apply Fin.ext
        have hv := congrArg Fin.val hz
        have hv' := congrArg Fin.val hj
        simp at hv hv' ⊢
        omega)
      have h0 := h 0 (fun hz => hi hz.symm)
      simp only [hj] at ht
      omega

/-- Two-index accounting: a pair inequality and equality elsewhere give the
global sum inequality. -/
private theorem sum_pair_nonincrease {m : Nat} (f g : Fin m → Nat) (i j : Fin m)
    (hij : i ≠ j) (hrest : ∀ k, k ≠ i → k ≠ j → f k = g k)
    (hpair : g i + g j ≤ f i + f j) :
    (List.ofFn g).sum ≤ (List.ofFn f).sum := by
  let mid : Fin m → Nat := fun k => if k = i then g k else f k
  have hfirst := sum_swap_single f mid i (by
    intro k hk
    simp [mid, hk])
  have hsecond := sum_swap_single mid g j (by
    intro k hkj
    by_cases hki : k = i
    · simp [mid, hki]
    · simp [mid, hki, hrest k hki hkj])
  have hji : j ≠ i := Ne.symm hij
  simp only [mid, if_pos rfl, if_neg hji] at hfirst hsecond
  omega

/-- Ring sum of a per-cell weight. -/
def ringMass {Q : Type} {n : Nat} (f : Q → Nat) (C : Fin n → Q) : Nat :=
  (List.ofFn fun i : Fin n => f (C i)).sum

/-- **Ring lift of a pair ledger (all `n ≥ 2`, any protocol).**  If the served
pair's weight does not increase, the ring mass does not increase.  This is the
only place where the ring size enters; every R7-specific obligation below is a
statement about one served pair. -/
theorem ringMass_step_le_of_pair (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (hn : 1 < n) (f : P.Q → Nat)
    (C : P.Configuration n) (e : Fin n)
    (hpair : f (P.transition (C e) (C (ring.rightNeighbor e))).1 +
        f (P.transition (C e) (C (ring.rightNeighbor e))).2 ≤
      f (C e) + f (C (ring.rightNeighbor e))) :
    ringMass f (P.step ring C e) ≤ ringMass f C := by
  have hne : e ≠ ring.rightNeighbor e :=
    Ne.symm (PPLLAuthGenDrain.bneighbor_ne ring hn e)
  unfold ringMass
  apply sum_pair_nonincrease (fun k => f (C k))
    (fun k => f (P.step ring C e k)) e (ring.rightNeighbor e) hne
  · intro k hke hkr
    show f (C k) = f (P.step ring C e k)
    rw [step_apply_of_ne P ring C e k hke hkr]
  · show f (P.step ring C e e) + f (P.step ring C e (ring.rightNeighbor e)) ≤
      f (C e) + f (C (ring.rightNeighbor e))
    rw [step_apply_left, step_apply_right P ring hn]
    exact hpair

/-! ## The payload ledger (garbage never increases)

A *payload* is the `(label, bit)` pair carried by a main path.  Fix a Boolean
table `W` of admissible payloads.  A carrier is *garbage* for `W` when its
payload is not admissible.  The only R7 stages that write a main path are
Step1 (moves the left payload of the served pair to the right cell) and GENSIG
(emission and backward propagation write the generating cell's resident
payload `(label, bit)`); every other stage keeps a path or deletes it.  Hence,
whenever both served cells have admissible resident payloads, the garbage on
the served pair cannot grow.  With `W` = the resident payloads of the whole
ring this is the n-independent ledger behind the replacement invariant: a
garbage packet (a payload that no physical group can generate) is never
created; it can only be moved or erased. -/

/-- The resident payload of a cell: its physical label and resident bit. -/
def residentPayload {ψ : Nat} (u : AuthState ψ) : PathInfo :=
  .some u.core.label.val (if u.core.bit then 1 else 0)

/-- `u` carries a garbage payload for the admissible table `W`. -/
def garbage {ψ : Nat} (W : Nat → Nat → Bool) (u : AuthState ψ) : Nat :=
  match u.core.path with
  | .bot => 0
  | .some k b => if W k b then 0 else 1

/-- The resident payload of `u` is admissible for `W`. -/
def ResidentOK {ψ : Nat} (W : Nat → Nat → Bool) (u : AuthState ψ) : Prop :=
  W u.core.label.val (if u.core.bit then 1 else 0) = true

/-- **Pair obligation, unrestricted (FALSE).**  For every admissible table
containing the resident payloads of the two served cells, one frozen R7 row
does not increase the number of garbage carriers on the pair.  The graph check
(0 violations) covered only seed-reachable, perfectly labelled pairs.  As
stated it is refuted by a mislabelled pair
(`PPLLAuthPStarPFrames.not_pairGarbageLedgerStatement`: the probe wall relabels
the responder before GENSIG emits its new resident payload).  The adjacent-label
form `PPLLAuthPStarPFrames.PairGarbageLedgerAdjStatement` is proved there, stage
by stage. -/
def PairGarbageLedgerStatement {ψ : Nat} (hψ : ψ > 0) : Prop :=
  ∀ (W : Nat → Nat → Bool) (a b : Cell ψ),
    ResidentOK W a.st → ResidentOK W b.st →
    garbage W (r7Row hψ a b).1.st + garbage W (r7Row hψ a b).2.st ≤
      garbage W a.st + garbage W b.st

/-- **Pair provenance, unrestricted (FALSE).**  Every main path written by one
R7 row is absent, one of the two input paths, or the cell's own input resident
payload.  Checked on every edge of the four stored graphs (perfectly labelled
pairs only); refuted on the same mislabelled pair
(`PPLLAuthPStarPFrames.not_pairPayloadProvenanceStatement`). -/
def PairPayloadProvenanceStatement {ψ : Nat} (hψ : ψ > 0) : Prop :=
  ∀ a b : Cell ψ,
    (∀ x ∈ [((r7Row hψ a b).1.st, a.st), ((r7Row hψ a b).2.st, b.st)],
      x.1.core.path = .bot ∨ x.1.core.path = a.st.core.path ∨
        x.1.core.path = b.st.core.path ∨ x.1.core.path = residentPayload x.2)

/-- Ring garbage for the table `W`. -/
def ringGarbage {ψ n : Nat} (W : Nat → Nat → Bool) (C : Fin n → Cell ψ) : Nat :=
  ringMass (fun a : Cell ψ => garbage W a.st) C

/-- **Ring ledger, conditional form (every `n ≥ 2`).**  The hypothesis is the
unrestricted pair obligation, which is false; the unconditional version on
perfectly labelled rings is `PPLLAuthPStarPFrames.ringGarbage_step_le_adj`.  If
every cell's resident payload is admissible, one R7 interaction anywhere on the
ring does not increase the number of garbage carriers. -/
theorem ringGarbage_step_le {ψ n : Nat} (hψ : ψ > 0)
    (hpair : PairGarbageLedgerStatement hψ) (ring : DirectedRing n) (hn : 1 < n)
    (W : Nat → Nat → Bool) (C : Fin n → Cell ψ)
    (hres : ∀ i, ResidentOK W (C i).st) (e : Fin n) :
    ringGarbage W ((r7Protocol hψ).step ring C e) ≤ ringGarbage W C := by
  unfold ringGarbage
  exact ringMass_step_le_of_pair (r7Protocol hψ) ring hn
    (fun a : Cell ψ => garbage W a.st) C e
    (hpair W (C e) (C (ring.rightNeighbor e)) (hres e) (hres _))

/-! ## The two payload writers never create garbage

GENSIG and Step1 are the only R7 stages that write a main-path payload.  Both
are proved here for every `ψ` and every admissible table: GENSIG writes only
resident payloads (or deletes, or keeps), and Step1 moves a payload from the
left cell into an empty right cell.  The remaining obligation of
`PairGarbageLedgerStatement` is the keep-or-delete frame of the other stages. -/

/-- The output main path is the input path, absent, or the input cell's
resident payload. -/
def KeepDelRes {ψ : Nat} (out inp : AuthState ψ) : Prop :=
  out.core.path = inp.core.path ∨ out.core.path = .bot ∨
    out.core.path = residentPayload inp

theorem garbage_le_of_keepDelRes {ψ : Nat} (W : Nat → Nat → Bool)
    (out inp : AuthState ψ) (h : KeepDelRes out inp) (hres : ResidentOK W inp) :
    garbage W out ≤ garbage W inp := by
  unfold garbage
  rcases h with h | h | h
  · rw [h]; exact Nat.le_refl _
  · rw [h]; exact Nat.zero_le _
  · rw [h]
    unfold ResidentOK at hres
    unfold residentPayload
    dsimp only
    rw [if_pos hres]
    exact Nat.zero_le _

/-- Main path, physical label, resident bit and leader flag of a core. -/
def regs {ψ : Nat} (a : AgentState ψ) : PathInfo × Fin ψ × Bool × Bool :=
  (a.path, a.label, a.bit, a.leader)

private theorem prep_regs {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    regs (waitSaturatedPrepare hψ l r).1 = regs l ∧
    regs (waitSaturatedPrepare hψ l r).2 = regs r := by
  unfold waitSaturatedPrepare
  dsimp only
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

private theorem carry_regs {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    regs (waitSaturatedCarry hψ κ l r).1 = regs l ∧
    regs (waitSaturatedCarry hψ κ l r).2 = regs r := by
  unfold waitSaturatedCarry
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

private theorem reset_regs {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    regs (waitSaturatedReset hψ l r).1 = regs l ∧
    regs (waitSaturatedReset hψ l r).2 = regs r := by
  unfold waitSaturatedReset
  dsimp only
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

private theorem finish_regs {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    regs (waitSaturatedFinish hψ κ l r).1 = regs l ∧
    regs (waitSaturatedFinish hψ κ l r).2 = regs r := by
  unfold waitSaturatedFinish
  dsimp only
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

/-- WAIT (the first sub-stage of GENSIG) changes neither main paths, labels,
bits nor leader flags. -/
theorem waitSaturated_regs {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    regs (waitSaturated hψ κ l r).1 = regs l ∧
    regs (waitSaturated hψ κ l r).2 = regs r := by
  obtain ⟨a1, a2⟩ := prep_regs hψ l r
  obtain ⟨b1, b2⟩ := carry_regs hψ κ (waitSaturatedPrepare hψ l r).1
    (waitSaturatedPrepare hψ l r).2
  obtain ⟨c1, c2⟩ := reset_regs hψ
    (waitSaturatedCarry hψ κ (waitSaturatedPrepare hψ l r).1
      (waitSaturatedPrepare hψ l r).2).1
    (waitSaturatedCarry hψ κ (waitSaturatedPrepare hψ l r).1
      (waitSaturatedPrepare hψ l r).2).2
  obtain ⟨d1, d2⟩ := finish_regs hψ κ
    (waitSaturatedReset hψ
      (waitSaturatedCarry hψ κ (waitSaturatedPrepare hψ l r).1
        (waitSaturatedPrepare hψ l r).2).1
      (waitSaturatedCarry hψ κ (waitSaturatedPrepare hψ l r).1
        (waitSaturatedPrepare hψ l r).2).2).1
    (waitSaturatedReset hψ
      (waitSaturatedCarry hψ κ (waitSaturatedPrepare hψ l r).1
        (waitSaturatedPrepare hψ l r).2).1
      (waitSaturatedCarry hψ κ (waitSaturatedPrepare hψ l r).1
        (waitSaturatedPrepare hψ l r).2).2).2
  exact ⟨d1.trans (c1.trans (b1.trans a1)), d2.trans (c2.trans (b2.trans a2))⟩

/-- Tracking relation through the GENSIG sub-stages: the current path is the
input path, absent, or the input resident payload, and label and bit are the
input ones. -/
def Tr {ψ : Nat} (u l : AuthState ψ) : Prop :=
  KeepDelRes u l ∧ u.core.label = l.core.label ∧ u.core.bit = l.core.bit

private theorem tr_of_regs {ψ : Nat} (u l : AuthState ψ)
    (h : regs u.core = regs l.core) : Tr u l := by
  simp only [regs, Prod.mk.injEq] at h
  exact ⟨Or.inl h.1, h.2.1, h.2.2.1⟩

private theorem tr_keep {ψ : Nat} {u l : AuthState ψ} (h : Tr u l) (u' : AuthState ψ)
    (hp : u'.core.path = u.core.path) (hl : u'.core.label = u.core.label)
    (hb : u'.core.bit = u.core.bit) : Tr u' l := by
  refine ⟨?_, hl.trans h.2.1, hb.trans h.2.2⟩
  rcases h.1 with h1 | h1 | h1
  · exact Or.inl (hp.trans h1)
  · exact Or.inr (Or.inl (hp.trans h1))
  · exact Or.inr (Or.inr (hp.trans h1))

private theorem tr_bot {ψ : Nat} {u l : AuthState ψ} (h : Tr u l) (u' : AuthState ψ)
    (hp : u'.core.path = .bot) (hl : u'.core.label = u.core.label)
    (hb : u'.core.bit = u.core.bit) : Tr u' l :=
  ⟨Or.inr (Or.inl hp), hl.trans h.2.1, hb.trans h.2.2⟩

private theorem tr_res {ψ : Nat} {u l : AuthState ψ} (h : Tr u l) (u' : AuthState ψ)
    (hp : u'.core.path = .some u.core.label.val (if u.core.bit then 1 else 0))
    (hl : u'.core.label = u.core.label) (hb : u'.core.bit = u.core.bit) : Tr u' l := by
  refine ⟨Or.inr (Or.inr ?_), hl.trans h.2.1, hb.trans h.2.2⟩
  rw [hp, h.2.1, h.2.2]
  rfl

private theorem tr_ite {ψ : Nat} {a b l : AuthState ψ} (c : Prop) [Decidable c]
    (ha : Tr a l) (hb : Tr b l) : Tr (if c then a else b) l := by
  split
  · exact ha
  · exact hb

/-! GENSIG factored into its five sub-stages, copied verbatim from `PPLLAuthF.genSigAuth`;
`genSigAuth_tr` checks the factoring by a definitional `change`. -/

private def gsStart {ψ : Nat} (hψ : ψ > 0) (l r : AuthState ψ) : AuthState ψ :=
  if l.core.leader = false ∧ l.core.label = ⟨0, hψ⟩ ∧ l.core.wait = false ∧
      l.core.path = .bot then
    wipeProduceAuth (if l.st = .produce then l.ctrl_mark else fresh3 l.path_mark r.path_mark) l
  else l

private def gsRecruit {ψ : Nat} (hψ : ψ > 0) (l r : AuthState ψ) : AuthState ψ :=
  if r.core.label ≠ ⟨0, hψ⟩ ∧ l.st = .produce ∧
      (r.core.path = .bot ∨ (r.st ≠ .produce ∧ r.st ≠ .done) ∨ r.ctrl_mark ≠ l.ctrl_mark) then
    wipeProduceAuth l.ctrl_mark r
  else r

private def gsEmit {ψ : Nat} (hψ : ψ > 0) (r : AuthState ψ) : AuthState ψ :=
  if r.core.label = ⟨ψ - 1, by omega⟩ ∧ r.st = .produce then
    { r with core := { r.core with state := .done,
                                   path := .some r.core.label.val (if r.core.bit then 1 else 0) },
             path_mark := r.ctrl_mark }
  else r

private def gsBack {ψ : Nat} (hψ : ψ > 0) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  if l.core.label ≠ ⟨ψ - 1, by omega⟩ ∧ l.st = .produce ∧ r.st = .done then
    ({ l with core := { l.core with state := .done,
                                    path := .some l.core.label.val (if l.core.bit then 1 else 0) },
              path_mark := r.path_mark, ctrl_mark := r.path_mark },
     r.setState .depart)
  else (l, r)

private def gsHead {ψ : Nat} (hψ : ψ > 0) (l : AuthState ψ) : AuthState ψ :=
  if l.core.label = ⟨0, hψ⟩ ∧ l.st = .done then
    { l with core := { l.core with state := .depart, wait := true } }
  else l

private theorem tr_gsStart {ψ : Nat} (hψ : ψ > 0) {u L : AuthState ψ} (v : AuthState ψ)
    (h : Tr u L) : Tr (gsStart hψ u v) L := by
  unfold gsStart
  split
  · exact tr_bot h _ rfl rfl rfl
  · exact h

private theorem tr_gsRecruit {ψ : Nat} (hψ : ψ > 0) (u : AuthState ψ) {v R : AuthState ψ}
    (h : Tr v R) : Tr (gsRecruit hψ u v) R := by
  unfold gsRecruit
  split
  · exact tr_bot h _ rfl rfl rfl
  · exact h

private theorem tr_gsEmit {ψ : Nat} (hψ : ψ > 0) {v R : AuthState ψ}
    (h : Tr v R) : Tr (gsEmit hψ v) R := by
  unfold gsEmit
  split
  · exact tr_res h _ rfl rfl rfl
  · exact h

private theorem tr_gsBack {ψ : Nat} (hψ : ψ > 0) {u v L R : AuthState ψ}
    (hu : Tr u L) (hv : Tr v R) :
    Tr (gsBack hψ u v).1 L ∧ Tr (gsBack hψ u v).2 R := by
  unfold gsBack
  split
  · exact ⟨tr_res hu _ rfl rfl rfl, tr_keep hv _ rfl rfl rfl⟩
  · exact ⟨hu, hv⟩

private theorem tr_gsHead {ψ : Nat} (hψ : ψ > 0) {u L : AuthState ψ}
    (h : Tr u L) : Tr (gsHead hψ u) L := by
  unfold gsHead
  split
  · exact tr_keep h _ rfl rfl rfl
  · exact h

/-- **GENSIG writes only resident payloads.**  Each output main path of
`genSigAuth` is the cell's input path, absent (recruitment wipe), or the cell's
resident payload (terminal emission, backward propagation); labels and bits
are unchanged. -/
theorem genSigAuth_tr {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) :
    Tr (genSigAuth hψ κ l r).1 l ∧ Tr (genSigAuth hψ κ l r).2 r := by
  obtain ⟨hw1, hw2⟩ := waitSaturated_regs hψ κ l.core r.core
  have t1 : Tr (lift2 (waitSaturated hψ κ) l r).1 l := tr_of_regs _ _ hw1
  have t2 : Tr (lift2 (waitSaturated hψ κ) l r).2 r := tr_of_regs _ _ hw2
  unfold genSigAuth
  generalize lift2 (waitSaturated hψ κ) l r = q at t1 t2 ⊢
  obtain ⟨a, b⟩ := q
  have s1 : Tr (gsStart hψ a b) l := tr_gsStart hψ b t1
  have s3 := tr_gsEmit hψ (tr_gsRecruit hψ (gsStart hψ a b) t2)
  have s4 := tr_gsBack hψ s1 s3
  change Tr (match gsBack hψ (gsStart hψ a b) (gsEmit hψ (gsRecruit hψ (gsStart hψ a b) b)) with
      | (x, y) => (gsHead hψ x, y)).1 l ∧
    Tr (match gsBack hψ (gsStart hψ a b) (gsEmit hψ (gsRecruit hψ (gsStart hψ a b) b)) with
      | (x, y) => (gsHead hψ x, y)).2 r
  generalize gsBack hψ (gsStart hψ a b) (gsEmit hψ (gsRecruit hψ (gsStart hψ a b) b)) = p at s4 ⊢
  obtain ⟨x, y⟩ := p
  exact ⟨tr_gsHead hψ s4.1, s4.2⟩

/-- GENSIG does not increase garbage on the served pair. -/
theorem genSigAuth_garbage_le {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (W : Nat → Nat → Bool)
    (l r : AuthState ψ) (hl : ResidentOK W l) (hr : ResidentOK W r) :
    garbage W (genSigAuth hψ κ l r).1 + garbage W (genSigAuth hψ κ l r).2 ≤
      garbage W l + garbage W r := by
  obtain ⟨hl', hr'⟩ := genSigAuth_tr hψ κ l r
  have a := garbage_le_of_keepDelRes W _ _ hl'.1 hl
  have b := garbage_le_of_keepDelRes W _ _ hr'.1 hr
  omega

/-- **Step1 moves a payload without copying it.**  Garbage on the pair is
conserved exactly. -/
theorem step1Auth_garbage {ψ : Nat} (W : Nat → Nat → Bool) (l r : AuthState ψ) :
    garbage W (step1Auth l r).1 + garbage W (step1Auth l r).2 =
      garbage W l + garbage W r := by
  unfold step1Auth
  split
  · rename_i k b hl hr
    dsimp only
    split
    · split
      · simp [garbage, hl, hr]
      · rfl
    · rfl
  · rfl

/-! ## Complete representatives

Carriers are cells with a main path.  A complete representative of a word
`w : Fin ψ → Bool` is a list of `ψ` carriers `pos 0, …, pos (ψ-1)` such that
`pos (k+1)` is the next carrier after `pos k` in ring order (holes allowed in
between), `pos k` carries payload `(k, w k)`, and all carry one provenance
colour.  This is the gap form; the literal adjacent
form is the special case with no holes. -/

/-- Cell `i` advanced `d` steps to the right. -/
def adv {n : Nat} (ring : DirectedRing n) (i : Fin n) (d : Nat) : Fin n :=
  ⟨(i.val + d) % n, Nat.mod_lt _ ring.hn⟩

/-- `j` is the next carrier strictly after carrier `i`, at distance `d ≥ 1`. -/
def NextCarrier {ψ n : Nat} (ring : DirectedRing n) (C : Fin n → Cell ψ)
    (i j : Fin n) : Prop :=
  ∃ d, 0 < d ∧ d ≤ n ∧ j = adv ring i d ∧ (C j).st.core.path ≠ .bot ∧
    ∀ t, 0 < t → t < d → (C (adv ring i t)).st.core.path = .bot

/-- A complete representative of `w` with colour `γ` at positions `pos`. -/
def RepAt {ψ n : Nat} (ring : DirectedRing n) (C : Fin n → Cell ψ)
    (w : Fin ψ → Bool) (γ : ProvColor) (pos : Fin ψ → Fin n) : Prop :=
  (∀ k : Fin ψ, (C (pos k)).st.core.path = .some k.val (if w k then 1 else 0) ∧
    (C (pos k)).st.path_mark = γ) ∧
  (∀ k : Fin ψ, ∀ h : k.val + 1 < ψ, NextCarrier ring C (pos k) (pos ⟨k.val + 1, h⟩))

/-- Some complete representative of `w` exists. -/
def HasRep {ψ n : Nat} (ring : DirectedRing n) (C : Fin n → Cell ψ)
    (w : Fin ψ → Bool) : Prop :=
  ∃ γ pos, RepAt ring C w γ pos

/-- Value of a word, label 0 most significant (as `StaleCleanP1.physicalGroupID`). -/
def wordVal {ψ : Nat} (w : Fin ψ → Bool) : Nat :=
  (List.ofFn fun k : Fin ψ => if w k then 2 ^ (ψ - 1 - k.val) else 0).sum

/-- The resident word of the physical group whose head is cell `h`. -/
def groupWord {ψ n : Nat} (ring : DirectedRing n) (C : Fin n → Cell ψ)
    (h : Fin n) : Fin ψ → Bool :=
  fun k => (C (adv ring h k.val)).st.core.bit

/-- `w` is the greatest physical-group ID (heads are the label-0 cells). -/
def MaxWord {ψ n : Nat} (ring : DirectedRing n) (C : Fin n → Cell ψ)
    (w : Fin ψ → Bool) : Prop :=
  (∃ h, (C h).st.core.label.val = 0 ∧ groupWord ring C h = w) ∧
  ∀ h, (C h).st.core.label.val = 0 → wordVal (groupWord ring C h) ≤ wordVal w

/-- No cell carries a leader. -/
def Leaderless {ψ n : Nat} (C : Fin n → Cell ψ) : Prop :=
  ∀ i, (C i).st.core.leader = false

/-- Run a finite word of interactions. -/
def run {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n) :
    (Fin n → Cell ψ) → List (Fin n) → (Fin n → Cell ψ)
  | C, [] => C
  | C, e :: es => run hψ ring ((r7Protocol hψ).step ring C e) es

/-! ## The literal persistence statement and its replacement -/

/-- **Literal P (false).**  A complete representative of the greatest word
survives every leaderless interaction.  Refuted on all four stored graphs:
the minimal witnesses are an ELIM wave (ψ = n = 2, depth 2) and EpisodeCap
(ψ = n = 3); see `run/verification/pstar/claude-pinv/results/`. -/
def LiteralPersistenceStatement {ψ : Nat} (hψ : ψ > 0) : Prop :=
  ∀ (n : Nat) (ring : DirectedRing n) (C : Fin n → Cell ψ) (w : Fin ψ → Bool) (e : Fin n),
    MaxWord ring C w → HasRep ring C w → Leaderless ((r7Protocol hψ).step ring C e) →
    HasRep ring ((r7Protocol hψ).step ring C e) w

/-- **Replacement P (endpoint form), unrestricted.**  Once a complete
representative of the greatest word `w` exists, every configuration reachable
from it without a leader can reach, by a finite word, a configuration with a
leader or with a complete representative of `w` again (a regenerated one may
carry a new colour).

**Domain audit.**  This quantifies over an *arbitrary* `C₀`.  No finite check
covers that domain: the stored graphs contain only configurations reachable
from the 72 "heads" seeds (below), and arbitrary configurations include
mislabelled rings, on which even the pair garbage ledger fails
(`PPLLAuthPStarPFrames.not_pairGarbageLedgerStatement`).  This statement is a
conjecture strictly stronger than the evidence; the evidence-backed target is
`ReturnFromSeedsStatement`. -/
def ReturnStatement {ψ : Nat} (hψ : ψ > 0) : Prop :=
  ∀ (n : Nat) (ring : DirectedRing n) (C₀ : Fin n → Cell ψ) (w : Fin ψ → Bool)
    (es : List (Fin n)),
    2 ≤ ψ → ψ ∣ n → MaxWord ring C₀ w → HasRep ring C₀ w →
    (∀ k ≤ es.length, Leaderless (run hψ ring C₀ (es.take k))) →
    ∃ fs : List (Fin n),
      (¬ Leaderless (run hψ ring (run hψ ring C₀ es) fs)) ∨
      HasRep ring (run hψ ring (run hψ ring C₀ es) fs) w

/-- `C` is reached from a configuration satisfying `Seed` by a word all of
whose prefixes are leaderless (the ZERO exploration discipline; the FULL graphs
contain these configurations and more). -/
def SeedReach {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (Seed : (Fin n → Cell ψ) → Prop) (C : Fin n → Cell ψ) : Prop :=
  ∃ (Cs : Fin n → Cell ψ) (es0 : List (Fin n)), Seed Cs ∧ C = run hψ ring Cs es0 ∧
    ∀ k ≤ es0.length, Leaderless (run hψ ring Cs (es0.take k))

/-- **Replacement P restricted to seed-reachable configurations.**

Evidence (exhaustive, on every stored node and edge): `Seed n` = the 72
"heads" seeds of the frozen V10 runner (`ZZPStarCorridorCompactV10.starts ψ n
_ "heads"`, i.e. `headSeed` over head state ∈ {larger, less, equal}, resident
and carried head bits, colour ∈ {0, 1}, three hole modes; perfectly labelled,
leaderless, κ = 0, zero EpisodeCap counters and latches) at (ψ, n) = (2, 2),
(3, 3), (4, 4) (FULL graphs) and (2, 4) (ZERO graph).  On those instances every
seed-reachable Rep state's leaderless forward closure returns to Rep or a
leader within 2, 5, 9 and 11 steps respectively.  Nothing is checked for other
`n`, other seed families or κ ≠ 0; the seeds contain garbage carriers (carried
bit ≠ resident bit), so no `garbage = 0` premise is used or needed.  The seed
predicate is left as a parameter because the seed generator lives in a runner
module. -/
def ReturnFromSeedsStatement {ψ : Nat} (hψ : ψ > 0)
    (Seed : (n : Nat) → (Fin n → Cell ψ) → Prop) : Prop :=
  ∀ (n : Nat) (ring : DirectedRing n) (C₀ : Fin n → Cell ψ) (w : Fin ψ → Bool)
    (es : List (Fin n)),
    2 ≤ ψ → ψ ∣ n → SeedReach hψ ring (Seed n) C₀ →
    MaxWord ring C₀ w → HasRep ring C₀ w →
    (∀ k ≤ es.length, Leaderless (run hψ ring C₀ (es.take k))) →
    ∃ fs : List (Fin n),
      (¬ Leaderless (run hψ ring (run hψ ring C₀ es) fs)) ∨
      HasRep ring (run hψ ring (run hψ ring C₀ es) fs) w

end PPLLAuthPStarPInvariant

#print axioms PPLLAuthPStarPInvariant.step_apply_of_ne
#print axioms PPLLAuthPStarPInvariant.ringMass_step_le_of_pair
#print axioms PPLLAuthPStarPInvariant.ringGarbage_step_le
#print axioms PPLLAuthPStarPInvariant.genSigAuth_garbage_le
#print axioms PPLLAuthPStarPInvariant.step1Auth_garbage
