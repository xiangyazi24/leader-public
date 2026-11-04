import Leader.Wu.Birth.ShortDoneTerminalPassiveLocalTripleMass
import Init.Data.List.OfFn
import Init.Data.List.Perm

namespace BirthShortDoneTerminalPassiveLocal3Rotation

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWait BirthShortWaitProjection
open BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Count BirthShortDoneTerminalPassiveLocal3Producer
open BirthShortDoneTerminalPassiveLocal3Mass
open FiniteUniformStoppingTree ControlledSchedulerMass

set_option autoImplicit false
set_option pp.structureInstances false
set_option Elab.async false

variable {psi kappa tau n : Nat}

/-! ## Literal cyclic coordinate change -/

/-- Physical position of canonical index `i` when canonical zero is placed at
`anchor`.  This is the literal additive rotation of `Fin n`. -/
def rotateIndex (ring : DirectedRing n) (anchor i : Fin n) : Fin n :=
  ⟨(anchor.val + i.val) % n, Nat.mod_lt _ ring.hn⟩

/-- Inverse physical-to-canonical coordinate. -/
def unrotateIndex (ring : DirectedRing n) (anchor i : Fin n) : Fin n :=
  ⟨(n - anchor.val + i.val) % n, Nat.mod_lt _ ring.hn⟩

@[simp] theorem rotateIndex_unrotateIndex
    (ring : DirectedRing n) (anchor i : Fin n) :
    rotateIndex ring anchor (unrotateIndex ring anchor i) = i := by
  apply Fin.ext
  change
    (anchor.val + ((n - anchor.val + i.val) % n)) % n = i.val
  calc
    (anchor.val + ((n - anchor.val + i.val) % n)) % n =
        ((anchor.val % n) + ((n - anchor.val + i.val) % n)) % n := by
      rw [Nat.mod_eq_of_lt anchor.isLt]
    _ = (anchor.val + (n - anchor.val + i.val)) % n :=
      (Nat.add_mod _ _ _).symm
    _ = (n + i.val) % n := by
      apply congrArg (fun x : Nat => x % n)
      omega
    _ = i.val := by
      simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt i.isLt]

@[simp] theorem unrotateIndex_rotateIndex
    (ring : DirectedRing n) (anchor i : Fin n) :
    unrotateIndex ring anchor (rotateIndex ring anchor i) = i := by
  apply Fin.ext
  change
    (n - anchor.val + ((anchor.val + i.val) % n)) % n = i.val
  calc
    (n - anchor.val + ((anchor.val + i.val) % n)) % n =
        (((n - anchor.val) % n) +
          (((anchor.val + i.val) % n) % n)) % n :=
      Nat.add_mod _ _ _
    _ = (((n - anchor.val) % n) +
          ((anchor.val + i.val) % n)) % n := by
      rw [Nat.mod_mod]
    _ = ((n - anchor.val) + (anchor.val + i.val)) % n :=
      (Nat.add_mod _ _ _).symm
    _ = (n + i.val) % n := by
      apply congrArg (fun x : Nat => x % n)
      omega
    _ = i.val := by
      simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt i.isLt]

/-- Inverse rotation supplies injectivity without a library equivalence wrapper. -/
theorem rotateIndex_injective (ring : DirectedRing n) (anchor : Fin n) :
    Function.Injective (rotateIndex ring anchor) := by
  intro i j h
  have hi := congrArg (unrotateIndex ring anchor) h
  simpa only [unrotateIndex_rotateIndex] using hi

/-- Literal compatibility with the repository's actual
`DirectedRing.rightNeighbor = (i+1) % n`. -/
theorem rotateIndex_rightNeighbor (hn : 2 <= n)
    (ring : DirectedRing n) (anchor i : Fin n) :
    rotateIndex ring anchor (ring.rightNeighbor i) =
      ring.rightNeighbor (rotateIndex ring anchor i) := by
  apply Fin.ext
  change
    (anchor.val + ((i.val + 1) % n)) % n =
      (((anchor.val + i.val) % n) + 1) % n
  calc
    (anchor.val + ((i.val + 1) % n)) % n =
        ((anchor.val % n) + ((i.val + 1) % n)) % n := by
      rw [Nat.mod_eq_of_lt anchor.isLt]
    _ = (anchor.val + (i.val + 1)) % n :=
      (Nat.add_mod _ _ _).symm
    _ = ((anchor.val + i.val) + 1) % n := by
      apply congrArg (fun x : Nat => x % n)
      omega
    _ = (((anchor.val + i.val) % n) + (1 % n)) % n :=
      Nat.add_mod _ _ _
    _ = (((anchor.val + i.val) % n) + 1) % n := by
      rw [Nat.mod_eq_of_lt (by omega : 1 < n)]

@[simp] theorem rotateIndex_p0 (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n) :
    rotateIndex ring anchor (p0 hn) = anchor := by
  apply Fin.ext
  change (anchor.val + 0) % n = anchor.val
  rw [Nat.add_zero, Nat.mod_eq_of_lt anchor.isLt]

@[simp] theorem rotateIndex_p1 (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n) :
    rotateIndex ring anchor (p1 hn) = ring.rightNeighbor anchor := by
  rw [← right_p0 hn ring,
    rotateIndex_rightNeighbor (by omega : 2 <= n) ring anchor (p0 hn),
    rotateIndex_p0 hn ring anchor]

@[simp] theorem rotateIndex_p2 (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n) :
    rotateIndex ring anchor (p2 hn) =
      ring.rightNeighbor (ring.rightNeighbor anchor) := by
  rw [← right_p1 hn ring,
    rotateIndex_rightNeighbor (by omega : 2 <= n) ring anchor (p1 hn),
    rotateIndex_p1 hn ring anchor]

/-- The rotated copy of the fixed `leftCross` is exactly an incoming edge of
`anchor`; this states the wrap boundary without introducing a predecessor API. -/
theorem right_rotateIndex_leftCross (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n) :
    ring.rightNeighbor (rotateIndex ring anchor (leftCross hn)) = anchor := by
  rw [← rotateIndex_rightNeighbor (by omega : 2 <= n)
      ring anchor (leftCross hn),
    right_leftCross hn ring, rotateIndex_p0 hn ring anchor]

/-! ## Configurations, words, and the actual local step -/

/-- Pull a physical configuration back to coordinates whose zero is `anchor`. -/
def rotateConfig {Q : Type} (ring : DirectedRing n) (anchor : Fin n)
    (C : Fin n -> Q) : Fin n -> Q :=
  fun i => C (rotateIndex ring anchor i)

/-- Send a canonical scheduler word to its physical location. -/
def rotateWord (ring : DirectedRing n) (anchor : Fin n)
    (word : List (Fin n)) : List (Fin n) :=
  word.map (rotateIndex ring anchor)

/-- Pull an original physical scheduler word back to canonical letters. -/
def unrotateWord (ring : DirectedRing n) (anchor : Fin n)
    (word : List (Fin n)) : List (Fin n) :=
  word.map (unrotateIndex ring anchor)

@[simp] theorem rotateWord_unrotateWord
    (ring : DirectedRing n) (anchor : Fin n) (word : List (Fin n)) :
    rotateWord ring anchor (unrotateWord ring anchor word) = word := by
  induction word with
  | nil => rfl
  | cons e rest ih =>
      simp only [rotateWord, unrotateWord, List.map_cons, rotateIndex_unrotateIndex, unrotateIndex_rotateIndex] at ih ⊢
      exact congrArg (List.cons e) ih

@[simp] theorem unrotateWord_rotateWord
    (ring : DirectedRing n) (anchor : Fin n) (word : List (Fin n)) :
    unrotateWord ring anchor (rotateWord ring anchor word) = word := by
  induction word with
  | nil => rfl
  | cons e rest ih =>
      simp only [rotateWord, unrotateWord, List.map_cons, rotateIndex_unrotateIndex, unrotateIndex_rotateIndex] at ih ⊢
      exact congrArg (List.cons e) ih

/-- Rotation equivariance of the repository's literal `localStep`.  The local
transition `T` is arbitrary; only the actual ring addressing is used. -/
theorem localStep_rotateConfig {Q : Type}
    (hn : 2 <= n) (ring : DirectedRing n) (T : Q -> Q -> Q × Q)
    (anchor : Fin n) (C : Fin n -> Q) (e : Fin n) :
    localStep ring T (rotateConfig ring anchor C) e =
      rotateConfig ring anchor
        (localStep ring T C (rotateIndex ring anchor e)) := by
  funext i
  unfold PPLLResearchFormulation.localStep rotateConfig
  dsimp only
  rw [← rotateIndex_rightNeighbor hn ring anchor e]
  have hinj : Function.Injective (rotateIndex ring anchor) :=
    rotateIndex_injective ring anchor
  by_cases hie : i = e
  · subst i
    simp
  · have hri :
        rotateIndex ring anchor i ≠ rotateIndex ring anchor e := by
      intro h
      exact hie (hinj h)
    by_cases hij : i = ring.rightNeighbor e
    · have hrj :
          rotateIndex ring anchor i =
            rotateIndex ring anchor (ring.rightNeighbor e) :=
        congrArg (rotateIndex ring anchor) hij
      have hne : ring.rightNeighbor e ≠ e := by simpa only [hij] using hie
      have hrne : rotateIndex ring anchor (ring.rightNeighbor e) ≠ rotateIndex ring anchor e := by simpa only [hij] using hri
      simp [hij, hne, hrne]
    · have hrj :
          rotateIndex ring anchor i ≠
            rotateIndex ring anchor (ring.rightNeighbor e) := by
        intro h
        exact hij (hinj h)
      simp [hie, hij, hri, hrj]

/-- Rotation equivariance of the **actual full** Local3 host step.  This is an
instantiation of the generic local-step lemma with the literal
`BirthShortDoneTerminalHost.row`; no host stage is replaced or projected. -/
theorem hostStep_rotateConfig
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n) :
    hostStep hpsi h2 ring (rotateConfig ring anchor C) e =
      rotateConfig ring anchor
        (hostStep hpsi h2 ring C (rotateIndex ring anchor e)) := by
  unfold BirthShortDoneTerminalPassiveR4.hostStep
  exact localStep_rotateConfig
    (Q := ExpiringAgentState psi kappa tau)
    (by omega : 2 <= n) ring
    (fun l r => BirthShortDoneTerminalHost.row
      hpsi (by decide : 0 < 2) h2 l r)
    anchor C e

/-- Fold-level scheduler reindexing: a canonical word on the pulled-back
configuration equals the pulled-back result of its physical rotated word. -/
theorem hostFold_rotateConfig
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (word : List (Fin n)) :
    word.foldl (hostStep hpsi h2 ring) (rotateConfig ring anchor C) =
      rotateConfig ring anchor
        ((rotateWord ring anchor word).foldl
          (hostStep hpsi h2 ring) C) := by
  induction word generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.foldl_cons, rotateWord, List.map_cons]
      rw [hostStep_rotateConfig hpsi h2 hn kappa tau ring anchor C e]
      exact ih
        (C := hostStep hpsi h2 ring C (rotateIndex ring anchor e))

/-- Same-original-word form.  `word` is the literal physical scheduler word;
only its alphabet is reindexed for the fixed-site proof. -/
theorem hostFold_unrotateWord
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (word : List (Fin n)) :
    (unrotateWord ring anchor word).foldl
        (hostStep hpsi h2 ring) (rotateConfig ring anchor C) =
      rotateConfig ring anchor
        (word.foldl (hostStep hpsi h2 ring) C) := by
  have h := hostFold_rotateConfig hpsi h2 hn kappa tau ring anchor C
    (unrotateWord ring anchor word)
  simpa only [rotateWord_unrotateWord] using h

/-! ## Local predicates at an arbitrary physical anchor -/

/-- The exact three-cell hypothesis used by fixed `LocalLine3`, translated to
an arbitrary cyclic physical location.  Nothing outside these three cells is
constrained. -/
structure LocalLine3At (hpsi : 0 < psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop where
  pass0 : Passive (raw (C anchor))
  pass1 : Passive (raw (C (ring.rightNeighbor anchor)))
  pass2 : Passive
    (raw (C (ring.rightNeighbor (ring.rightNeighbor anchor))))
  lab0 : (raw (C anchor)).label.val = 0
  lab1 : (raw (C (ring.rightNeighbor anchor))).label.val = 1
  lab2 :
    (raw (C (ring.rightNeighbor (ring.rightNeighbor anchor)))).label.val =
      2 % psi

/-- Pulling back an arbitrary physical triple gives exactly the frozen
fixed-site `LocalLine3` premise. -/
theorem localLine3At_rotateConfig
    (hpsi : 0 < psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (h : LocalLine3At hpsi hn ring anchor C) :
    LocalLine3 hpsi hn (rotateConfig ring anchor C) := by
  refine {
    pass0 := ?_
    pass1 := ?_
    pass2 := ?_
    lab0 := ?_
    lab1 := ?_
    lab2 := ?_ }
  · change Passive (raw (C (rotateIndex ring anchor (p0 hn))))
    rw [rotateIndex_p0 hn ring anchor]
    exact h.pass0
  · change Passive (raw (C (rotateIndex ring anchor (p1 hn))))
    rw [rotateIndex_p1 hn ring anchor]
    exact h.pass1
  · change Passive (raw (C (rotateIndex ring anchor (p2 hn))))
    rw [rotateIndex_p2 hn ring anchor]
    exact h.pass2
  · change (raw (C (rotateIndex ring anchor (p0 hn)))).label.val = 0
    rw [rotateIndex_p0 hn ring anchor]
    exact h.lab0
  · change (raw (C (rotateIndex ring anchor (p1 hn)))).label.val = 1
    rw [rotateIndex_p1 hn ring anchor]
    exact h.lab1
  · change
      (raw (C (rotateIndex ring anchor (p2 hn)))).label.val = 2 % psi
    rw [rotateIndex_p2 hn ring anchor]
    exact h.lab2

/-- Fixed safe-edge syntax pulled back from an actual physical edge.  Thus the
excluded edges are exactly the rotated copies of `p2` and `leftCross`. -/
def SafeLine3EdgeAt (hn : 4 <= n) (ring : DirectedRing n)
    (anchor e : Fin n) : Prop :=
  SafeLine3Edge hn (unrotateIndex ring anchor e)

/-- Physical versions of the two internal Local3 scheduler letters. -/
def InternalLine3EdgeAt (hn : 4 <= n) (ring : DirectedRing n)
    (anchor e : Fin n) : Prop :=
  InternalLine3Edge hn (unrotateIndex ring anchor e)

/-- Width-two completed WAIT entry, viewed at the chosen physical anchor. -/
def OrderedWaitEntry2At (hn : 4 <= n) (ring : DirectedRing n)
    (anchor : Fin n) (C : FC n psi kappa tau) : Prop :=
  OrderedWaitEntry2 hn (rotateConfig ring anchor C)

/-- The current cap test is rotation-equivariant because it reads only the
actual selected endpoint and its actual right neighbor. -/
theorem rowCap2_rotateConfig_iff
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 2 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n) :
    RowCap2 hpsi h2 kappa ring (rotateConfig ring anchor C) e ↔
      RowCap2 hpsi h2 kappa ring C (rotateIndex ring anchor e) := by
  unfold RowCap2 rotateConfig
  dsimp only
  rw [rotateIndex_rightNeighbor hn ring anchor e]

/-- The negative current-row test transports with the same coordinates. -/
theorem rowPreCap2_rotateConfig_iff
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 2 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n) :
    RowPreCap2 hpsi h2 kappa ring (rotateConfig ring anchor C) e ↔
      RowPreCap2 hpsi h2 kappa ring C (rotateIndex ring anchor e) := by
  unfold RowPreCap2
  exact not_congr
    (rowCap2_rotateConfig_iff hpsi h2 hn kappa tau ring anchor C e)

/-- The accepted clock projection itself is spatially equivariant. -/
theorem rowProjection2_rotateConfig_iff
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 2 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n) :
    RowProjection2 hpsi h2 kappa tau ring
        (rotateConfig ring anchor C) e ↔
      RowProjection2 hpsi h2 kappa tau ring C
        (rotateIndex ring anchor e) := by
  unfold RowProjection2 rotateConfig
  dsimp only
  rw [rotateIndex_rightNeighbor hn ring anchor e]

/-! ## Physical endpoint on the original coordinates -/

/-- Arbitrary-location version of the accepted physical endpoint.  Entry is
measured on the chosen anchor after an actually executed prefix of the ORIGINAL
physical word.  In the cap branch the displayed physical edge is still current
and has not been executed. -/
def Local3PhysicalEndpointAt
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (es : List (Fin n)) : Prop :=
  (exists pre post,
    es = pre ++ post /\
    OrderedWaitEntry2At hn ring anchor
      (pre.foldl (hostStep hpsi h2 ring) C)) \/
  exists pre e post,
    es = pre ++ (e :: post) /\
    SafeLine3EdgeAt hn ring anchor e /\
    InternalLine3EdgeAt hn ring anchor e /\
    RowCap2 hpsi h2 kappa ring
      (pre.foldl (hostStep hpsi h2 ring) C) e

/-- Canonical fixed-site event attached to one literal original physical word. -/
def Local3EntryOrCapAt
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (es : List (Fin n)) : Prop :=
  Local3EntryOrCap hpsi h2 hn kappa tau ring
    (rotateConfig ring anchor C) (unrotateWord ring anchor es)

/-- A fixed-site physical endpoint on the inverse-rotated word is exactly an
actual physical endpoint on the original word. -/
private theorem physicalEndpointAt_of_rotated
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (es : List (Fin n))
    (h : Local3PhysicalEndpoint hpsi h2 hn kappa tau ring
      (rotateConfig ring anchor C) (unrotateWord ring anchor es)) :
    Local3PhysicalEndpointAt hpsi h2 hn kappa tau ring anchor C es := by
  rcases h with hentry | hcap
  · rcases hentry with ⟨pre, post, hword, hwait⟩
    refine Or.inl
      ⟨rotateWord ring anchor pre, rotateWord ring anchor post, ?_, ?_⟩
    · calc
        es = rotateWord ring anchor (unrotateWord ring anchor es) :=
          (rotateWord_unrotateWord ring anchor es).symm
        _ = rotateWord ring anchor (pre ++ post) :=
          congrArg (rotateWord ring anchor) hword
        _ = rotateWord ring anchor pre ++ rotateWord ring anchor post := by
          simp [rotateWord]
    · unfold OrderedWaitEntry2At
      rw [hostFold_rotateConfig hpsi h2 hn kappa tau ring anchor C pre]
        at hwait
      exact hwait
  · rcases hcap with ⟨pre, e, post, hword, hsafe, hint, hrow⟩
    refine Or.inr
      ⟨rotateWord ring anchor pre, rotateIndex ring anchor e,
        rotateWord ring anchor post, ?_, ?_, ?_, ?_⟩
    · calc
        es = rotateWord ring anchor (unrotateWord ring anchor es) :=
          (rotateWord_unrotateWord ring anchor es).symm
        _ = rotateWord ring anchor (pre ++ (e :: post)) :=
          congrArg (rotateWord ring anchor) hword
        _ = rotateWord ring anchor pre ++
            (rotateIndex ring anchor e :: rotateWord ring anchor post) := by
          simp [rotateWord]
    · unfold SafeLine3EdgeAt
      simpa only [unrotateIndex_rotateIndex] using hsafe
    · unfold InternalLine3EdgeAt
      simpa only [unrotateIndex_rotateIndex] using hint
    · have hrun := hostFold_rotateConfig
        hpsi h2 hn kappa tau ring anchor C pre
      rw [hrun] at hrow
      exact
        (rowCap2_rotateConfig_iff hpsi h2 (by omega : 2 <= n)
          kappa tau ring anchor
          ((rotateWord ring anchor pre).foldl
            (hostStep hpsi h2 ring) C) e).1 hrow

/-- Public arbitrary-location consumer of the accepted recursive event. -/
theorem Local3EntryOrCapAt_physical_endpoint
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (es : List (Fin n))
    (h : Local3EntryOrCapAt hpsi h2 hn kappa tau ring anchor C es) :
    Local3PhysicalEndpointAt hpsi h2 hn kappa tau ring anchor C es := by
  unfold Local3EntryOrCapAt at h
  exact physicalEndpointAt_of_rotated
    hpsi h2 hn kappa tau ring anchor C es
    (Local3EntryOrCap_physical_endpoint
      hpsi h2 hn kappa tau ring (rotateConfig ring anchor C)
        (unrotateWord ring anchor es) h)

/-- Direct matcher consumer on the ORIGINAL physical word.  The matcher sees
only the inverse-rotated alphabet; the physical endpoint is returned on the
original configuration and original scheduler coordinates. -/
theorem twoCross_success_physical_endpoint_at
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (hline : LocalLine3At hpsi hn ring anchor C)
    (es : List (Fin n))
    (hs : runWord (twoCrossStep hn) (.active false)
      (unrotateWord ring anchor es) = .success) :
    Local3PhysicalEndpointAt hpsi h2 hn kappa tau ring anchor C es := by
  apply physicalEndpointAt_of_rotated
    hpsi h2 hn kappa tau ring anchor C es
  exact twoCross_success_physical_endpoint
    hpsi h2 hn kappa tau ring
    (rotateConfig ring anchor C)
    (localLine3At_rotateConfig hpsi hn ring anchor C hline)
    (unrotateWord ring anchor es) hs

/-! ## Exact finite-uniform raw-word reindexing -/

private theorem reindexListSum_eq_of_perm {xs ys : List Nat}
    (hperm : xs.Perm ys) : xs.sum = ys.sum := by
  induction hperm with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simpa [List.sum_cons] using Nat.add_left_comm ..
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem reindexNodup_ofFn_of_injective {m : Nat} {A : Type}
    (f : Fin m -> A) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

/-- Reindex one uniform `Fin m` sum by a concrete permutation. -/
private theorem ofFn_sum_reindex {m : Nat}
    (forward backward : Fin m -> Fin m)
    (hleft : forall edge, backward (forward edge) = edge)
    (hright : forall edge, forward (backward edge) = edge)
    (value : Fin m -> Nat) :
    (List.ofFn (fun edge => value (forward edge))).sum =
      (List.ofFn value).sum := by
  have hforwardInjective : Function.Injective forward := by
    intro x y hxy
    rw [← hleft x, ← hleft y, hxy]
  have hforwardNodup : (List.ofFn forward).Nodup :=
    reindexNodup_ofFn_of_injective forward hforwardInjective
  have hidNodup : (List.ofFn (fun edge : Fin m => edge)).Nodup :=
    reindexNodup_ofFn_of_injective (fun edge : Fin m => edge)
      (fun _ _ h => h)
  have hperm : (List.ofFn forward).Perm
      (List.ofFn (fun edge : Fin m => edge)) := by
    apply (List.perm_ext_iff_of_nodup hforwardNodup hidNodup).2
    intro edge
    constructor
    · intro _
      exact List.mem_ofFn.mpr ⟨edge, rfl⟩
    · intro _
      exact List.mem_ofFn.mpr ⟨backward edge, hright edge⟩
  have hmap := hperm.map value
  have hsum := reindexListSum_eq_of_perm hmap
  simpa [List.map_ofFn, Function.comp_def] using hsum

/-- Coordinatewise permutation of every literal raw scheduler word preserves
`wordSum` exactly, including multiplicity.  The proof uses the existing
`wordSum_succ`, so it respects that definition's reverse-word enumeration. -/
theorem wordSum_reindex {m : Nat}
    (forward backward : Fin m -> Fin m)
    (hleft : forall edge, backward (forward edge) = edge)
    (hright : forall edge, forward (backward edge) = edge)
    (T : Nat) (f : List (Fin m) -> Nat) :
    FixedSpanRenewalPayload.wordSum m T
        (fun word => f (word.map forward)) =
      FixedSpanRenewalPayload.wordSum m T f := by
  induction T generalizing f with
  | zero =>
      simp [FixedSpanRenewalPayload.wordSum, allSchedules]
  | succ T ih =>
      rw [FixedSpanRenewalPayload.wordSum_succ,
        FixedSpanRenewalPayload.wordSum_succ]
      calc
        (List.ofFn (fun e : Fin m =>
          FixedSpanRenewalPayload.wordSum m T
            (fun u => f ((e :: u).map forward)))).sum =
          (List.ofFn (fun e : Fin m =>
            FixedSpanRenewalPayload.wordSum m T
              (fun u => f (forward e :: u)))).sum := by
            apply ofFn_sum_eq
            intro e
            simpa only [List.map_cons] using
              ih (f := fun v => f (forward e :: v))
        _ = (List.ofFn (fun e : Fin m =>
            FixedSpanRenewalPayload.wordSum m T
              (fun u => f (e :: u)))).sum := by
          exact ofFn_sum_reindex forward backward hleft hright
            (fun e => FixedSpanRenewalPayload.wordSum m T
              (fun u => f (e :: u)))

/-! ## Arbitrary-location Local3 numerator and 1/16 mass -/

/-- Indicator on an ORIGINAL physical scheduler word.  The fixed proof event
sees the inverse-rotated alphabet and pulled-back physical state. -/
noncomputable def actualEventBitAt
    (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (es : List (Fin n)) : Nat :=
  actualEventBit h2 hn kappa tau ring
    (rotateConfig ring anchor C) (unrotateWord ring anchor es)

/-- Exact numerator over the same `n^T` original raw scheduler words. -/
noncomputable def actualEventCountAt
    (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T
    (actualEventBitAt h2 hn kappa tau ring anchor C)

/-- Counted arbitrary-location words are genuine physical endpoint words on the
original host, not merely canonical matcher outcomes. -/
theorem actualEventBitAt_one_physical_endpoint
    (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (es : List (Fin n))
    (hbit : actualEventBitAt h2 hn kappa tau ring anchor C es = 1) :
    Local3PhysicalEndpointAt (by omega : 0 < psi) h2 hn
      kappa tau ring anchor C es := by
  classical
  by_cases he : Local3EntryOrCapAt (by omega : 0 < psi) h2 hn
      kappa tau ring anchor C es
  · exact Local3EntryOrCapAt_physical_endpoint
      (by omega : 0 < psi) h2 hn kappa tau ring anchor C es he
  · have he' :
        ¬ Local3EntryOrCap (by omega : 0 < psi) h2 hn
          kappa tau ring (rotateConfig ring anchor C)
            (unrotateWord ring anchor es) := by
      simpa only [Local3EntryOrCapAt] using he
    simp [actualEventBitAt, actualEventBit, he'] at hbit

/-- Spatial reindexing changes neither the exact Local3 event numerator nor any
scheduler-word multiplicity. -/
theorem actualEventCountAt_eq
    (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (T : Nat) :
    actualEventCountAt h2 hn kappa tau ring anchor C T =
      actualEventCount h2 hn kappa tau ring
        (rotateConfig ring anchor C) T := by
  unfold actualEventCountAt actualEventBitAt actualEventCount
  simpa only [unrotateWord] using
    wordSum_reindex
      (forward := unrotateIndex ring anchor)
      (backward := rotateIndex ring anchor)
      (hleft := rotateIndex_unrotateIndex ring anchor)
      (hright := unrotateIndex_rotateIndex ring anchor)
      T
      (actualEventBit h2 hn kappa tau ring
        (rotateConfig ring anchor C))

/-- The accepted Local3 `1/16` numerator bound at an arbitrary physical cyclic
location.  Outside records remain unrestricted exactly as in fixed Local3. -/
theorem local3_entry_or_cap_sixteenth_at
    (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (hline : LocalLine3At (by omega : 0 < psi) hn ring anchor C) :
    n^(4*n) <= 16 *
      actualEventCountAt h2 hn kappa tau ring anchor C (4*n) := by
  rw [actualEventCountAt_eq h2 hn kappa tau ring anchor C (4*n)]
  exact local3_entry_or_cap_sixteenth
    h2 hn kappa tau ring (rotateConfig ring anchor C)
    (localLine3At_rotateConfig
      (by omega : 0 < psi) hn ring anchor C hline)

/-- Existential chosen-triple consumer.  The only existential premise is the
initial physical location of an actual LocalLine3 triple; no global cyclic
labels, future safe word, independence, or arbitrary-state entry is assumed. -/
theorem exists_local3_entry_or_cap_sixteenth_at
    (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau)
    (htriple : exists anchor : Fin n,
      LocalLine3At (by omega : 0 < psi) hn ring anchor C) :
    exists anchor : Fin n,
      n^(4*n) <= 16 *
        actualEventCountAt h2 hn kappa tau ring anchor C (4*n) := by
  rcases htriple with ⟨anchor, hline⟩
  exact ⟨anchor,
    local3_entry_or_cap_sixteenth_at
      h2 hn kappa tau ring anchor C hline⟩

#print axioms BirthShortDoneTerminalPassiveLocal3Rotation.rotateIndex_rightNeighbor
#print axioms BirthShortDoneTerminalPassiveLocal3Rotation.hostStep_rotateConfig
#print axioms BirthShortDoneTerminalPassiveLocal3Rotation.hostFold_unrotateWord
#print axioms BirthShortDoneTerminalPassiveLocal3Rotation.Local3EntryOrCapAt_physical_endpoint
#print axioms BirthShortDoneTerminalPassiveLocal3Rotation.wordSum_reindex
#print axioms BirthShortDoneTerminalPassiveLocal3Rotation.actualEventCountAt_eq
#print axioms BirthShortDoneTerminalPassiveLocal3Rotation.local3_entry_or_cap_sixteenth_at
#print axioms BirthShortDoneTerminalPassiveLocal3Rotation.exists_local3_entry_or_cap_sixteenth_at

end BirthShortDoneTerminalPassiveLocal3Rotation
