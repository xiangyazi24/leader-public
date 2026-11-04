import Leader.L3.Top.FreshTailTicketBarrier

/-!
Q7c P.3 J3: the finite visit-ticket
injection before the first genuine border tail and the accepted-port
bound (r^2+3r)/2 <= r + r^2 + 1.

The injection is the actual chronological spent list of the genealogy
(J2 identifies its entries with the recorded comparison port receipts;
here only the count bridge topFreshTailTicketReceiptCountEq is used).
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A duplicate-free list inside another list is no longer.
Consumer: the ticket counts below. -/
theorem topFreshTailTicketNodupLengthLe
    {α : Type} [DecidableEq α] :
    ∀ (l L : List α), l.Nodup → (∀ x ∈ l, x ∈ L) → l.length ≤ L.length := by
  intro l
  induction l with
  | nil => intro L _ _; exact Nat.zero_le _
  | cons a l ih =>
      intro L hl hsub
      rw [List.nodup_cons] at hl
      have ha : a ∈ L := hsub a (List.mem_cons_self)
      have hrest : ∀ x ∈ l, x ∈ L.erase a := by
        intro x hx
        have hne : x ≠ a := by
          intro h; subst h; exact hl.1 hx
        exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem a hx))
      have h1 := ih (L.erase a) hl.2 hrest
      rw [List.length_erase_of_mem ha] at h1
      have h2 := List.length_pos_of_mem ha
      simp only [List.length_cons]
      omega

/-- filterMap by a partial map that is injective on the list keeps a
list duplicate-free. Consumer: the ticket counts below. -/
theorem topFreshTailTicketNodupFilterMap
    {α β : Type} (f : α → Option β) :
    ∀ l : List α, l.Nodup →
      (∀ x ∈ l, ∀ y ∈ l, ∀ z : β, f x = some z → f y = some z → x = y) →
      (l.filterMap f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; exact List.nodup_nil
  | cons a l ih =>
      intro hl hinj
      rw [List.nodup_cons] at hl
      have hrest := ih hl.2 (fun x hx y hy z hfx hfy =>
        hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) z hfx hfy)
      rw [List.filterMap_cons]
      cases hfa : f a with
      | none => exact hrest
      | some b =>
          rw [List.nodup_cons]
          refine ⟨?_, hrest⟩
          intro hb
          rw [List.mem_filterMap] at hb
          obtain ⟨y, hy, hfy⟩ := hb
          have := hinj a List.mem_cons_self y (List.mem_cons_of_mem a hy) b hfa hfy
          subst this
          exact hl.1 hy

/-- Splitting a list by a decidable predicate into two filterMaps.
Consumer: the triangular ticket count. -/
theorem topFreshTailTicketSplitLength
    {α β γ : Type} (P : α → Prop) [DecidablePred P] (f : α → β) (g : α → γ) :
    ∀ l : List α,
      (l.filterMap (fun x => if P x then some (f x) else none)).length +
      (l.filterMap (fun x => if P x then none else some (g x))).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases ha : P a
      · simp [List.filterMap_cons, ha]
        omega
      · simp [List.filterMap_cons, ha]
        omega

/-- At most m duplicate-free naturals below m. Consumer: the ticket
counts below. -/
theorem topFreshTailTicketNatNodupBound
    (m : Nat) (l : List Nat) (hl : l.Nodup) (hlt : ∀ x ∈ l, x < m) :
    l.length ≤ m := by
  have h := topFreshTailTicketNodupLengthLe l (List.range m) hl
    (fun x hx => List.mem_range.2 (hlt x hx))
  rw [List.length_range] at h
  exact h

/-- The oldVisit cells (i,k) with i <= k and 1 <= k < m+1 number at
most (m+1)(m+2)/2 - 1: twice the count plus two is at most (m+1)(m+2).
Consumer: topFreshTailPreTailAcceptedPortBound. -/
theorem topFreshTailTicketTriangleBound :
    ∀ (m : Nat) (l : List (Nat × Nat)), l.Nodup →
      (∀ p ∈ l, p.1 ≤ p.2 ∧ 0 < p.2 ∧ p.2 < m + 1) →
      2 * l.length + 2 ≤ (m + 1) * (m + 2) := by
  intro m
  induction m with
  | zero =>
      intro l _ hp
      cases l with
      | nil => simp
      | cons p rest =>
          have := hp p List.mem_cons_self
          omega
  | succ m ih =>
      intro l hl hp
      let A := l.filterMap (fun p => if p.2 < m + 1 then some p else none)
      let B := l.filterMap (fun p => if p.2 < m + 1 then none else some p.1)
      have hsplit : A.length + B.length = l.length :=
        topFreshTailTicketSplitLength (fun p : Nat × Nat => p.2 < m + 1)
          (fun p => p) (fun p => p.1) l
      have hA : A.Nodup := by
        apply topFreshTailTicketNodupFilterMap _ l hl
        intro x _ y _ z hx hy
        by_cases h1 : x.2 < m + 1
        · by_cases h2 : y.2 < m + 1
          · simp [h1] at hx; simp [h2] at hy; rw [hx, hy]
          · simp [h2] at hy
        · simp [h1] at hx
      have hB : B.Nodup := by
        apply topFreshTailTicketNodupFilterMap _ l hl
        intro x hx' y hy' z hx hy
        have hpx := hp x hx'
        have hpy := hp y hy'
        by_cases h1 : x.2 < m + 1
        · simp [h1] at hx
        · by_cases h2 : y.2 < m + 1
          · simp [h2] at hy
          · simp [h1] at hx; simp [h2] at hy
            have hx2 : x.2 = m + 1 := by omega
            have hy2 : y.2 = m + 1 := by omega
            cases x; cases y
            simp only at hx hy hx2 hy2
            rw [hx, hy, hx2, hy2]
      have hAbound := ih A hA (by
        intro p hpA
        rw [List.mem_filterMap] at hpA
        obtain ⟨q, hq, hqp⟩ := hpA
        by_cases h1 : q.2 < m + 1
        · simp [h1] at hqp
          subst hqp
          have := hp q hq
          omega
        · simp [h1] at hqp)
      have hBbound : B.length ≤ m + 2 := by
        apply topFreshTailTicketNatNodupBound (m + 2) B hB
        intro x hxB
        rw [List.mem_filterMap] at hxB
        obtain ⟨q, hq, hqx⟩ := hxB
        by_cases h1 : q.2 < m + 1
        · simp [h1] at hqx
        · simp [h1] at hqx
          have := hp q hq
          omega
      have key : (m + 1 + 1) * (m + 1 + 2) = (m + 1) * (m + 2) + 2 * (m + 2) := by
        rw [Nat.mul_comm (m + 1 + 1) (m + 1 + 2), Nat.mul_succ, Nat.mul_comm (m + 1 + 2) (m + 1)]
        have : (m + 1) * (m + 1 + 2) = (m + 1) * (m + 2) + (m + 1) := by
          rw [show m + 1 + 2 = (m + 2) + 1 by omega, Nat.mul_succ]
        rw [this]
        omega
      rw [key]
      omega

/-- The inherited-ticket code of an origin. -/
def topFreshTailTicketInheritedCode {r : Nat} : TopFreshTailOrigin r → Option Nat
  | .inherited i => some i.val
  | _ => none

/-- The oldVisit cell of an origin. -/
def topFreshTailTicketVisitCode {r : Nat} : TopFreshTailOrigin r → Option (Nat × Nat)
  | .oldVisit i k => some (i.val, k.val)
  | _ => none

/-- A list of nonfresh tickets is its inherited part plus its oldVisit
part. Consumer: topFreshTailTicketSpentBound. -/
theorem topFreshTailTicketNonfreshSplit
    {r : Nat} :
    ∀ l : List (TopFreshTailOrigin r),
      (∀ o ∈ l, topFreshTailTicketIsFresh o = false) →
      l.length = (l.filterMap topFreshTailTicketInheritedCode).length +
        (l.filterMap topFreshTailTicketVisitCode).length := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons o rest ih =>
      intro h
      have hrest := ih (fun x hx => h x (List.mem_cons_of_mem o hx))
      have ho := h o List.mem_cons_self
      cases o with
      | inherited i =>
          simp [List.filterMap_cons, topFreshTailTicketInheritedCode,
            topFreshTailTicketVisitCode]
          omega
      | oldVisit i k =>
          simp [List.filterMap_cons, topFreshTailTicketInheritedCode,
            topFreshTailTicketVisitCode]
          omega
      | freshBorder b => cases ho

/-- The spent list of a reached cut splits into at most r inherited
tickets and oldVisit tickets with 2(#oldVisit) + 2 <= r(r+1).
Consumer: topFreshTailPreTailVisitCharge. -/
theorem topFreshTailTicketSpentBound
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (H : TopFreshTailTicketHistory ring C s Z) :
    let L := topFreshTailTicketSpent (topFreshTailGenealogy ring C s Z)
    L.length = (L.filterMap topFreshTailTicketInheritedCode).length +
        (L.filterMap topFreshTailTicketVisitCode).length ∧
    (L.filterMap topFreshTailTicketInheritedCode).length ≤ topClockSpan n ∧
    2 * (L.filterMap topFreshTailTicketVisitCode).length + 2 ≤
      topClockSpan n * (topClockSpan n + 1) := by
  intro L
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  refine ⟨topFreshTailTicketNonfreshSplit L
      (fun o ho => topFreshTailTicketSpentNonfresh _ o ho), ?_, ?_⟩
  · apply topFreshTailTicketNatNodupBound _ _
      (topFreshTailTicketNodupFilterMap _ L H.spentNodup ?_)
    · intro x hx
      rw [List.mem_filterMap] at hx
      obtain ⟨o, _, ho⟩ := hx
      cases o with
      | inherited i =>
          simp [topFreshTailTicketInheritedCode] at ho
          rw [← ho]; exact i.isLt
      | oldVisit i k => simp [topFreshTailTicketInheritedCode] at ho
      | freshBorder b => simp [topFreshTailTicketInheritedCode] at ho
    · intro x _ y _ z hx hy
      cases x <;> cases y <;>
        simp [topFreshTailTicketInheritedCode] at hx hy
      rename_i i j
      exact congrArg _ (Fin.ext (hx.trans hy.symm))
  · have htri := topFreshTailTicketTriangleBound (topClockSpan n - 1)
      (L.filterMap topFreshTailTicketVisitCode)
      (topFreshTailTicketNodupFilterMap _ L H.spentNodup (by
        intro x _ y _ z hx hy
        cases x with
        | oldVisit i k =>
            cases y with
            | oldVisit i' k' =>
                simp only [topFreshTailTicketVisitCode, Option.some.injEq] at hx hy
                have h := hx.trans hy.symm
                simp only [Prod.mk.injEq] at h
                rw [Fin.ext h.1, Fin.ext h.2]
            | inherited _ => simp [topFreshTailTicketVisitCode] at hy
            | freshBorder _ => simp [topFreshTailTicketVisitCode] at hy
        | inherited _ => simp [topFreshTailTicketVisitCode] at hx
        | freshBorder _ => simp [topFreshTailTicketVisitCode] at hx))
      (by
        intro p hp
        rw [List.mem_filterMap] at hp
        obtain ⟨o, ho, hop⟩ := hp
        cases o with
        | inherited i => simp [topFreshTailTicketVisitCode] at hop
        | oldVisit i k =>
            simp [topFreshTailTicketVisitCode] at hop
            have hsh := H.spentVisitShape i k ho
            rw [← hop]
            have := k.isLt
            simp only
            omega
        | freshBorder b => simp [topFreshTailTicketVisitCode] at hop)
    have he1 : topClockSpan n - 1 + 1 = topClockSpan n := by omega
    have he2 : topClockSpan n - 1 + 2 = topClockSpan n + 1 := by omega
    rw [he1, he2] at htri
    exact htri

/-- When every consumed entry has a nonfresh origin, the spent list
has the consumed list's length. Consumer:
topFreshTailPreTailAcceptedPortBound. -/
theorem topFreshTailTicketSpentLengthOfAll
    {n : Nat} (G : TopFreshTailGenealogyState n)
    (h : ∀ entry ∈ G.consumed, ∃ o : TopFreshTailOrigin (topClockSpan n),
      entry.2 = some o ∧ topFreshTailTicketIsFresh o = false) :
    (topFreshTailTicketSpent G).length = G.consumed.length := by
  unfold topFreshTailTicketSpent
  generalize G.consumed = L at h
  induction L with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨o, ho, hf⟩ := h entry List.mem_cons_self
      have hrest := ih (fun x hx => h x (List.mem_cons_of_mem entry hx))
      rw [List.filterMap_cons, ho]
      simp only [hf, Bool.false_eq_true, if_false, List.length_cons]
      omega

/-- Item 5, sharp form. On every reached cut of the actual trace
none of whose strict prefixes accepts the first genuine border tail,
the comparison source-port receipts number at most r inherited
tickets, plus the oldVisit tickets (2 * #oldVisit + 2 <= r(r+1)),
plus one for the anchor: twice the receipt count is at most r^2 + 3r.
Consumer: P.3 J3 (topFreshTailPreTailVisitCharge). -/
theorem topFreshTailPreTailAcceptedPortBound
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (hpre : ∀ (pre suffix : List (Fin n)),
      pre ++ suffix = Z.2 → suffix ≠ [] →
      ¬ topClockGenuineTailAccepted C s (topFixedTraceRun ring C pre)) :
    ∃ inherited descendants : Nat,
      inherited ≤ topClockSpan n ∧
      2 * descendants + 2 ≤ topClockSpan n * (topClockSpan n + 1) ∧
      topFreshTailPortReceiptCount s Z ≤ inherited + descendants + 1 := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  rcases List.eq_nil_or_concat Z.2 with hnil | ⟨w, e, hw⟩
  · refine ⟨0, 0, Nat.zero_le _, by
      have : 2 ≤ topClockSpan n * (topClockSpan n + 1) := by
        have := Nat.mul_le_mul (show 1 ≤ topClockSpan n by omega)
          (show 2 ≤ topClockSpan n + 1 by omega)
        omega
      omega, ?_⟩
    rw [hreach, hnil, topFreshTailTicketReceiptCountEq ring C s hn []]
    have hw : (topFixedTraceRun ring C ([] : List (Fin n))).snd = [] := rfl
    simp [topFreshTailGenealogy, topFreshTailGenealogyReplay,
      topFreshTailGenealogyInitial, hw]
  · rw [List.concat_eq_append] at hw
    have hYreach : topClockReached ring C (topFixedTraceRun ring C w) := by
      unfold topClockReached
      rw [topFreshTailAuditRunWord]
    have hB := topFreshTailFirstBorderBarrier ring C s hn hbad w (by
      intro pre suffix h hne
      exact hpre pre (suffix ++ [e]) (by rw [hw, ← h, List.append_assoc]) (by simp))
    have hH := topFreshTailOldVisitIssuedOnceAndNonTail ring C s hn hbad
      (topFixedTraceRun ring C w) hYreach
    obtain ⟨hsplit, hinh, hvis⟩ := topFreshTailTicketSpentBound ring C s hn _ hH
    have hlen := topFreshTailTicketSpentLengthOfAll _ hB.spentAll
    refine ⟨_, _, hinh, hvis, ?_⟩
    have hZ : Z = topFixedTraceNext ring C (topFixedTraceRun ring C w) e := by
      rw [hreach, hw, topFreshTailFifoRunSnoc]
    rw [hZ, topFreshTailTicketReceiptCountStep,
      topFreshTailTicketReceiptCountEq ring C s hn w, ← hlen, hsplit]
    have : (topFreshTailGenealogyPortExport ring C s
        (topFixedTraceRun ring C w) e).toList.length ≤ 1 := by
      cases topFreshTailGenealogyPortExport ring C s (topFixedTraceRun ring C w) e <;>
        simp
    omega

/-- Item 5. The finite ticket injection: the P.3 pre-tail charge
TopFreshTailPreTailCharge holds outright (inherited <= r, descendants
<= r^2), with the sharper count (r^2+3r)/2 from
topFreshTailPreTailAcceptedPortBound.
Consumer: P.3 J3, via topFreshTailFIFOReceiptBoundOfCharge into
TopFreshTailFIFOReceiptBound. -/
theorem topFreshTailPreTailVisitCharge
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopFreshTailPreTailCharge ring C s := by
  intro Z hreach hpre
  obtain ⟨inherited, descendants, hi, hd, hcount⟩ :=
    topFreshTailPreTailAcceptedPortBound ring C s hn hbad Z hreach hpre
  refine ⟨inherited, descendants, hi, ?_, hcount⟩
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hsq : topClockSpan n ≤ topClockSpan n * topClockSpan n :=
    Nat.le_mul_self _
  rw [Nat.pow_two]
  rw [Nat.mul_succ] at hd
  omega

/-- The P.3 FIFO receipt bound, now proved: every reached trace before
its first genuine border tail has at most 2r^2+1 comparison source
port receipts. Consumer: P.3 TopClockFreshTailPhase (the Prop
TopFreshTailFIFOReceiptBound in Leader/L3/Top/FreshTail.lean). -/
theorem topFreshTailFIFOReceiptBoundHolds
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopFreshTailFIFOReceiptBound ring C s :=
  topFreshTailFIFOReceiptBoundOfCharge ring hn C s
    (topFreshTailPreTailVisitCharge ring C s hn hbad)

end L3

#print axioms L3.topFreshTailTicketNodupLengthLe
#print axioms L3.topFreshTailTicketNodupFilterMap
#print axioms L3.topFreshTailTicketSplitLength
#print axioms L3.topFreshTailTicketNatNodupBound
#print axioms L3.topFreshTailTicketTriangleBound
#print axioms L3.topFreshTailTicketNonfreshSplit
#print axioms L3.topFreshTailTicketSpentBound
#print axioms L3.topFreshTailTicketSpentLengthOfAll
#print axioms L3.topFreshTailPreTailAcceptedPortBound
#print axioms L3.topFreshTailPreTailVisitCharge
#print axioms L3.topFreshTailFIFOReceiptBoundHolds
