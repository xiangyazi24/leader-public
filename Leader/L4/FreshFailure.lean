import Leader.L4.FreshFailureMass
import Leader.L4.FreshEpochEntry
import Leader.L4.FreshPaymentMass
import Leader.L4.FreshGapAssembly

namespace L4.FreshFailure
open RankSupplier RankRenewal TaggedTail FreshEpochEarly

private theorem s_mono {n : Nat} {f g : Fin n → Nat} (h : ∀ e, f e ≤ g e) :
    sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (h 0) (ih (fun e => h e.succ))

private theorem s_const (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    rw [show (List.ofFn (fun _ : Fin n => a)).sum=n*a from ih,Nat.succ_mul,Nat.add_comm]

private theorem s_scale {n : Nat} (C : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => C*f e)=C*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    rw [Nat.mul_add]
    exact congrArg (fun z => C*f 0+z) (ih (fun e => f e.succ))

private theorem run_length {α : Type} {n : Nat} (next : α → Fin n → α)
    (score : α → Nat) (x : α) (t : Nat) (C : Nat)
    (h : ∀ w : List (Fin n), w.length=t → score (GGTiming.runMarks next x w)=C) :
    endpointSum next score t x=C*n^t := by
  induction t generalizing x with
  | zero => simpa [endpointSum,GGTiming.runMarks] using h [] rfl
  | succ t ih =>
    rw [endpointSum]
    have he : ∀ e : Fin n, endpointSum next score t (next x e)=C*n^t := fun e =>
      ih (next x e) (fun w hw => h (e::w) (by simp [hw]))
    simp only [he,s_const,Nat.pow_succ]
    ac_rfl

/-- Padding a word summit only counts freely available suffix labels;
no independence assumption beyond the original uniform raw marks. -/
theorem endpoint_pad {α : Type} {n : Nat} (next : α → Fin n → α)
    (score : α → Nat) (x : α) (t r : Nat) (eq : ∀ z w,
      w.length=r → score (GGTiming.runMarks next z w)=score z) :
    endpointSum next score (t+r) x = n^r * endpointSum next score t x := by
  induction t generalizing x with
  | zero => simpa [endpointSum,Nat.mul_comm] using run_length next score x r (score x) (eq x)
  | succ t ih =>
    rw [show t+1+r=(t+r)+1 by omega,endpointSum,endpointSum,←s_scale]
    congr 1
    funext e
    exact ih (next x e)

/-- Truncated projection comparison on the same raw word set. -/
theorem endpoint_le_words {α β : Type} {n : Nat} (next : α → Fin n → α)
    (other : β → Fin n → β) (f : α → Nat) (g : β → Nat)
    (t : Nat) (x : α) (y : β)
    (h : ∀ w : List (Fin n), w.length=t →
      f (GGTiming.runMarks next x w) ≤ g (GGTiming.runMarks other y w)) :
    endpointSum next f t x≤endpointSum other g t y := by
  induction t generalizing x y with
  | zero => exact h [] rfl
  | succ t ih =>
    exact s_mono (fun e => ih (next x e) (other y e) (fun w hw => h (e::w) (by simp [hw])))

/-- On a live fixed gap, either exit, pay to a strictly larger gap,
or execute a valid literal fixed-gap mark. A non-retirement stop is a
valid final fixed-gap mark and gives the *old* target birth. -/
theorem gap_step {p c n : Nat} (hn : 4≤n) (v e : Fin n) (s : Obs p c n)
    (hs : Protected v s) (hC : COV s.config) :
    let t := advance v s e
    (t.stopped=false ∧ s.donor<t.donor) ∨
    RankPhysical.retirement s.config e=true ∨
    (readyMark s.config v e s.donor ∧ t.config=step s.config e ∧ t.donor=s.donor ∧
      (t.stopped=true ↔ (t.config (liftedSite v (s.donor+1))).leader=true)) := by
  let y := step s.config e
  let pay := geometricPay (s.config e) (s.config (rightNeighbor e))
  let m := (e == liftedSite v s.donor) && pay
  have hv : (y v).leader=true := (protected_supplier_on_mark hn v e s hs).1
  have hret : RankPhysical.retirement s.config e = (pay && (s.config (rightNeighbor e)).mark) := rfl
  by_cases hr : RankPhysical.retirement s.config e=true
  · exact Or.inr (Or.inl hr)
  have hR : (pay && (s.config (rightNeighbor e)).mark)=false := by
    rw [←hret]
    exact Bool.eq_false_iff.mpr hr
  cases hm : m
  · have hN (he : e=liftedSite v s.donor) : pay=false := by
      change ((e == liftedSite v s.donor) && pay)=false at hm
      simpa [he] using hm
    right; right
    refine ⟨⟨hs.1.2.1,hC,hs.2,hN⟩,?_⟩
    have ha : advance v s e = if (y (liftedSite v (s.donor+1))).leader then
        ⟨y,s.donor,true⟩ else ⟨y,s.donor,false⟩ := by
      unfold advance
      change (if s.stopped then s else if stop s.config y v e (s.donor+m.toNat) pay then
        ⟨y,s.donor,true⟩ else ⟨y,s.donor+m.toNat,false⟩)=_
      simp [hs.1.1,hm,stop,hR,hv]
    rw [ha]
    split <;> simp_all [y]
  · have hem : ((e == liftedSite v s.donor) && pay)=true := hm
    have hBoth : (e == liftedSite v s.donor)=true ∧ pay=true := by simpa only [Bool.and_eq_true] using hem
    have he := beq_iff_eq.mp hBoth.1
    have hp := hBoth.2
    have hA := FreshTimerEpoch.paid_landing_off hn s.config e hs.1.2.1 hC hp (Bool.eq_false_iff.mpr hr)
    have hz : liftedSite v (s.donor+1+1)=rightNeighbor (rightNeighbor e) := by
      rw [liftedSite_succ,liftedSite_succ,he]
    have hb : (y (liftedSite v (s.donor+1+1))).leader=false := by rw [hz]; exact hA.2.1
    left
    have ha : advance v s e = ⟨y,s.donor+1,false⟩ := by
      unfold advance
      change (if s.stopped then s else if stop s.config y v e (s.donor+m.toNat) pay then
        ⟨y,s.donor,true⟩ else ⟨y,s.donor+m.toNat,false⟩)=_
      simp [hs.1.1,hm,stop,hR,hv,hb]
    rw [ha]
    exact ⟨rfl,Nat.lt_succ_self _⟩


/-- Lifetime of a frozen geometric gap. This monitor does not reassign
a later gap's birth to the old controller. -/
inductive EarlyState (p c n : Nat) where
  | active (x : Config p c n)
  | born
  | invalid

open Classical in
noncomputable def earlyStart {p c n : Nat} (v : Fin n) (d : Nat) (x : Config p c n) :
    EarlyState p c n :=
  if (x (liftedSite v (d+1))).leader then .born else .active x

open Classical in
noncomputable def earlyNext {p c n : Nat} (v : Fin n) (d : Nat)
    (a : EarlyState p c n) (e : Fin n) : EarlyState p c n :=
  match a with
  | .born => .born
  | .invalid => .invalid
  | .active x => if readyMark x v e d then earlyStart v d (step x e) else .invalid

def earlyScore {p c n : Nat} : EarlyState p c n → Nat
  | .born => 1
  | _ => 0

theorem early_mass_exact {p c n : Nat} (v : Fin n) (d t : Nat) (x : Config p c n) :
    endpointSum (earlyNext v d) earlyScore t (earlyStart v d x) = birthWithin v d t x := by
  classical
  have hborn : ∀ t, endpointSum (earlyNext (p:=p) (c:=c) v d) earlyScore t .born=n^t := by
    intro t
    rw [run_length _ _ _ _ 1]
    · simp
    intro w hw
    clear hw
    induction w with
    | nil => rfl
    | cons e w ih => exact ih
  have hbad : ∀ t, endpointSum (earlyNext (p:=p) (c:=c) v d) earlyScore t .invalid=0 := by
    intro t
    rw [run_length _ _ _ _ 0]
    · simp
    intro w hw
    clear hw
    induction w with
    | nil => rfl
    | cons e w ih => exact ih
  induction t generalizing x with
  | zero =>
    cases h : (x (liftedSite v (d+1))).leader <;> simp [endpointSum,earlyStart,earlyScore,birthWithin,h]
  | succ t ih =>
    cases h : (x (liftedSite v (d+1))).leader
    · simp only [earlyStart,h,Bool.false_eq_true,if_false,birthWithin,endpointSum]
      apply congrArg (sumEdge (n:=n))
      funext e
      by_cases hM : readyMark x v e d <;> simp [earlyNext,hM,ih,hbad]
    · simp [earlyStart,birthWithin,h,hborn]

/-- A clock-limited observer pads all extensions after the cutoff but
ignores their physical actions. In particular the cutoff mark itself
is executed and included. -/
def clockNext {α : Type} {n : Nat} (next : α → Fin n → α)
    (q : Nat × α) (e : Fin n) : Nat × α :=
  match q.1 with
  | 0 => q
  | t+1 => (t,next q.2 e)

theorem clock_mass {α : Type} {n : Nat} (next : α → Fin n → α) (score : α → Nat)
    (t cap : Nat) (x : α) :
    endpointSum (clockNext next) (fun a => score a.2) t (cap,x) =
      n^(t-cap) * endpointSum next score (min t cap) x := by
  induction t generalizing cap x with
  | zero => simp [endpointSum]
  | succ t ih =>
    cases cap with
    | zero =>
      rw [endpointSum]
      simp only [clockNext, ih, Nat.sub_zero,Nat.min_zero,endpointSum,s_const,Nat.pow_succ]
      ac_rfl
    | succ cap =>
      rw [endpointSum,show min (t+1) (cap+1)=min t cap+1 by omega,endpointSum,←s_scale]
      apply congrArg (sumEdge (n:=n))
      funext e
      simpa [clockNext] using ih cap (next x e)

theorem early_cylinder_bound {p c n : Nat} (hn : 4≤n) (hc : 12≤c)
    (v : Fin n) (s : Obs p c n) (hs : Live v s) (hInit : freshInit s.config v s.donor)
    (t : Nat) :
    let h := s.donor+1
    256^h * endpointSum (clockNext (earlyNext v s.donor)) (fun a => earlyScore a.2) t
      (2*n*(c*h),earlyStart v s.donor s.config) ≤ n^t := by
  dsimp only
  rw [clock_mass,early_mass_exact,Nat.mul_left_comm]
  apply Nat.le_trans (Nat.mul_le_mul_left _
    (early_of_freshInit hn hc v hs.2.2.2.2.2 _ (Nat.min_le_right ..) s.config hInit))
  rw [←Nat.pow_add]
  rw [show t - (2*n*(c*(s.donor+1))) + min t (2*n*(c*(s.donor+1))) = t by omega]
  exact Nat.le_refl _ 

theorem late_cylinder_bound {p c n : Nat} (hn : 4≤n) (hc : 12≤c)
    (v : Fin n) (s : Obs p c n) (hs : Live v s) (t : Nat) :
    let h := s.donor+1
    2048^h * endpointSum (clockNext (advance v))
      (fun a => if a.1=0 then FreshPaymentMass.unpaidIndicator s.donor a.2 else 0)
      t (2*n*(c*h),s) ≤ n^t := by
  dsimp only
  let cap := 2*n*(c*(s.donor+1))
  have clock_read {α : Type} (f : α → Fin n → α) (x : α) (m : Nat) (w : List (Fin n)) :
      (GGTiming.runMarks (clockNext f) (m,x) w).1 = m-w.length := by
    induction w generalizing m x with
    | nil => simp [GGTiming.runMarks]
    | cons e w ih =>
      cases m <;> simp [GGTiming.runMarks,clockNext, ih]
  by_cases ht : cap≤t
  · have hle := endpoint_le_words (clockNext (advance v)) (clockNext (advance v))
      (fun a => if a.1=0 then FreshPaymentMass.unpaidIndicator s.donor a.2 else 0)
      (fun a => FreshPaymentMass.unpaidIndicator s.donor a.2) t (cap,s) (cap,s)
      (by intro w hw; rw [clock_read,hw, Nat.sub_eq_zero_of_le ht,if_pos rfl]; exact Nat.le_refl _)
    apply Nat.le_trans (Nat.mul_le_mul_left _ hle)
    rw [clock_mass,Nat.min_eq_right ht,Nat.mul_left_comm]
    apply Nat.le_trans (Nat.mul_le_mul_left _ (FreshPaymentMass.unpaid_gap_tail hn hc v s hs))
    rw [←Nat.pow_add]
    change n^(t-cap+cap)≤n^t
    rw [Nat.sub_add_cancel ht]
    exact Nat.le_refl _
  · have hz := run_length (clockNext (advance v))
        (fun a => if a.1=0 then FreshPaymentMass.unpaidIndicator s.donor a.2 else 0)
        (cap,s) t 0 (by
          intro w hw
          rw [clock_read,hw,if_neg (by omega)])
    change 2048^(s.donor+1) * _ ≤ _
    rw [hz,Nat.zero_mul,Nat.mul_zero]
    exact Nat.zero_le _

inductive FailsHere {p c n : Nat} (v : Fin n) (d : Nat) :
    Obs p c n → List (Fin n) → Prop
  | here {s e w} (hs : s.donor=d) (ready : readyMark s.config v e d)
      (born : (step s.config e (liftedSite v (d+1))).leader=true) :
      FailsHere v d s (e::w)
  | later {s e w} (hs : s.donor=d) (ready : readyMark s.config v e d)
      (ht : (advance v s e).stopped=false) (hd : (advance v s e).donor=d)
      (h : FailsHere v d (advance v s e) w) :
      FailsHere v d s (e::w)

theorem early_of_failsHere {p c n : Nat} (v : Fin n) (d : Nat)
    (s : Obs p c n) (w : List (Fin n))
    (hs : s.stopped=false) (h : FailsHere v d s w) :
    earlyScore (GGTiming.runMarks (earlyNext v d) (earlyStart v d s.config) w)=1 := by
  classical
  have hB (w : List (Fin n)) :
      earlyScore (GGTiming.runMarks (earlyNext (p:=p) (c:=c) v d) .born w)=1 := by
    induction w with
    | nil => rfl
    | cons e w ih => exact ih
  induction h with
  | @here s e w hd hm hb =>
    cases hh : (s.config (liftedSite v (d+1))).leader
    · simpa [GGTiming.runMarks,earlyStart,earlyNext,hh,hm,hb] using hB w
    · simpa [earlyStart,hh] using hB (e::w)
  | @later s e w hd hm ht he h ih =>
    have hf := (RankSupplierPhysical.unstopped_fields v e s hs ht).1
    cases hh : (s.config (liftedSite v (d+1))).leader
    · simpa [GGTiming.runMarks,earlyNext,earlyStart,hh,hm,←hf] using ih ht
    · simpa [earlyStart,hh] using hB (e::w)

theorem unpaid_of_failsHere_prefix {p c n : Nat} (v : Fin n) (d : Nat)
    (s : Obs p c n) (a b : List (Fin n))
    (hs : s.stopped=false) (hd : s.donor=d)
    (h : FailsHere v d s (a++b)) (hNot : ¬ FailsHere v d s a) :
    FreshPaymentMass.unpaidIndicator d (track v s a)=1 := by
  induction a generalizing s with
  | nil => simp [track,GGTiming.runMarks,FreshPaymentMass.unpaidIndicator,hs,hd]
  | cons e a ih =>
    change FailsHere v d s (e::(a++b)) at h
    cases h with
    | here hs hm hb => exact False.elim (hNot (.here hs hm hb))
    | later hs hm ht he h =>
      exact ih (advance v s e) ht he h (fun w => hNot (.later hs hm ht he w))

theorem capped_run {α : Type} {n : Nat} (next : α → Fin n → α)
    (x : α) (cap : Nat) (w : List (Fin n)) :
    GGTiming.runMarks (clockNext next) (cap,x) w =
      (cap-w.length, GGTiming.runMarks next x (w.take cap)) := by
  induction w generalizing cap x with
  | nil => simp [GGTiming.runMarks]
  | cons e w ih =>
    cases cap with
    | zero => simpa [GGTiming.runMarks,clockNext] using (ih x 0)
    | succ cap => simp [GGTiming.runMarks,clockNext,ih]

/-- Inclusive dichotomy: birth within cap is charged early (including
exactly cap); otherwise the prefix of length cap remained live and
unpaid. The same full word feeds both observers. -/
theorem failsHere_cylinder_cover {p c n : Nat} (v : Fin n) (s : Obs p c n)
    (hs : Live v s) (w : List (Fin n)) (cap : Nat)
    (h : FailsHere v s.donor s w) :
    1 ≤ earlyScore (GGTiming.runMarks (clockNext (earlyNext v s.donor))
      (cap,earlyStart v s.donor s.config) w).2 +
    (let z := GGTiming.runMarks (clockNext (advance v)) (cap,s) w
      if z.1=0 then FreshPaymentMass.unpaidIndicator s.donor z.2 else 0) := by
  rw [capped_run,capped_run]
  by_cases hg : FailsHere v s.donor s (w.take cap)
  · rw [early_of_failsHere v s.donor s _ hs.1 hg]
    omega
  · have hcap : cap<w.length := by
      apply Nat.lt_of_not_ge
      intro hn
      exact hg (by simpa [List.take_of_length_le (by omega : w.length≤cap)] using h)
    let a := w.take cap
    let b := w.drop cap
    have hab : a++b=w := List.take_append_drop ..
    have hW : FailsHere v s.donor s (a++b) := hab ▸ h
    have hU := unpaid_of_failsHere_prefix v s.donor s a b hs.1 rfl hW hg
    simp only [Nat.sub_eq_zero_of_le (Nat.le_of_lt hcap)]
    change 1 ≤ _ + FreshPaymentMass.unpaidIndicator s.donor (track v s a)
    rw [hU]
    omega


inductive Phase (p c n : Nat) where
  | live (s : Obs p c n)
  | retired
  | failed (donor : Nat)

open Classical in
noncomputable def freshNext {p c n : Nat} (v : Fin n) :
    Phase p c n → Fin n → Phase p c n
  | .live s,e =>
      if RankPhysical.retirement s.config e then .retired else
      let t := advance v s e
      if t.stopped then .failed s.donor else .live t
  | .retired,_ => .retired
  | .failed d,_ => .failed d

def Failure {p c n : Nat} (a : Phase p c n) : Prop :=
  match a with | .failed _ => True | _ => False

def entryMark {p c n : Nat} (d : Nat) : Phase p c n → Prop
  | .live s => s.donor=d
  | _ => False

/-- First entry either happened on the empty word (initial kill)
or on a surviving paid mark, with strict progress of the gap index. -/
theorem firstGap_step {p c n : Nat} (hn : 4≤n) (v : Fin n)
    (s t : Obs p c n) (e : Fin n) (hs : Protected v s) (hc : COV s.config)
    (h : freshNext v (.live s) e=.live t) :
    s.donor≤t.donor ∧ Protected v t ∧ COV t.config ∧
      (s.donor<t.donor → freshInit t.config v t.donor) := by
  simp only [freshNext] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i ht
      have hf : advance v s e=t := Phase.live.inj h
      have hr : (advance v s e).stopped=false := Bool.eq_false_iff.mpr ht
      subst t
      refine ⟨donor_mono_step v e s,protected_step hn v e s hs hr,?_,?_⟩
      · rw [(RankSupplierPhysical.unstopped_fields v e s hs.1.1 hr).1]
        exact (EntranceCover.cover_closed hn s.config e ⟨hs.1.2.1,hc⟩).2
      · intro hd
        exact (FreshEpochEntry.paid_starts_fresh_epoch hn v e s hs hc hr hd).2.2

/-- Trace decomposition at the first live occurrence of the failure's
donor, with a ready stationary suffix ending at the true first stop. -/
inductive Attributed {p c n : Nat} (v : Fin n) (d : Nat) :
    Obs p c n → List (Fin n) → Prop
  | entry {s w} (hs : s.donor=d) (hw : FailsHere v d s w) : Attributed v d s w
  | before {s t e w} (hs : s.donor<d) (ht : freshNext v (.live s) e=.live t)
      (hw : Attributed v d t w) : Attributed v d s (e::w)

theorem attribution_exact {p c n : Nat} (hn : 4≤n) (v : Fin n)
    (s : Obs p c n) (w : List (Fin n)) (d : Nat)
    (hs : Protected v s) (hc : COV s.config)
    (h : GGTiming.runMarks (freshNext v) (.live s) w=.failed d) :
    Attributed v d s w := by
  classical
  induction w generalizing s with
  | nil => contradiction
  | cons e w ih =>
    have frozen (a : Phase p c n) (ha : ∀ e, freshNext v a e=a) (u : List (Fin n)) :
        GGTiming.runMarks (freshNext v) a u=a := by
      induction u with
      | nil => rfl
      | cons e w ih => simp only [GGTiming.runMarks,ha,ih]
    change GGTiming.runMarks (freshNext v) (freshNext v (.live s) e) w=.failed d at h
    have casesRow := gap_step hn v e s hs hc
    by_cases hRet : RankPhysical.retirement s.config e=true
    · have H : freshNext v (.live s) e=.retired := by simp [freshNext,hRet]
      rw [H,frozen _ (fun _ => rfl) w] at h
      contradiction
    · rcases casesRow with hPay | hR | ⟨hm,hx,hd,hStop⟩
      · have H : freshNext v (.live s) e=.live (advance v s e) := by
          simp [freshNext,hRet,hPay.1]
        rw [H] at h
        have P := firstGap_step hn v s (advance v s e) e hs hc H
        have Z := ih _ P.2.1 P.2.2.1 h
        have hz : (advance v s e).donor≤d := by cases Z with
          | entry he _ => exact Nat.le_of_eq he
          | before he _ _ => exact Nat.le_of_lt he
        exact .before (Nat.lt_of_lt_of_le hPay.2 hz) H Z
      · exact False.elim (hRet hR)
      · by_cases ht : (advance v s e).stopped=true
        · have H : freshNext v (.live s) e=.failed s.donor := by simp [freshNext,hRet,ht]
          rw [H,frozen _ (fun _ => rfl) w] at h
          have hEq := Phase.failed.inj h
          subst d
          exact .entry rfl (.here rfl hm (hx ▸ (hStop.mp ht)))
        · have ht0 := Bool.eq_false_iff.mpr ht
          have H : freshNext v (.live s) e=.live (advance v s e) := by simp [freshNext,hRet,ht0]
          rw [H] at h
          have P := firstGap_step hn v s (advance v s e) e hs hc H
          have Z := ih _ P.2.1 P.2.2.1 h
          cases Z with
          | entry hD hW =>
            have hEq : s.donor=d := hd.symm.trans hD
            exact .entry hEq (.later hEq (hEq ▸ hm) ht0 hD hW)
          | before hD hN hW =>
            exact .before (hd ▸ hD) H (.before hD hN hW)


inductive Watch (p c n : Nat) where
  | waiting (s : Obs p c n)
  | watching (early : Nat × EarlyState p c n) (late : Nat × Obs p c n)
  | never

open Classical in
noncomputable def watchStart {p c n : Nat} (v : Fin n) (d : Nat) (s : Obs p c n) :
    Watch p c n :=
  if s.donor=d then
    let cap := 2*n*(c*(d+1))
    .watching (cap,earlyStart v d s.config) (cap,s)
  else .waiting s

noncomputable def watchPhase {p c n : Nat} (v : Fin n) (d : Nat) :
    Phase p c n → Watch p c n
  | .live t => watchStart v d t
  | _ => .never

noncomputable def watchNext {p c n : Nat} (v : Fin n) (d : Nat) :
    Watch p c n → Fin n → Watch p c n
  | .waiting s,e => watchPhase v d (freshNext v (.live s) e)
  | .watching a b,e => .watching (clockNext (earlyNext v d) a e) (clockNext (advance v) b e)
  | .never,_ => .never

private theorem waiting_eq {p c n : Nat} (v : Fin n) (d : Nat) (s : Obs p c n)
    (e : Fin n) : watchNext v d (.waiting s) e =
      watchPhase v d (freshNext v (.live s) e) := rfl

def earlyCredit {p c n : Nat} : Watch p c n → Nat
  | .watching a _ => earlyScore a.2
  | _ => 0

def lateCredit {p c n : Nat} (d : Nat) : Watch p c n → Nat
  | .watching _ b => if b.1=0 then FreshPaymentMass.unpaidIndicator d b.2 else 0
  | _ => 0

private theorem watching_run {p c n : Nat} (v : Fin n) (d : Nat)
    (a : Nat × EarlyState p c n) (b : Nat × Obs p c n) (w : List (Fin n)) :
    GGTiming.runMarks (watchNext v d) (.watching a b) w =
      .watching (GGTiming.runMarks (clockNext (earlyNext v d)) a w)
        (GGTiming.runMarks (clockNext (advance v)) b w) := by
  induction w generalizing a b with
  | nil => rfl
  | cons e w ih => exact ih _ _

theorem attributed_credit {p c n : Nat} (hn : 4≤n) (v : Fin n) (d : Nat)
    (s : Obs p c n) (w : List (Fin n)) (hs : Protected v s) (hc : COV s.config)
    (h : Attributed v d s w) :
    let z := GGTiming.runMarks (watchNext v d) (watchStart v d s) w
    1≤earlyCredit z + lateCredit d z := by
  classical
  induction h with
  | @entry s w hh hW =>
    subst d
    let cap := 2*n*(c*(s.donor+1))
    rw [show watchStart v s.donor s = .watching (cap,earlyStart v s.donor s.config) (cap,s) by simp [watchStart,cap]]
    rw [watching_run]
    exact failsHere_cylinder_cover v s hs.1 w _ hW
  | @before s t e w hh hhT hW ih =>
    have hP := firstGap_step hn v s t e hs hc hhT
    have hEq : watchNext v d (watchStart v d s) e = watchStart v d t := by
      have hw : watchStart v d s = Watch.waiting s := by simp only [watchStart,if_neg (Nat.ne_of_lt hh)]
      rw [hw,waiting_eq,hhT]
      rfl
    simp only [GGTiming.runMarks,hEq]
    exact ih hP.2.1 hP.2.2.1

private theorem never_run {p c n : Nat} (v : Fin n) (d : Nat) (w : List (Fin n)) :
    GGTiming.runMarks (watchNext (p:=p) (c:=c) v d) .never w=.never := by
  induction w with
  | nil => rfl
  | cons e w ih => exact ih

/-- Conditional only on the actual fresh epoch boundary, not on any
citation or scheduler event. The gap witness is unique from Phase.failed. -/
theorem watch_budget {p c n : Nat} (hn : 4≤n) (hc : 12≤c) (v : Fin n)
    (d t : Nat) (s : Obs p c n) (hs : Protected v s) (hC : COV s.config)
    (hInit : s.donor=d → freshInit s.config v d) :
    256^(d+1)*endpointSum (watchNext v d) earlyCredit t (watchStart v d s)≤n^t ∧
    256^(d+1)*endpointSum (watchNext v d) (lateCredit d) t (watchStart v d s)≤n^t := by
  classical
  induction t generalizing s with
  | zero =>
    by_cases he : s.donor=d
    · have h := hInit he
      subst d
      have hE := early_cylinder_bound hn hc v s hs.1 h 0
      have hL := late_cylinder_bound hn hc v s hs.1 0
      have hLP := Nat.le_trans (Nat.mul_le_mul_right _ (show 256^(s.donor+1)≤2048^(s.donor+1) by exact Nat.pow_le_pow_left (by decide) _)) hL
      exact ⟨by simpa [watchStart,endpointSum,earlyCredit] using hE,
        by simpa [watchStart,endpointSum,lateCredit] using hLP⟩
    · simp [watchStart,he,endpointSum,earlyCredit,lateCredit]
  | succ t ih =>
    by_cases he : s.donor=d
    · have h := hInit he
      subst d
      simp only [watchStart,if_true]
      let cap := 2*n*(c*(s.donor+1))
      constructor
      · have hh := endpoint_le_words (watchNext v s.donor) (clockNext (earlyNext v s.donor))
          earlyCredit (fun a => earlyScore a.2) (t+1)
          (.watching (cap,earlyStart v s.donor s.config) (cap,s))
          (cap,earlyStart v s.donor s.config)
          (by intro w _; rw [watching_run]; exact Nat.le_refl _)
        exact Nat.le_trans (Nat.mul_le_mul_left _ hh) (early_cylinder_bound hn hc v s hs.1 h _)
      · have hh := endpoint_le_words (watchNext v s.donor) (clockNext (advance v))
          (lateCredit s.donor)
          (fun a => if a.1=0 then FreshPaymentMass.unpaidIndicator s.donor a.2 else 0) (t+1)
          (.watching (cap,earlyStart v s.donor s.config) (cap,s)) (cap,s)
          (by intro w _; rw [watching_run]; exact Nat.le_refl _)
        have hL := Nat.le_trans (Nat.mul_le_mul_left _ hh) (late_cylinder_bound hn hc v s hs.1 _)
        exact Nat.le_trans (Nat.mul_le_mul_right _ (show 256^(s.donor+1)≤2048^(s.donor+1) by exact Nat.pow_le_pow_left (by decide) _)) hL
    · have hEach (e : Fin n) :
          256^(d+1)*endpointSum (watchNext v d) earlyCredit t (watchNext v d (.waiting s) e)≤n^t ∧
          256^(d+1)*endpointSum (watchNext v d) (lateCredit d) t
            (watchNext v d (.waiting s) e)≤n^t := by
        rw [waiting_eq]
        cases hN : freshNext v (.live s) e with
        | live u =>
          have hr := firstGap_step hn v s u e hs hC hN
          have hi (hh : u.donor=d) : freshInit u.config v d := by
            rw [←hh]
            exact hr.2.2.2 (by omega)
          exact ih u hr.2.1 hr.2.2.1 hi
        | retired | failed =>
          have hE := run_length (watchNext (p:=p) (c:=c) v d) earlyCredit .never t 0
            (by intro w _; rw [never_run]; rfl)
          have hL := run_length (watchNext (p:=p) (c:=c) v d) (lateCredit d) .never t 0
            (by intro w _; rw [never_run]; rfl)
          simp only [watchPhase,hE,hL,Nat.zero_mul,Nat.mul_zero,Nat.zero_le,and_self]
      have hw : watchStart v d s = Watch.waiting s := by simp only [watchStart,if_neg he]
      rw [hw]
      simp only [endpointSum,←s_scale]
      rw [show n^(t+1)=sumEdge (fun _ : Fin n => n^t) by rw [s_const,Nat.pow_succ,Nat.mul_comm]]
      exact ⟨s_mono (fun e => (hEach e).1),s_mono (fun e => (hEach e).2)⟩


theorem attributed_cap {p c n : Nat} (hn : 4≤n) (v : Fin n) (d : Nat)
    (s : Obs p c n) (w : List (Fin n)) (hs : Protected v s) (hc : COV s.config)
    (h : Attributed v d s w) : d+1<n := by
  induction h with
  | entry hd _ => rw [←hd]; exact hs.1.2.2.2.2.2
  | before _ hN _ ih =>
    have hh := firstGap_step hn v _ _ _ hs hc hN
    exact ih hh.2.1 hh.2.2.1

private theorem push_run {n : Nat} (x w : List (Fin n)) :
    GGTiming.runMarks FreshCountHits.pushMark x w=x++w := by
  induction w generalizing x with
  | nil => simp [GGTiming.runMarks]
  | cons e w ih => simp [GGTiming.runMarks,FreshCountHits.pushMark,ih,List.append_assoc]

open Classical in
/-- Sticky failure bound from a literal fresh start. This bound is valid
for every raw-mark horizon including horizons shorter than a cutoff. -/
theorem fresh_failure_mass {p c n : Nat} (hn : 4≤n) (hc : 12≤c)
    (v : Fin n) (s : Obs p c n) (hs : Protected v s) (hC : COV s.config)
    (hI : freshInit s.config v s.donor) (t : Nat) :
    1000*endpointSum (freshNext v) (fun z => if Failure z then 1 else 0) t (.live s)
       ≤11*n^t := by
  classical
  let fail (w : List (Fin n)) := Failure (GGTiming.runMarks (freshNext v) (.live s) w)
  let early (h : Nat) (w : List (Fin n)) :=
    earlyCredit (GGTiming.runMarks (watchNext v (h-1)) (watchStart v (h-1) s) w)
  let late (h : Nat) (w : List (Fin n)) :=
    lateCredit (h-1) (GGTiming.runMarks (watchNext v (h-1)) (watchStart v (h-1) s) w)
  have credit (w : List (Fin n)) (_ : True) (hf : fail w) :
      ∃ h, 0<h ∧ h≤n ∧ 1≤early h w+late h w := by
    unfold fail at hf
    cases hh : GGTiming.runMarks (freshNext v) (.live s) w with
    | live | retired => rw [hh] at hf; exact False.elim hf
    | failed d =>
      have hA := attribution_exact hn v s w d hs hC hh
      have hB := attributed_cap hn v d s w hs hC hA
      refine ⟨d+1,by omega,by omega,?_⟩
      exact attributed_credit hn v d s w hs hC hA
  have E (h : Nat) (hh : 0<h) (_ : h≤n) :
      256^h*endpointSum FreshCountHits.pushMark (early h) t []≤n^t := by
    have hh' : h-1+1=h := by omega
    have hW := (watch_budget hn hc v (h-1) t s hs hC (fun he => he ▸ hI)).1
    rw [hh'] at hW
    apply Nat.le_trans (Nat.mul_le_mul_left _ ?_) hW
    apply endpoint_le_words
    intro w _
    simp only [early,push_run,List.nil_append,Nat.le_refl]
  have L (h : Nat) (hh : 0<h) (_ : h≤n) :
      256^h*endpointSum FreshCountHits.pushMark (late h) t []≤n^t := by
    have hh' : h-1+1=h := by omega
    have hW := (watch_budget hn hc v (h-1) t s hs hC (fun he => he ▸ hI)).2
    rw [hh'] at hW
    apply Nat.le_trans (Nat.mul_le_mul_left _ ?_) hW
    apply endpoint_le_words
    intro w _
    simp only [late,push_run,List.nil_append,Nat.le_refl]
  have hz := FreshFailureMass.failure_mass_of_gap_partition FreshCountHits.pushMark
    [] t n (fun z => if fail z then 1 else 0) early late (fun _ => True) trivial
    (fun _ _ _ => trivial)
    (fun w hw => FreshFailureMass.attributed_failure_le_gap_sum fail early late n w (credit w hw))
    E L
  apply Nat.le_trans (Nat.mul_le_mul_left _ ?_) hz
  apply endpoint_le_words
  intro w _
  simp only [fail,push_run,List.nil_append,Nat.le_refl]


def Done {p c n : Nat} : Phase p c n → Prop
  | .live _ => False
  | _ => True

theorem retirement_stops {p c n : Nat} (v e : Fin n) (s : Obs p c n)
    (hR : RankPhysical.retirement s.config e=true) : (advance v s e).stopped=true := by
  have hR' : (geometricPay (s.config e) (s.config (rightNeighbor e)) &&
      (s.config (rightNeighbor e)).mark)=true := hR
  cases hs : s.stopped
  · simp only [advance,hs,Bool.false_eq_true,if_false,stop,hR',Bool.true_or,if_true]
  · simp [advance,hs]

theorem done_iff_stop {p c n : Nat} (v e : Fin n) (s : Obs p c n) :
    Done (freshNext v (.live s) e) ↔ (advance v s e).stopped=true := by
  by_cases hr : RankPhysical.retirement s.config e=true
  · simp only [freshNext,if_pos hr,Done,retirement_stops v e s hr]
  · cases hs : (advance v s e).stopped <;> simp [freshNext,hr,hs,Done]

theorem live_step_eq {p c n : Nat} (v e : Fin n) (s : Obs p c n)
    (h : (advance v s e).stopped=false) :
    freshNext v (.live s) e=.live (advance v s e) := by
  have hR : ¬RankPhysical.retirement s.config e=true := by
    intro hR; rw [retirement_stops v e s hR] at h; contradiction
  simp [freshNext,hR,h]

theorem cost_eq {p c n : Nat} (v : Fin n) (s : Obs p c n) (hs : s.stopped=false)
    (t : Nat) :
    iidHitCost (freshNext v) Done t (.live s) =
      iidHitCost (advance v) (fun z => z.stopped=true) t s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    have he : ¬ Done (.live s) := fun h => h
    rw [iidHitCost,iidHitCost,if_neg he,if_neg (by rw [hs]; decide)]
    congr 1
    apply congrArg List.sum
    apply congrArg List.ofFn
    funext e
    cases hS : (advance v s e).stopped
    · rw [live_step_eq v e s hS]
      exact ih (advance v s e) hS
    · rw [iidHitCost_of_target _ _ _ ((done_iff_stop v e s).mpr hS)]
      exact (iidHitCost_of_target (advance v) (fun z => z.stopped=true) (advance v s e) hS t).symm

theorem fresh_mean_of_fixed {p c n : Nat} (v : Fin n) (s : Obs p c n) (hs : s.stopped=false)
    (K : Nat)
    (hm : IIDExpectedHittingTimeAtMost (advance v) (fun z => z.stopped=true) s K) :
    IIDExpectedHittingTimeAtMost (freshNext v) Done (.live s) K := by
  intro t
  rw [cost_eq v s hs]
  exact hm t

end L4.FreshFailure

#print axioms L4.FreshFailure.attribution_exact
#print axioms L4.FreshFailure.attributed_credit
#print axioms L4.FreshFailure.watch_budget
#print axioms L4.FreshFailure.fresh_failure_mass
#print axioms L4.FreshFailure.fresh_mean_of_fixed
