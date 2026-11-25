import Leader.L4.FastClockPath

/-! Exact atomic word-centre projection of the signed and biased
rows. This does not assert the packed transport refines the atomic
centre model; that is a separate custody/compiler theorem. -/
namespace L4.UnisonRows

structure Clock where
  err : Bool
  value : Int
  deriving DecidableEq, Repr

inductive Action where
  | reset | propagate | clear | inc | hold
  deriving DecidableEq, Repr

def Valid (P : Int) (x : Clock) : Prop :=
  -P ≤ x.value ∧ x.value < P ∧ (x.err = true → x.value < 0)

def succ (P c : Int) : Int := if c=P-1 then 0 else c+1

def lowerGap (P a b : Int) : Bool :=
  decide (a+2 ≤ b ∧ ¬(a=0 ∧ b=P-1))

def lowerError (x y : Clock) : Bool := y.err && decide (y.value < x.value)

def root (P : Int) (l x r : Clock) : Bool :=
  if x.err then !(lowerError x l || lowerError x r)
  else lowerGap P x.value l.value || lowerGap P x.value r.value

def base (P : Int) (x : Clock) : Bool := x.err && decide (x.value = -P)

def suggestion (x y : Clock) : Int :=
  if y.err && decide (y.value+1<0) then min x.value (y.value+1) else x.value

def propValue (l x r : Clock) : Int := min (suggestion x l) (suggestion x r)

def near (a b : Int) : Bool := decide (a≤b+1 ∧ b≤a+1)

def clearOK (x y : Clock) : Bool :=
  near x.value y.value && (decide (y.value≤x.value) || !y.err)

def incOK (P : Int) (x y : Clock) : Bool :=
  decide (y.value=x.value ∨ y.value=succ P x.value)

def signedRow (P : Int) (l x r : Clock) : Action × Clock :=
  if root P l x r && !base P x then (.reset, ⟨true,-P⟩)
  else if propValue l x r < x.value then (.propagate,⟨true,propValue l x r⟩)
  else if x.err && clearOK x l && clearOK x r then (.clear,⟨false,x.value⟩)
  else if !x.err && incOK P x l && incOK P x r then (.inc,⟨false,succ P x.value⟩)
  else (.hold,x)

def act (P : Int) (l x r : Clock) : Action := (signedRow P l x r).1
def poll (P : Int) (l x r : Clock) : Clock := (signedRow P l x r).2

def bias (P : Int) (x : Clock) : Clock := ⟨x.err,x.value+P⟩

def normalizeBiased (P : Int) (x : Clock) : Clock :=
  if x.err && decide (P ≤ x.value) then ⟨true,0⟩ else x

def biasedSucc (P t : Int) : Int := if t=2*P-1 then P else t+1

def biasedLowerGap (P a b : Int) : Bool :=
  decide (a<b ∧ a+1<b ∧ ¬(a=P ∧ b=2*P-1))

def biasedRoot (P : Int) (l x r : Clock) : Bool :=
  if x.err then !(lowerError x l || lowerError x r)
  else biasedLowerGap P x.value l.value || biasedLowerGap P x.value r.value

def biasedSuggestion (P : Int) (x y : Clock) : Int :=
  if y.err && decide (y.value<P-1) && decide (y.value+1<x.value) then y.value+1 else x.value

def biasedProp (P : Int) (l x r : Clock) : Int :=
  min (biasedSuggestion P x l) (biasedSuggestion P x r)

def biasedNear (a b : Int) : Bool :=
  decide (a=b ∨ (a<b ∧ a+1=b) ∨ (b<a ∧ b+1=a))

def biasedClearOK (x y : Clock) : Bool :=
  biasedNear x.value y.value && (decide (y.value≤x.value) || !y.err)

def biasedIncOK (P : Int) (x y : Clock) : Bool :=
  decide (y.value=x.value ∨ y.value=biasedSucc P x.value)

def biasedRow (P : Int) (l x r : Clock) : Action × Clock :=
  if biasedRoot P l x r && !(x.err && decide (x.value=0)) then (.reset,⟨true,0⟩)
  else if biasedProp P l x r < x.value then (.propagate,⟨true,biasedProp P l x r⟩)
  else if x.err && biasedClearOK x l && biasedClearOK x r then (.clear,⟨false,x.value⟩)
  else if !x.err && biasedIncOK P x l && biasedIncOK P x r then (.inc,⟨false,biasedSucc P x.value⟩)
  else (.hold,x)

private theorem bool_guard {a b : Bool} (h : (a=true ↔ b=true)) : a=b := by
  cases a <;> cases b <;> simp_all

private theorem succ_bias (P c : Int) : biasedSucc P (c+P) = succ P c+P := by
  have h : c+P=2*P-1 ↔ c=P-1 := by omega
  simp [biasedSucc,succ,h]
  split <;> omega

private theorem root_bias (P : Int) (l x r : Clock) :
    biasedRoot P (bias P l) (bias P x) (bias P r) = root P l x r := by
  have he (y : Clock) : lowerError (bias P x) (bias P y) = lowerError x y := by
    have hh : y.value+P < x.value+P ↔ y.value < x.value := by omega
    simp [lowerError,bias,hh]
  have hg (y : Clock) : biasedLowerGap P (x.value+P) (y.value+P) = lowerGap P x.value y.value := by
    apply bool_guard
    simp only [biasedLowerGap,lowerGap,decide_eq_true_eq]
    omega
  unfold biasedRoot root
  change (if x.err then _ else _) = (if x.err then _ else _)
  split
  · rw [he,he]
  · simp only [bias,hg]

private theorem sugg_bias (P : Int) (x y : Clock) :
    biasedSuggestion P (bias P x) (bias P y) = suggestion x y+P := by
  have hn : y.value+P<P-1 ↔ y.value+1<0 := by omega
  have hl : y.value+P+1<x.value+P ↔ y.value+1<x.value := by omega
  simp only [biasedSuggestion,suggestion,bias,hn,hl]
  by_cases he : y.err = true <;> by_cases hh : y.value+1<0 <;>
    by_cases hz : y.value+1<x.value <;> simp [he,hh,hz] <;> omega

private theorem prop_bias (P : Int) (l x r : Clock) :
    biasedProp P (bias P l) (bias P x) (bias P r) = propValue l x r+P := by
  unfold biasedProp propValue
  rw [sugg_bias,sugg_bias]
  omega

private theorem clear_bias (P : Int) (x y : Clock) :
    biasedClearOK (bias P x) (bias P y) = clearOK x y := by
  have hn : biasedNear (x.value+P) (y.value+P)=near x.value y.value := by
    apply bool_guard
    simp only [biasedNear,near,decide_eq_true_eq]
    omega
  have ho : y.value+P≤x.value+P ↔ y.value≤x.value := by omega
  simp [biasedClearOK,clearOK,bias,hn,ho]

private theorem inc_bias (P : Int) (x y : Clock) :
    biasedIncOK P (bias P x) (bias P y) = incOK P x y := by
  apply bool_guard
  simp only [biasedIncOK,incOK,bias,decide_eq_true_eq,succ_bias]
  omega

/-- Stronger than the fixed-period executable miter: exact row and post
clock agree on every input triple under signed-to-biased translation.
Validity is needed only for interpreting a bounded bit record. -/
theorem biased_signed_commutes (P : Int) (l x r : Clock) :
    biasedRow P (bias P l) (bias P x) (bias P r) =
      ((signedRow P l x r).1,bias P (signedRow P l x r).2) := by
  have hb : (x.err && decide ((bias P x).value=0)) = base P x := by
    have h : x.value+P=0 ↔ x.value = -P := by omega
    simp [bias,base,h]
  have he : (bias P x).err=x.err := rfl
  have hp : propValue l x r+P < (bias P x).value ↔ propValue l x r < x.value := by
    change propValue l x r+P < x.value+P ↔ propValue l x r < x.value
    omega
  have hs : biasedSucc P (bias P x).value = succ P x.value+P := succ_bias P _
  simp only [biasedRow,signedRow,root_bias,prop_bias,clear_bias,inc_bias,hb,hp,he,hs]
  split <;> (try split) <;> (try split) <;> (try split)
  all_goals simp [bias] <;> omega

def decodeBiased (P : Int) (x : Clock) : Clock :=
  ⟨x.err,(normalizeBiased P x).value-P⟩

theorem decodeBiased_valid (P : Int) (x : Clock) (hP : 0<P)
    (hx : 0≤x.value ∧ x.value<2*P) : Valid P (decodeBiased P x) := by
  cases he : x.err <;> by_cases hv : P≤x.value <;>
    simp [decodeBiased,normalizeBiased,he,hv,Valid] <;> omega

theorem normalize_is_bias_decode (P : Int) (x : Clock) :
    normalizeBiased P x = bias P (decodeBiased P x) := by
  rcases x with ⟨e,t⟩
  cases e <;> by_cases hv : P≤t <;>
    simp [decodeBiased,normalizeBiased,hv,bias] <;> omega

abbrev Correct (x : Clock) : Prop := x.err = false

def Adjacent (P a b : Int) : Prop := a=b ∨ succ P a=b ∨ succ P b=a

private theorem adjacent_no_lower (P a b : Int) (hP : 0<P) (h : Adjacent P a b) :
    lowerGap P a b = false := by
  unfold lowerGap
  apply decide_eq_false
  intro ⟨hd,hwrap⟩
  rcases h with h | h | h
  · omega
  · unfold succ at h
    split at h <;> omega
  · unfold succ at h
    split at h
    · exact hwrap ⟨h.symm,by assumption⟩
    · omega

private theorem suggestion_same (x y : Clock) (hy : Correct y) :
    suggestion x y = x.value := by simp [suggestion,hy]

private theorem valid_suggestion (P : Int) (x y : Clock) (hx : Valid P x) (hy : Valid P y) :
    -P ≤ suggestion x y ∧ suggestion x y ≤ x.value ∧
      (suggestion x y < x.value → suggestion x y < 0) := by
  unfold suggestion
  split
  · rename_i h
    have hh := (Bool.and_eq_true_iff.mp h).2
    have hf : y.value+1 < 0 := of_decide_eq_true hh
    have hl := hx.1
    have hr := hy.1
    omega
  · have hl := hx.1; omega

theorem poll_valid (P : Int) (l x r : Clock) (hP : 0<P)
    (hl : Valid P l) (hx : Valid P x) (hr : Valid P r) :
    Valid P (poll P l x r) := by
  have hProp : -P ≤ propValue l x r ∧ propValue l x r ≤ x.value ∧
      (propValue l x r < x.value → propValue l x r < 0) := by
    have hL := valid_suggestion P x l hx hl
    have hR := valid_suggestion P x r hx hr
    unfold propValue
    omega
  have hi : Valid P ⟨false,succ P x.value⟩ := by
    unfold succ
    have h1 := hx.1
    have h2 := hx.2.1
    split <;> simp [Valid] <;> omega
  unfold poll signedRow
  split
  · simp [Valid]; omega
  · split
    · rename_i h
      have hb := hx.2.1
      have hg := hProp.2.2 h
      simp only [Valid]
      omega
    · split
      · simp [Valid,hx.1,hx.2.1]
      · split
        · exact hi
        · exact hx

/-- Legitimate, correct neighbors do not enable RESET/PROP/CLEAR. An
atomic service either holds or increments, and both incident seams
remain adjacent. Current-vs-previous payload handling is separate. -/
theorem LEG_poll (P : Int) (l x r : Clock) (hP : 0<P)
    (hl : Correct l) (hx : Correct x) (hr : Correct r)
    (hL : Adjacent P x.value l.value) (hR : Adjacent P x.value r.value) :
    Correct (poll P l x r) ∧
    Adjacent P (poll P l x r).value l.value ∧
    Adjacent P (poll P l x r).value r.value ∧
    (act P l x r = .inc ∨ act P l x r = .hold) := by
  have hRoot : root P l x r = false := by
    simp [root,Correct] at hx ⊢
    simp [hx,adjacent_no_lower P _ _ hP hL,adjacent_no_lower P _ _ hP hR]
  have hProp : propValue l x r = x.value := by
    simp [propValue,suggestion_same x l hl,suggestion_same x r hr]
  have he : x.err=false := hx
  unfold act poll signedRow
  simp only [hRoot,Bool.false_and,Bool.false_eq_true,if_false,hProp,Int.lt_irrefl,
    he,Bool.not_false,Bool.true_and]
  split
  · rename_i h
    obtain ⟨hl',hr'⟩ := Bool.and_eq_true_iff.mp h
    have aL : l.value=x.value ∨ l.value=succ P x.value := of_decide_eq_true hl'
    have aR : r.value=x.value ∨ r.value=succ P x.value := of_decide_eq_true hr'
    refine ⟨rfl,?_ ,?_ ,.inl rfl⟩
    · rcases aL with h|h
      · exact .inr (.inr (congrArg (succ P) h))
      · exact .inl h.symm
    · rcases aR with h|h
      · exact .inr (.inr (congrArg (succ P) h))
      · exact .inl h.symm
  · exact ⟨hx,hL,hR,.inr rfl⟩

/-- For the Q round: an activation at a nonbase root resets it. -/
theorem nonbase_root_reset (P : Int) (l x r : Clock)
    (h : root P l x r=true) (hb : base P x=false) :
    act P l x r = .reset ∧ poll P l x r = ⟨true,-P⟩ := by
  simp [act,poll,signedRow,h,hb]

/-- Existing error stays nonincreasing in value until it clears. -/
theorem error_poll_nonincrease (P : Int) (l x r : Clock) (_hP : 0<P)
    (hx : Valid P x) (he : x.err=true) :
    (poll P l x r).value ≤ x.value := by
  unfold poll signedRow
  split
  · exact hx.1
  · split
    · exact Int.le_of_lt (by assumption)
    · split
      · exact Int.le_refl _
      · simp [he]

/-- A larger erroneous neighbor prevents the smaller error from clearing.
This is the germ of persistence of the witness to a nonroot error. -/
theorem error_cannot_clear_with_larger_error (P : Int) (l x r : Clock)
    (he : x.err=true)
    (h : (l.err=true ∧ x.value<l.value) ∨ (r.err=true ∧ x.value<r.value)) :
    (poll P l x r).err=true := by
  have hc : (x.err && clearOK x l && clearOK x r)=false := by
    rcases h with ⟨hE,hV⟩ | ⟨hE,hV⟩
    · have hb : ¬l.value≤x.value := by omega
      simp [clearOK,he,hE,hb]
    · have hb : ¬r.value≤x.value := by omega
      simp [clearOK,he,hE,hb]
  unfold poll signedRow
  split
  · rfl
  · split
    · rfl
    · rw [hc]
      simp [he]

/-- Literal counterexample to the *typed* phrase “no new error root”:
resetting an old correct root creates an error root at the same
physical centre. It is already a base, so Q can use nonbase roots. -/
theorem reset_creates_error_root_at_old_root :
    let L : Clock := ⟨false,0⟩
    let X : Clock := ⟨false,0⟩
    let R : Clock := ⟨false,2⟩
    X.err=false ∧ root 4 L X R=true ∧
    (poll 4 L X R).err=true ∧ base 4 (poll 4 L X R)=true ∧
    root 4 L (poll 4 L X R) R=true := by decide

private theorem suggestion_lt {x y : Clock} (h : suggestion x y < x.value) :
    y.err=true ∧ suggestion x y=y.value+1 ∧ suggestion x y<0 := by
  unfold suggestion at h ⊢
  split at h
  · rename_i he
    have hh := Bool.and_eq_true_iff.mp he
    have hN : y.value+1<0 := of_decide_eq_true hh.2
    have hlt : y.value+1 < x.value := by omega
    have hem : min x.value (y.value+1) = y.value+1 := by omega
    rw [if_pos he,hem]
    exact ⟨hh.1,rfl,hN⟩
  · exact False.elim ((Int.lt_irrefl _) h)

private theorem prop_witness {l x r : Clock} (h : propValue l x r < x.value) :
    ∃ y, (y=l ∨ y=r) ∧ y.err=true ∧ propValue l x r=y.value+1 ∧ propValue l x r<0 := by
  by_cases he : suggestion x l ≤ suggestion x r
  · have hVal : propValue l x r = suggestion x l := by unfold propValue; omega
    have hh := suggestion_lt (by simpa [hVal] using h : suggestion x l < x.value)
    exact ⟨l,.inl rfl,hh.1,hVal.trans hh.2.1,hVal ▸ hh.2.2⟩
  · have hVal : propValue l x r = suggestion x r := by unfold propValue; omega
    have hh := suggestion_lt (by simpa [hVal] using h : suggestion x r < x.value)
    exact ⟨r,.inr rfl,hh.1,hVal.trans hh.2.1,hVal ▸ hh.2.2⟩

/-- Exactly the useful old-state premises retained from case splitting
the priority row. Each rule supplies only its own claimed effects. -/
inductive PollFacts (P : Int) (l x r : Clock) : Clock → Prop where
  | reset : root P l x r = true → base P x = false → PollFacts P l x r ⟨true,-P⟩
  | propagate (v : Int) :
      v < x.value → v < 0 →
      (∃ y, (y=l ∨ y=r) ∧ y.err=true ∧ v=y.value+1) → PollFacts P l x r ⟨true,v⟩
  | clear : x.err=true → clearOK x l=true → clearOK x r=true → PollFacts P l x r ⟨false,x.value⟩
  | inc : x.err=false → incOK P x l=true → incOK P x r=true → PollFacts P l x r ⟨false,succ P x.value⟩
  | hold : PollFacts P l x r x

theorem poll_facts (P : Int) (l x r : Clock) : PollFacts P l x r (poll P l x r) := by
  unfold poll signedRow
  split
  · rename_i h
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
    exact .reset a (by cases h : base P x <;> simp_all)
  · split
    · rename_i h
      obtain ⟨y,hy,he,hv,ht⟩ := prop_witness h
      exact .propagate _ h ht ⟨y,hy,he,hv⟩
    · split
      · rename_i h
        have hh := Bool.and_eq_true_iff.mp h
        exact .clear (Bool.and_eq_true_iff.mp hh.1).1 (Bool.and_eq_true_iff.mp hh.1).2 hh.2
      · split
        · rename_i h
          have hh := Bool.and_eq_true_iff.mp h
          exact .inc (by have h := (Bool.and_eq_true_iff.mp hh.1).1; cases hX : x.err <;> simp_all)
            (Bool.and_eq_true_iff.mp hh.1).2 hh.2
        · exact .hold

private theorem gap_of_close (P a b : Int) (h : near a b = true) : lowerGap P a b=false := by
  unfold near at h
  have he := of_decide_eq_true h
  unfold lowerGap
  apply decide_eq_false
  omega

private theorem after_inc_adj {P : Int} {x y : Clock} (h : incOK P x y=true) :
    Adjacent P (succ P x.value) y.value := by
  unfold incOK at h
  rcases of_decide_eq_true h with h | h
  · exact .inr (.inr (congrArg (succ P) h))
  · exact .inl h.symm

/-- Q uses no *new nonbase root*; an old correct root may convert into
a base error root, as recorded by the explicit counter-witness. -/
theorem centre_no_new_nonbase_root (P : Int) (l x r : Clock) (hP : 0<P)
    (hQ : root P l x r = true → base P x = true) :
    root P l (poll P l x r) r = true → base P (poll P l x r) = true := by
  generalize hh : poll P l x r = y
  have ho : PollFacts P l x r y := hh ▸ poll_facts P l x r
  intro hNew
  cases ho with
  | reset _ _ => simp [base]
  | propagate v hlt hn hw =>
    obtain ⟨z,hz,he,hv⟩ := hw
    rcases hz with rfl | rfl
    · have hs : z.value < v := by omega
      simp [root,lowerError,he,hs] at hNew
    · have hs : z.value < v := by omega
      simp [root,lowerError,he,hs] at hNew
  | clear he hL hR =>
    have h1 := gap_of_close P _ _ (Bool.and_eq_true_iff.mp hL).1
    have h2 := gap_of_close P _ _ (Bool.and_eq_true_iff.mp hR).1
    simp [root,h1,h2] at hNew
  | inc he hL hR =>
    have h1 := adjacent_no_lower P _ _ hP (after_inc_adj hL)
    have h2 := adjacent_no_lower P _ _ hP (after_inc_adj hR)
    simp [root,h1,h2] at hNew
  | hold => exact hQ hNew

private theorem no_new_correct_lower_gap (P : Int) (x l y r : Clock) (hP : 0<P)
    (hx : Valid P x) (hn : x=l ∨ x=r) (hG : lowerGap P x.value y.value=false) :
    lowerGap P x.value (poll P l y r).value=false := by
  generalize hh : poll P l y r = z
  have hf : PollFacts P l y r z := hh ▸ poll_facts P l y r
  cases hf with
  | reset hb hr =>
    unfold lowerGap
    apply decide_eq_false
    change ¬ (x.value+2 ≤ -P ∧ ¬ (x.value=0 ∧ -P=P-1))
    have h := hx.1
    omega
  | propagate v hv hneg _ =>
    unfold lowerGap at hG ⊢
    apply decide_eq_false
    intro hNew
    change v ≥ x.value+2 ∧ ¬(x.value=0 ∧ v=P-1) at hNew
    have hOld : x.value+2≤y.value ∧ ¬(x.value=0 ∧ y.value=P-1) := by omega
    have ht := decide_eq_true hOld
    rw [hG] at ht
    cases ht
  | clear _ _ _ => exact hG
  | inc _ hL hR =>
    have hA : Adjacent P (succ P y.value) x.value := by
      rcases hn with rfl | rfl
      · exact after_inc_adj hL
      · exact after_inc_adj hR
    have hA' : Adjacent P x.value (succ P y.value) := by
      rcases hA with h|h|h
      · exact .inl h.symm
      · exact .inr (.inr h)
      · exact .inr (.inl h)
    exact adjacent_no_lower P _ _ hP hA'
  | hold => exact hG

private theorem lower_error_survives (P : Int) (x l y r : Clock) (hP : 0<P)
    (hy : Valid P y) (he : x.err=true) (hn : x=l ∨ x=r) (h : lowerError x y=true) :
    lowerError x (poll P l y r)=true := by
  unfold lowerError at h ⊢
  obtain ⟨he',hval⟩ := Bool.and_eq_true_iff.mp h
  have hLt : y.value < x.value := of_decide_eq_true hval
  have hE := error_cannot_clear_with_larger_error P l y r he' (by
    rcases hn with rfl | rfl
    · exact .inl ⟨he,hLt⟩
    · exact .inr ⟨he,hLt⟩)
  have hNon := error_poll_nonincrease P l y r hP hy he'
  exact Bool.and_eq_true_iff.mpr ⟨hE,decide_eq_true (by omega)⟩

private theorem root_symm (P : Int) (l x r : Clock) :
    root P l x r = root P r x l := by
  unfold root
  simp only [Bool.or_comm]

/-- An old nonroot stays a nonroot if its *left neighbour* is polled.
The right neighbour is fixed. New erroneous type at the changing
site does not invalidate the smaller-error witness of an existing error. -/
theorem left_poll_preserves_nonroot (P : Int) (ll l x r : Clock)
    (hP : 0<P) (hl : Valid P l) (hx : Valid P x) (h : root P l x r=false) :
    root P (poll P ll l x) x r=false := by
  cases he : x.err
  · have hOld : lowerGap P x.value l.value=false ∧ lowerGap P x.value r.value=false := by
      simpa [root,he,Bool.or_eq_false_iff] using h
    have hn := no_new_correct_lower_gap P x ll l x hP hx (.inr rfl) hOld.1
    simp [root,he,hn,hOld.2]
  · have hOld : lowerError x l=true ∨ lowerError x r=true := by
      simp only [root,he,if_true] at h
      cases hL : lowerError x l <;> cases hR : lowerError x r <;> simp_all
    rcases hOld with hL | hR
    · have hn := lower_error_survives P x ll l x hP hl he (.inr rfl) hL
      simp [root,he,hn]
    · simp [root,he,hR]

private theorem poll_symm (P : Int) (l x r : Clock) :
    poll P l x r = poll P r x l := by
  have hP : propValue l x r = propValue r x l := by unfold propValue; omega
  have hC : (x.err && clearOK x l && clearOK x r) = (x.err && clearOK x r && clearOK x l) := by
    rw [Bool.and_assoc,Bool.and_assoc,Bool.and_comm (clearOK x l) (clearOK x r)]
  have hI : (!x.err && incOK P x l && incOK P x r) = (!x.err && incOK P x r && incOK P x l) := by
    rw [Bool.and_assoc,Bool.and_assoc,Bool.and_comm (incOK P x l) (incOK P x r)]
  unfold poll signedRow
  rw [root_symm P l x r,hP,hC,hI]

theorem right_poll_preserves_nonroot (P : Int) (l x r rr : Clock)
    (hP : 0<P) (hr : Valid P r) (hx : Valid P x) (h : root P l x r=false) :
    root P l x (poll P x r rr)=false := by
  rw [root_symm,poll_symm P x r rr]
  exact left_poll_preserves_nonroot P rr r x l hP hr hx ((root_symm P l x r).symm.trans h)

/-- Touching a centre suffices to establish its Q predicate. The
nonbase-root case is an actual priority RESET, not a possible HOLD. -/
theorem centre_poll_establishes_Q (P : Int) (l x r : Clock) (hP : 0<P) :
    root P l (poll P l x r) r=true → base P (poll P l x r)=true := by
  by_cases hQ : root P l x r=true → base P x=true
  · exact centre_no_new_nonbase_root P l x r hP hQ
  · have hR : root P l x r=true := by
      cases h : root P l x r <;> simp_all
    have hB : base P x=false := by
      cases h : base P x <;> simp_all
    rw [(nonbase_root_reset P l x r hR hB).2]
    simp [base]

/-- Once a cell's value is at most one above an adjacent error, its own
poll preserves this ceiling while that neighbour remains fixed. INC
checks this same neighbour even when it is erroneous. -/
theorem poll_keeps_error_ceiling (P : Int) (l x r u : Clock) (hP : 0<P)
    (hu : Valid P u) (hE : u.err=true) (hNear : u=l ∨ u=r)
    (hBelow : x.value≤u.value+1) :
    (poll P l x r).value≤u.value+1 := by
  generalize hh : poll P l x r = y
  have h := hh ▸ poll_facts P l x r
  cases h with
  | reset _ _ =>
    change -P≤u.value+1
    have H := hu.1
    omega
  | propagate v hv _ _ =>
    change v≤u.value+1
    omega
  | clear _ _ _ => exact hBelow
  | inc _ hl hr =>
    have hI : incOK P x u=true := by
      rcases hNear with rfl|rfl
      · exact hl
      · exact hr
    unfold incOK at hI
    rcases of_decide_eq_true hI with ht|ht
    · change succ P x.value≤u.value+1
      have hN := hu.2.2 hE
      unfold succ
      split <;> omega
    · exact Int.le_of_lt (by change succ P x.value<u.value+1; omega)
  | hold => exact hBelow

/-- The flooding no-new-low-error lemma at one centre. The aperture
hypothesis is precisely the old G bound at neighbouring errors up to
level ceiling−1. Already-low errors may clear (outside the conclusion)
but cannot move to a different error level. -/
theorem no_new_low_error (P ceiling : Int) (l x r : Clock)
    (hQ : root P l x r=true → base P x=true)
    (hAperture : ∀ u, (u=l ∨ u=r) → u.err=true → u.value≤ceiling-1 → x.value≤u.value+1)
    (he : (poll P l x r).err=true) (hLow : (poll P l x r).value≤ceiling) :
    poll P l x r = x := by
  generalize hh : poll P l x r = y at he hLow ⊢
  have h := hh ▸ poll_facts P l x r
  cases h with
  | reset hR hB => rw [hQ hR] at hB; cases hB
  | propagate v hv _ hw =>
    obtain ⟨u,hu,hE,hU⟩ := hw
    change v≤ceiling at hLow
    have h := hAperture u hu hE (by omega)
    omega
  | clear _ _ _ => cases he
  | inc _ _ _ => cases he
  | hold => rfl

private theorem Q_reset_disabled (P : Int) (l x r : Clock)
    (hQ : root P l x r=true → base P x=true) :
    (root P l x r && !base P x)=false := by
  cases h : root P l x r
  · rfl
  · simp [hQ h]

private theorem prop_le_suggestion (l x r u : Clock) (hu : u=l ∨ u=r) :
    propValue l x r≤suggestion x u := by
  unfold propValue
  rcases hu with rfl|rfl <;> omega

/-- Flood round's decisive service: an actual neighbouring negative
error with positive slack below zero forces this site's value to at
most that error plus one. Q rules out priority RESET (although reset
would satisfy the same numeric bound anyway). -/
theorem poll_fills_error_ceiling (P : Int) (l x r u : Clock) (hP : 0<P)
    (hu : Valid P u) (hE : u.err=true) (hNear : u=l ∨ u=r) (hNeg : u.value+1<0)
    (hQ : root P l x r=true → base P x=true) :
    (poll P l x r).value≤u.value+1 := by
  by_cases hb : x.value≤u.value+1
  · exact poll_keeps_error_ceiling P l x r u hP hu hE hNear hb
  · have hs : suggestion x u = u.value+1 := by
      simp [suggestion,hE,hNeg]
      omega
    have hv := prop_le_suggestion l x r u hNear
    rw [hs] at hv
    have hp : propValue l x r < x.value := by omega
    unfold poll signedRow
    rw [if_neg (by simp [Q_reset_disabled P l x r hQ]),if_pos hp]
    exact hv

private theorem suggestion_eq_if_not_below (x y : Clock)
    (hy : x.value≤y.value+1) : suggestion x y=x.value := by
  unfold suggestion
  split <;> omega

/-- Once the remaining erroneous band has no holes and no error above
x, activating this maximum error clears it without changing its value. -/
theorem poll_clears_top_error (P : Int) (l x r : Clock)
    (hQ : root P l x r=true → base P x=true)
    (hE : x.err=true) (hl : near x.value l.value=true) (hr : near x.value r.value=true)
    (hL : l.err=true → l.value≤x.value) (hR : r.err=true → r.value≤x.value) :
    poll P l x r = ⟨false,x.value⟩ := by
  have ha : x.value≤l.value+1 := (of_decide_eq_true hl : _ ∧ _).1
  have hb : x.value≤r.value+1 := (of_decide_eq_true hr : _ ∧ _).1
  have hP : propValue l x r=x.value := by
    simp [propValue,suggestion_eq_if_not_below x l ha,suggestion_eq_if_not_below x r hb]
  have hS (u : Clock) (hu : near x.value u.value=true) (hh : u.err=true → u.value≤x.value) :
      clearOK x u=true := by
    cases he : u.err
    · simp [clearOK,hu,he]
    · simp [clearOK,hu,he,hh he]
  unfold poll signedRow
  rw [if_neg (by simp [Q_reset_disabled P l x r hQ]),if_neg (by simp [hP])]
  simp [hE,hS l hl hL,hS r hr hR]

/-- Under Q a nonbase error has an actual lower error next door. -/
theorem smaller_error_of_Q_nonbase (P : Int) (l x r : Clock)
    (hQ : root P l x r=true → base P x=true)
    (hE : x.err=true) (hB : base P x=false) :
    ∃ u, (u=l ∨ u=r) ∧ u.err=true ∧ u.value<x.value := by
  have hz : root P l x r=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    rw [hQ h] at hB
    cases hB
  have hh : lowerError x l=true ∨ lowerError x r=true := by
    simp only [root,hE,if_true] at hz
    cases hl : lowerError x l <;> cases hr : lowerError x r <;> simp_all
  rcases hh with hf|hf
  · have h := Bool.and_eq_true_iff.mp (show (l.err && decide (l.value<x.value))=true from hf)
    exact ⟨l,.inl rfl,h.1,of_decide_eq_true h.2⟩
  · have h := Bool.and_eq_true_iff.mp (show (r.err && decide (r.value<x.value))=true from hf)
    exact ⟨r,.inr rfl,h.1,of_decide_eq_true h.2⟩

end L4.UnisonRows
