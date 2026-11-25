import Leader.L4.TripleRenewal
import Leader.L4.GGTiming

/-! The finite-word common clock of the last-two argument. The span observer
charges at most one predictable physical edge per raw mark. -/
namespace L4.WindowClock
open TaggedTail TripleRenewal RankRenewal Classical

private theorem sSucc {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f=f 0+sumEdge (fun e => f e.succ) := by
  simp [sumEdge,List.ofFn_succ]

private theorem sMono {n : Nat} {f g : Fin n → Nat} (h : ∀ e, f e≤g e) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc]; exact Nat.add_le_add (h _) (ih (fun i => h i.succ))

private theorem sConst (n a : Nat) : sumEdge (fun _ : Fin n => a)=n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,ih,Nat.succ_mul,Nat.add_comm]

private theorem sAdd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e+g e)=sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sSucc,sSucc f,sSucc g,ih]; omega

private theorem sMul {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => a*f e)=a*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc f,ih,Nat.mul_add]

private theorem sPick {n : Nat} (i : Fin n) :
    sumEdge (fun e => if e=i then 1 else 0)=1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [sSucc]
      simp [show (fun i : Fin n => if i.succ=(0 : Fin (n+1)) then 1 else 0) =
        (fun _ => 0) from funext (fun i => by simp [Fin.succ_ne_zero]),sConst]
    · rw [sSucc,if_neg (Ne.symm (Fin.succ_ne_zero j))]
      simpa using ih j

/-- A physically moving right boundary can increase its lifted span by
one only on the single pre-nominated edge. This implication is enough;
not every selected nomination needs to move the boundary. -/
theorem average_span_step {α : Type} {n : Nat} (next : α → Fin n → α)
    (span : α → Nat) (x : α) (nom : Fin n)
    (hh : ∀ e, span (next x e)≤span x+(if e=nom then 1 else 0)) :
    sumEdge (fun e => span (next x e))≤n*span x+1 := by
  have h := sMono hh
  rw [sAdd,sConst,sPick] at h
  exact h

/-- Endpoint objective frozen at first stopping. If the horizon occurs
first, use the objective there. All raw suffixes retain their weights. -/
noncomputable def stoppedWeight {α : Type} {n : Nat} (next : α → Fin n → α)
    (done : α → Prop) (W : α → Nat) : Nat → α → Nat
  | 0, x => W x
  | t+1, x => if done x then W x*n^(t+1)
      else sumEdge (fun e => stoppedWeight next done W t (next x e))

/-- Stopped mark frequency: the expected number of charges to a
predictable one-edge nomination is at most expected stopped duration
divided by n. This form even allows skipped charges or span decreases. -/
theorem stoppedWeight_of_span_step {α : Type} {n : Nat}
    (next : α → Fin n → α) (done good : α → Prop) (W : α → Nat)
    (keep : ∀ x e, good x → good (next x e))
    (drift : ∀ x, good x → ¬done x → sumEdge (fun e => W (next x e))≤n*W x+1)
    (t : Nat) (x : α) (hx : good x) :
    n*stoppedWeight next done W t x≤n*W x*n^t+iidHitCost next done t x := by
  induction t generalizing x with
  | zero => simp [stoppedWeight,iidHitCost]
  | succ t ih =>
    by_cases hd : done x
    · simp [stoppedWeight,iidHitCost,hd,Nat.mul_assoc]
    · simp only [stoppedWeight,iidHitCost,hd,if_false,←sMul]
      let S := sumEdge (fun e => W (next x e))
      let C := sumEdge (fun e => iidHitCost next done t (next x e))
      calc
        _ ≤ sumEdge (fun e => n*W (next x e)*n^t+iidHitCost next done t (next x e)) :=
          sMono (fun e => ih (next x e) (keep x e hx))
        _ = n*n^t*S+C := by
          rw [sAdd]
          have h (e : Fin n) : n*W (next x e)*n^t=(n*n^t)*W (next x e) := by ac_rfl
          simp only [h,sMul,S,C]
        _ ≤ n*n^t*(n*W x+1)+C :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (drift x hx hd)) _
        _ = _ := by
          change _ = n*W x*n^(t+1)+(n^(t+1)+C)
          rw [Nat.pow_succ,Nat.mul_add,Nat.mul_one,Nat.mul_comm n (n^t)]
          ac_rfl

/-- Glue a future expected cost that depends on the first stopped
objective. On unfinished words the unused continuation allowance is
nonnegative. -/
theorem glue_weighted {α : Type} {n : Nat} {step : α → Fin n → α}
    {x : α} (s : Stage step x) (goal : α → Prop) (W : s.State → Nat) (F : Nat)
    (cont : ∀ z, s.reachable z → s.ready z → ¬goal (s.project z) →
      IIDExpectedHittingTimeAtMost step goal (s.project z) (F*W z))
    (t : Nat) (z : s.State) (hz : s.reachable z) :
    iidHitCost step goal t (s.project z)≤iidHitCost s.next s.ready t z+
      F*stoppedWeight s.next s.ready W t z := by
  induction t generalizing z with
  | zero => simp [iidHitCost]
  | succ t ih =>
    by_cases hg : goal (s.project z)
    · rw [iidHitCost_of_target step goal _ hg]; exact Nat.zero_le _
    · by_cases hp : s.ready z
      · simpa [iidHitCost,stoppedWeight,hp,Nat.mul_assoc] using cont z hz hp hg (t+1)
      · rw [iidHitCost,if_neg hg,iidHitCost,if_neg hp,stoppedWeight,if_neg hp,←sMul]
        let G := sumEdge (fun e => iidHitCost step goal t (s.project (s.next z e)))
        let C := sumEdge (fun e => iidHitCost s.next s.ready t (s.next z e))
        let R := sumEdge (fun e => F*stoppedWeight s.next s.ready W t (s.next z e))
        have h : G≤C+R := by
          dsimp [G,C,R]
          rw [←sAdd]
          exact sMono (fun e => ih (s.next z e) (s.reachStep z e hz))
        change n^(t+1)+sumEdge (fun e => iidHitCost step goal t (step (s.project z) e)) ≤ n^(t+1)+C+R
        simp only [←s.projStep]
        change n^(t+1)+G≤n^(t+1)+C+R
        omega

/-- Compose one adapted stage of mean C*n*(span+1) with a post-stop
clock of coefficient F at the new span. -/
theorem stage_of_span {α : Type} {n : Nat} {step : α → Fin n → α} {x : α}
    (s : Stage step x) (goal : α → Prop) (span : s.State → Nat) (startSpan C F : Nat)
    (hs : span s.start≤startSpan)
    (nom : s.State → Fin n)
    (hlocal : ∀ z e, s.reachable z → ¬s.ready z →
      span (s.next z e)≤span z+(if e=nom z then 1 else 0))
    (prep : IIDExpectedHittingTimeAtMost s.next s.ready s.start (C*n*(startSpan+1)))
    (cont : ∀ z, s.reachable z → s.ready z → ¬goal (s.project z) →
      IIDExpectedHittingTimeAtMost step goal (s.project z) (F*n*(span z+1))) :
    IIDExpectedHittingTimeAtMost step goal x ((C+(1+C)*F)*n*(startSpan+1)) := by
  intro t
  let W := fun z => span z+1
  let N := n^t
  let Cst := iidHitCost s.next s.ready t s.start
  let G := stoppedWeight s.next s.ready W t s.start
  let P := n*(startSpan+1)
  have hw := stoppedWeight_of_span_step s.next s.ready s.reachable W
    s.reachStep (fun z h hz => by
      have hh := average_span_step s.next span z (nom z) (fun e => hlocal z e h hz)
      dsimp [W]
      rw [sAdd,sConst,Nat.mul_add,Nat.mul_one]
      omega) t s.start s.reachStart
  have hh : n*G≤P*N+Cst := by
    exact Nat.le_trans hw (Nat.add_le_add_right (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left _ (show W s.start≤startSpan+1 from Nat.succ_le_succ hs))) _)
  have hg := glue_weighted s goal W (F*n) cont t s.start s.reachStart
  rw [s.projInit] at hg
  have hc : Cst≤C*P*N := by
    simpa [Cst,P,N,Nat.mul_assoc] using prep t
  calc
    _ ≤ Cst+(F*n)*G := hg
    _ = Cst+F*(n*G) := by rw [Nat.mul_assoc]
    _ ≤ Cst+F*(P*N+Cst) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hh) _
    _ ≤ C*P*N+F*(P*N+C*P*N) :=
      Nat.add_le_add hc (Nat.mul_le_mul_left _ (Nat.add_le_add_left hc _))
    _ = _ := by
      dsimp [P,N]
      simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul]
      ac_rfl

/-- Evidence for a sequence of at most j adapted stages. Stage boundaries
are actual stopping rules, and each future stage has its own start span.
The terminal goal includes the specified early success/failure exits. -/
inductive WindowStages {α : Type} {n : Nat} (step : α → Fin n → α)
    (goal : α → Prop) (C : Nat) : Nat → α → Nat → Prop where
  | already {j x h} (done : goal x) : WindowStages step goal C j x h
  | phase {j x h} (s : Stage step x) (span : s.State → Nat)
    (startSpan : span s.start≤h) (nom : s.State → Fin n)
    (hlocal : ∀ z e, s.reachable z → ¬ s.ready z → span (s.next z e)≤span z+(if e=nom z then 1 else 0))
    (prep : IIDExpectedHittingTimeAtMost s.next s.ready s.start (C*n*(h+1)))
    (after : ∀ z, s.reachable z → s.ready z → ¬ goal (s.project z) →
      WindowStages step goal C j (s.project z) (span z)) :
    WindowStages step goal C (j+1) x h

/-- Close the recurrence of the five common-clock stages at *every*
finite horizon, not via a real limit. -/
theorem windowStages_mean {α : Type} {n : Nat} {step : α → Fin n → α}
    {goal : α → Prop} {C j : Nat} {x : α} {h : Nat}
    (s : WindowStages step goal C j x h) :
    IIDExpectedHittingTimeAtMost step goal x (((1+C)^j-1)*n*(h+1)) := by
  induction s with
  | already done =>
    intro t; rw [iidHitCost_of_target step goal _ done]; exact Nat.zero_le _
  | @phase j x h s span hspan nom hlocal prep after ih =>
    have hh := stage_of_span s goal span h C ((1+C)^j-1) hspan nom hlocal prep ih
    have he : C+(1+C)*((1+C)^j-1)=(1+C)^(j+1)-1 := by
      let d := (1+C)^j
      have hd : 0<d := Nat.pow_pos (by omega)
      have hp : (1+C)^(j+1)=d*(1+C) := Nat.pow_succ ..
      have hh : (1+C)*(d-1)+(1+C)=(1+C)*d := by
        rw [←Nat.mul_succ,show (d-1).succ=d by omega]
      have hcomm : (1+C)*d=d*(1+C) := Nat.mul_comm ..
      change C+(1+C)*(d-1)=(1+C)^(j+1)-1
      omega
    rwa [he] at hh

/-- Raw indicator used in the common-window failure/success numerators. -/
noncomputable def indicator {α : Type} (p : α → Prop) (x : α) : Nat :=
  if p x then 1 else 0

private theorem eConst {α : Type} {n : Nat} (next : α → Fin n → α)
    (a t : Nat) (x : α) : endpointSum next (fun _ => a) t x=a*n^t := by
  induction t generalizing x with
  | zero => simp [endpointSum]
  | succ t ih => simp only [endpointSum,ih,sConst,Nat.pow_succ]; ac_rfl

private theorem eAdd {α : Type} {n : Nat} (next : α → Fin n → α)
    (f g : α → Nat) (t : Nat) (x : α) :
    endpointSum next (fun y => f y+g y) t x=endpointSum next f t x+endpointSum next g t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simp only [endpointSum,ih,sAdd]

private theorem eMono {α : Type} {n : Nat} (next : α → Fin n → α)
    {f g : α → Nat} (h : ∀ x, f x≤g x) (t : Nat) (x : α) :
    endpointSum next f t x≤endpointSum next g t x := by
  induction t generalizing x with
  | zero => exact h x
  | succ t ih => exact sMono (fun e => ih (next x e))

private theorem endpoint_dead {α : Type} {n : Nat} (next : α → Fin n → α)
    (done : α → Prop) (closed : ∀ x e, done x → done (next x e))
    (t : Nat) (x : α) (hx : done x) :
    endpointSum next (indicator fun y => ¬done y) t x=0 := by
  induction t generalizing x with
  | zero => simp [endpointSum,indicator,hx]
  | succ t ih =>
    simp only [endpointSum,ih _ (closed x _ hx),sConst,Nat.mul_zero]

private theorem endpoint_live {α : Type} {n : Nat} (next : α → Fin n → α)
    (done : α → Prop) (closed : ∀ x e, done x → done (next x e))
    (t : Nat) (x : α) :
    endpointSum next (indicator fun y => ¬done y) t x =
      survival next (fun y => ¬done y) t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases hd : done x
    · rw [endpoint_dead next done closed _ _ hd]
      simp [survival,weightedSurvival,hd]
    · simp only [endpointSum,survival,weightedSurvival,hd,not_false_eq_true,if_true]
      exact congrArg sumEdge (funext (fun e => ih (next x e)))

/-- A window reward on a common deterministic raw-word horizon.
The only probability assumptions are a mean-to-final-stop bound, a
quarter entry-cut tail, and the 11/1000 fresh failure budget. The
logical event cover is deterministic on the same complete observer. -/
theorem window_reward_of_budget {α : Type} {n : Nat} (next : α → Fin n → α)
    (done reward entryBad freshBad : α → Prop)
    (closed : ∀ x e, done x → done (next x e))
    (eventCover : ∀ y, done y → ¬entryBad y → ¬freshBad y → reward y)
    (K T : Nat) (hK : 0<K) (hT : 4*K≤T) (x : α)
    (clock : IIDExpectedHittingTimeAtMost next done x K)
    (entry : 4*endpointSum next (indicator entryBad) T x≤n^T)
    (fresh : 1000*endpointSum next (indicator freshBad) T x≤11*n^T) :
    12*n^T≤25*endpointSum next (indicator reward) T x := by
  let N := n^T
  let S := survival next (fun y => ¬done y) T x
  have ht : T*S≤K*N := Nat.le_trans (RankPhysical.horizon_mul_survival_le_cost next done T x) (clock T)
  have hlo : 4*S≤N := by
    apply Nat.le_of_mul_le_mul_left _ hK
    calc
      _ = (4*K)*S := by ac_rfl
      _ ≤ T*S := Nat.mul_le_mul_right _ hT
      _ ≤ _ := ht
  have hcover (y : α) : 1≤indicator reward y+indicator (fun z => ¬done z) y+
      indicator entryBad y+indicator freshBad y := by
    by_cases hd : done y
    · by_cases he : entryBad y
      · simp [indicator,hd,he]; omega
      · by_cases hf : freshBad y
        · simp [indicator,hd,he,hf]
        · simp [indicator,hd,he,hf,eventCover y hd he hf]
    · simp [indicator,hd]; omega
  have hu := eMono next hcover T x
  rw [eConst,eAdd,eAdd,eAdd,endpoint_live next done closed,Nat.one_mul] at hu
  change N≤endpointSum next (indicator reward) T x+S+
      endpointSum next (indicator entryBad) T x+endpointSum next (indicator freshBad) T x at hu
  change 4*endpointSum next (indicator entryBad) T x≤N at entry
  change 1000*endpointSum next (indicator freshBad) T x≤11*N at fresh
  change 12*N≤_
  omega

/-- Direct five-stage specialization sufficient for the GroupReward
probability interface. Fixed experiment parameters such as the
initial tags are stored in the observer or held externally. -/
theorem five_stage_reward {α : Type} {n : Nat} (next : α → Fin n → α)
    (done reward entryBad freshBad : α → Prop)
    (closed : ∀ x e, done x → done (next x e))
    (eventCover : ∀ y, done y → ¬entryBad y → ¬freshBad y → reward y)
    (C h T : Nat) (hn : 0<n) (hC : 0<C)
    (hT : 4*(((1+C)^5-1)*n*(h+1))≤T) (x : α)
    (clock : WindowStages next done C 5 x h)
    (entry : 4*endpointSum next (indicator entryBad) T x≤n^T)
    (fresh : 1000*endpointSum next (indicator freshBad) T x≤11*n^T) :
    12*n^T≤25*endpointSum next (indicator reward) T x := by
  have hpow : 1+C ≤ (1+C)^5 := by
    simpa only [Nat.pow_one] using (Nat.pow_le_pow_right (show 0<1+C by omega)
      (by decide : 1≤5))
  have hK : 0<((1+C)^5-1)*n*(h+1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) hn) (Nat.succ_pos _)
  exact window_reward_of_budget next done reward entryBad freshBad closed eventCover _ T hK hT x
    (windowStages_mean clock) entry fresh

/-- Thread the lifted left and right root positions without assigning
an absolute physical coordinate to a wrapped root. Right displacement
from the initial lift upper-bounds the span increase; motion of the left
endpoint can only improve the bound. -/
theorem span_le_initial_add_displacement (left right left' right' X : Nat)
    (hleft : left≤left') (hright : right'≤right+X) :
    right'-left'≤right-left+X := by omega

/-- The short-window cutoff fits the one common block of the window clock.
B=8*((1+C)^5−1)=2*B₇ and does not depend on the cut or window. -/
theorem common_deadline (C n s D L : Nat) (short : s≤D) (cap : D+1≤2*L) :
    4*(((1+C)^5-1)*n*(s+1)) ≤ (8*((1+C)^5-1))*n*L := by
  let K := (1+C)^5-1
  change 4*(K*n*(s+1))≤8*K*n*L
  calc
    _ = (4*K*n)*(s+1) := by ac_rfl
    _ ≤ (4*K*n)*(2*L) := Nat.mul_le_mul_left _ (Nat.le_trans (Nat.succ_le_succ short) cap)
    _ = (4*2)*K*n*L := by ac_rfl
    _ = _ := rfl

/-- Endpoints of a first-attempt state machine ordinarily still take
all future raw marks. A sticky loss indicator at a shorter deadline
pads to the longer common horizon with the corresponding power of n. -/
theorem sticky_mass_pad {α : Type} {n : Nat} (next : α → Fin n → α)
    (bad : α → Prop) (keep : ∀ x e, bad x → bad (next x e))
    (T U : Nat) (x : α) :
    n^U*endpointSum next (indicator bad) T x≤endpointSum next (indicator bad) (T+U) x := by
  have constant_after (x : α) (hx : bad x) (j : Nat) :
      endpointSum next (indicator bad) j x=n^j := by
    induction j generalizing x with
    | zero => simp [endpointSum,indicator,hx]
    | succ j ih =>
      simp only [endpointSum,ih _ (keep x _ hx),sConst,Nat.pow_succ']
  induction T generalizing x with
  | zero =>
    by_cases h : bad x
    · simp [endpointSum,indicator,h,constant_after _ h]
    · simp [endpointSum,indicator,h]
  | succ T ih =>
    rw [show T+1+U=(T+U)+1 by omega]
    simp only [endpointSum,←sMul]
    exact sMono (fun e => ih (next x e))

private theorem eComp {α : Type} {n : Nat} (next : α → Fin n → α)
    (f : α → Nat) (T U : Nat) (x : α) :
    endpointSum next f (T+U) x=
      endpointSum next (fun z => endpointSum next f U z) T x := by
  induction T generalizing x with
  | zero => simp [endpointSum]
  | succ T ih =>
    rw [show T+1+U=(T+U)+1 by omega]
    simp only [endpointSum,ih]

private theorem eMul {α : Type} {n : Nat} (next : α → Fin n → α)
    (f : α → Nat) (a T : Nat) (x : α) :
    endpointSum next (fun z => a*f z) T x=a*endpointSum next f T x := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih => simp only [endpointSum,ih,sMul]

private theorem eCompare {α β : Type} {n : Nat} (next : α → Fin n → α)
    (other : β → Fin n → β) (f : α → Nat) (g : β → Nat)
    (T : Nat) (x : α) (y : β)
    (h : ∀ w : List (Fin n), w.length=T →
      f (GGTiming.runMarks next x w)≤g (GGTiming.runMarks other y w)) :
    endpointSum next f T x≤endpointSum other g T y := by
  induction T generalizing x y with
  | zero => exact h [] rfl
  | succ T ih =>
    exact sMono (fun e => ih (next x e) (other y e) (fun w hw => h (e::w) (by simp [hw])))

/-- A bad outcome by a common deadline can be injected into an earlier
prefix event, even when the experiment and prefix observer have different
state types. The subsequent marks are accounted for exactly by n^U. -/
theorem loss_mass_le_prefix {α β : Type} {n : Nat} (next : α → Fin n → α)
    (other : β → Fin n → β) (bad : α → Prop) (prefixBad : β → Prop)
    (T U : Nat) (x : α) (y : β)
    (inclusion : ∀ w v : List (Fin n), w.length=T → v.length=U →
      bad (GGTiming.runMarks next x (w++v)) → prefixBad (GGTiming.runMarks other y w)) :
    endpointSum next (indicator bad) (T+U) x ≤
      n^U*endpointSum other (indicator prefixBad) T y := by
  rw [eComp,←eMul]
  apply eCompare
  intro w hw
  let u := GGTiming.runMarks other y w
  have hv (v : List (Fin n)) (hv : v.length=U) :
      indicator bad (GGTiming.runMarks next (GGTiming.runMarks next x w) v)≤
        indicator prefixBad u := by
    by_cases h : bad (GGTiming.runMarks next (GGTiming.runMarks next x w) v)
    · have h' := inclusion w v hw hv (by rwa [GGTiming.runMarks_append])
      simp [indicator,h,h',u]
    · simp [indicator,h]
  have h := eCompare next next (indicator bad) (fun _ => indicator prefixBad u)
    U (GGTiming.runMarks next x w) x hv
  rw [eConst,Nat.mul_comm] at h
  exact h

/-- Early entry aborts are charged at their own deterministic horizon
4*K and then extended to the common deadline. Compare to a stopped A0
observer; no probability for an aborted later stage is charged here. -/
theorem entry_quarter_of_prefix {α β : Type} {n : Nat} (next : α → Fin n → α)
    (other : β → Fin n → β) (entryBad : α → Prop) (entryDone : β → Prop)
    (closed : ∀ y e, entryDone y → entryDone (other y e))
    (K U : Nat) (hK : 0<K) (x : α) (y : β)
    (bound : IIDExpectedHittingTimeAtMost other entryDone y K)
    (inclusion : ∀ w v : List (Fin n), w.length=4*K → v.length=U →
      entryBad (GGTiming.runMarks next x (w++v)) → ¬entryDone (GGTiming.runMarks other y w)) :
    4*endpointSum next (indicator entryBad) (4*K+U) x≤n^(4*K+U) := by
  have h := loss_mass_le_prefix next other entryBad (fun y => ¬entryDone y)
    (4*K) U x y inclusion
  rw [endpoint_live other entryDone closed] at h
  have hb := quarter_overrun K hK bound
  calc
    _ ≤ 4*(n^U*survival other (fun y => ¬entryDone y) (4*K) y) :=
      Nat.mul_le_mul_left _ h
    _ = n^U*(4*survival other (fun y => ¬entryDone y) (4*K) y) := by ac_rfl
    _ ≤ n^U*n^(4*K) := Nat.mul_le_mul_left _ hb
    _ = _ := by rw [←Nat.pow_add, Nat.add_comm U]

end L4.WindowClock

#print axioms L4.WindowClock.stoppedWeight_of_span_step
#print axioms L4.WindowClock.stage_of_span
#print axioms L4.WindowClock.windowStages_mean
#print axioms L4.WindowClock.five_stage_reward

#print axioms L4.WindowClock.common_deadline
#print axioms L4.WindowClock.sticky_mass_pad

#print axioms L4.WindowClock.loss_mass_le_prefix
#print axioms L4.WindowClock.entry_quarter_of_prefix
