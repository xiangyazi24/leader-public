import Leader.L4.WindowA0Guard
import Leader.L4.TripleRenewal
import Leader.L4.TripleControlled

/-! Exact finite-word contact weight for a released A0 return. -/
namespace L4.WindowA0Return
open BarrierIID TripleRenewal

/-- Exponent coordinate: b records whether the new top's donor has
already had a refill opportunity. -/
def exponent (I D : Nat) (b : Bool) : Nat := 2*(D-I)-b.toNat

/-- A nonnegative, common-denominator version of (2/3)^k.
Only exponents at most H are used in the clock. -/
def weight (H k : Nat) : Nat := 2^k * 3^(H-k)

theorem weight_next {H k : Nat} (h : k+1≤H) :
    3*weight H (k+1)=2*weight H k := by
  have E : H-k=(H-(k+1))+1 := by omega
  simp only [weight,E,Nat.pow_succ]
  ac_rfl

theorem weight_mono {H i j : Nat} (hij : i≤j) (hj : j≤H) :
    weight H j≤weight H i := by
  induction j with
  | zero => have he : i=0 := by omega
            rw [he]; exact Nat.le_refl _
  | succ j ih =>
    by_cases he : i=j+1
    · simp [he]
    · have A := ih (by omega) (by omega)
      have B := weight_next (H:=H) (k:=j) hj
      omega

theorem move_exponent {i d : Nat} (h : i<d) (b : Bool) :
    exponent i (d+1) b=exponent i d b+2 := by
  cases b <;> simp [exponent] <;> omega

theorem refill_exponent {i d : Nat} (h : i<d) :
    exponent i d true+1=exponent i d false := by simp [exponent]; omega

theorem payment_exponent {i d : Nat} (h : i<d) :
    exponent (i+1) d false+1=exponent i d true := by simp [exponent]; omega

private theorem es_succ {n} (f : Fin (n+1) → Int) :
    edgeSum f=f 0+edgeSum (fun e : Fin n => f e.succ) := by
  simp [edgeSum,List.ofFn_succ]

private theorem es_add {n} (f g : Fin n → Int) :
    edgeSum (fun e => f e+g e)=edgeSum f+edgeSum g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [es_succ,es_succ f,es_succ g,ih]; omega

private theorem es_const (n : Nat) (v : Int) : edgeSum (fun _ : Fin n => v)=(n:Int)*v := by
  induction n with
  | zero => simp [edgeSum]
  | succ n ih =>
    rw [es_succ]
    change v+edgeSum (fun _ : Fin n => v)=_
    rw [ih,Int.natCast_succ,Int.add_mul,Int.one_mul,Int.add_comm]

private theorem es_mono {n} (f g : Fin n → Int) (h : ∀ e, f e≤g e) : edgeSum f≤edgeSum g := by
  induction n with
  | zero => simp [edgeSum]
  | succ n ih => rw [es_succ,es_succ]; exact Int.add_le_add (h 0) (ih _ _ fun e => h e.succ)

private theorem drift_two {n} (r a : Fin n) (hne : r≠a) (w : Nat)
    (f : Fin n → Nat) (hr : 9*f r≤4*w) (ha : 2*f a≤3*w)
    (he : ∀ e, e≠r → e≠a → f e≤w) :
    edgeSum (fun e => (f e:Int))≤(n:Int)*w := by
  let b := fun (e : Fin n) => (w:Int) +
    (if e=r then (f r:Int)-w else 0) + (if e=a then (f a:Int)-w else 0)
  have hh := es_mono (fun e => (f e : Int)) b (fun e => by
    by_cases h1 : e=r
    · subst e; simp [b,hne]; omega
    · by_cases h2 : e=a
      · subst e; simp [b,h1]; omega
      · have H := he e h1 h2
        simpa [b,h1,h2] using H)
  unfold b at hh
  rw [es_add,es_add,es_const,edgeSum_selector,edgeSum_selector] at hh
  omega

/-- A return service reduces weight by at least 4/9, the one distinct
possible refill/payment raises it by at most 3/2, and all other marks
are nonincreasing. Their exact joint one-step drift is nonpositive. -/
theorem return_drift {n H k : Nat} {f : Fin n → Nat} (r a : Fin n) (hne : r≠a)
    (hk : 1≤k) (hR : k+2≤H)
    (hr : f r≤weight H (k+2)) (ha : f a≤weight H (k-1))
    (he : ∀ e, e≠r → e≠a → f e≤weight H k) :
    edgeSum (fun e => (f e:Int))≤(n:Int)*weight H k := by
  apply drift_two r a hne _ f
  · have A := weight_next (H:=H) (k:=k+1) hR
    have B := weight_next (H:=H) (k:=k) (by omega)
    rw [show k+1+1=k+2 by omega] at A
    omega
  · have A := weight_next (H:=H) (k:=k-1) (by omega)
    have B : k-1+1=k := by omega
    rw [B] at A
    omega
  · exact he

/- An arbitrary finite monitor may use actual states or raw-prefix
   histories. The two exits are treated at their first occurrence. -/
inductive Position where
  | accepted
  | contact
  | active (level : Nat)
deriving DecidableEq

def credit (H : Nat) : Position → Nat
  | .accepted => 0
  | .contact => 3^H
  | .active k => weight H k

def done : Position → Prop
  | .active _ => False
  | _ => True

private theorem es_scale {n} (c : Int) (f : Fin n → Int) :
    edgeSum (fun e => c*f e)=c*edgeSum f := by
  induction n with
  | zero => simp [edgeSum]
  | succ n ih => rw [es_succ,es_succ f,ih,Int.mul_add]

private theorem es_nat {n} (f : Fin n → Nat) :
    edgeSum (fun e => (f e:Int))=(TaggedTail.sumEdge f : Int) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [es_succ]
    change (f 0 : Int)+edgeSum (fun e : Fin n => (f e.succ : Int)) =
      (((List.ofFn f).sum : Nat) : Int)
    rw [List.ofFn_succ,List.sum_cons,Int.natCast_add,ih]
    rfl

/-- Integer supermartingale for first physical contact. Accepted, global
early exits, or earlier genuine door acceptance may be assigned zero;
contact is charged absorbing unit credit in the first-hit word count. -/
theorem contact_mass {α : Type} {n H : Nat} (step : α → Fin n → α)
    (pos : α → Position) (good : α → Prop)
    (keep : ∀ x e k, good x → pos x=.active k → good (step x e))
    (hrow : ∀ x k, good x → pos x=.active k →
      ∃ r a : Fin n, r≠a ∧ 1≤k ∧ k+2≤H ∧
        credit H (pos (step x r))≤weight H (k+2) ∧
        credit H (pos (step x a))≤weight H (k-1) ∧
        ∀ e, e≠r → e≠a → credit H (pos (step x e))≤weight H k) :
    ∀ t x, good x →
      3^H*terminalMass step (fun y => done (pos y)) (fun y => pos y=.contact) t x
        ≤ credit H (pos x)*n^t := by
  classical
  intro t
  induction t with
  | zero =>
    intro x hx
    cases h : pos x <;> simp [terminalMass,h,done,credit]
  | succ t ih =>
    intro x hx
    cases h : pos x with
    | accepted => simp [terminalMass,h,done,credit]
    | contact => simp [terminalMass,h,done,credit]
    | active k =>
      obtain ⟨r,a,hne,hk,hH,hr,ha,he⟩ := hrow x k hx h
      have D := return_drift r a hne hk hH hr ha he
      simp only [terminalMass,h,done,if_false,credit]
      apply Int.ofNat_le.mp
      simp only [Int.natCast_mul,Int.natCast_pow]
      rw [←Int.natCast_pow,←es_nat,←es_scale,Int.pow_succ]
      have I := es_mono _ _ (fun e => Int.ofNat_le.mpr (ih (step x e) (keep x e k hx h)))
      simp only [Int.natCast_mul] at I
      rw [show (fun e : Fin n => (credit H (pos (step x e)) : Int)*(n^t : Nat)) =
          (fun e : Fin n => (n^t : Nat)*(credit H (pos (step x e)) : Int))
          from funext (fun _ => Int.mul_comm _ _),es_scale (↑(n ^ t) : Int)] at I
      apply Int.le_trans I
      simpa only [Int.natCast_pow,Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using
        Int.mul_le_mul_of_nonneg_left D (Int.natCast_nonneg (n^t))

/-- If the genuine released return starts strictly ahead, its first
contact uses at most two thirds of raw words at every finite horizon. -/
theorem contact_two_thirds {α : Type} {n H : Nat} (step : α → Fin n → α)
    (pos : α → Position) (good : α → Prop)
    (keep : ∀ x e k, good x → pos x=.active k → good (step x e))
    (hrow : ∀ x k, good x → pos x=.active k →
      ∃ r a : Fin n, r≠a ∧ 1≤k ∧ k+2≤H ∧
        credit H (pos (step x r))≤weight H (k+2) ∧
        credit H (pos (step x a))≤weight H (k-1) ∧
        ∀ e, e≠r → e≠a → credit H (pos (step x e))≤weight H k)
    (t : Nat) (x : α) (hx : good x) {k : Nat} (hp : pos x=.active k) :
    3*terminalMass step (fun y => done (pos y)) (fun y => pos y=.contact) t x≤2*n^t := by
  obtain ⟨_,_,_,hk,hH,_,_,_⟩ := hrow x k hx hp
  have T := contact_mass step pos good keep hrow t x hx
  rw [hp] at T
  change 3^H*_≤weight H k*n^t at T
  have W := weight_mono hk (by omega : k≤H)
  have A := weight_next (H:=H) (k:=0) (by omega)
  have T' := Nat.le_trans T (Nat.mul_le_mul_right (n^t) W)
  have H' := Nat.mul_le_mul_left 3 T'
  rw [←Nat.mul_assoc,←Nat.mul_assoc,A,show weight H 0=3^H by simp [weight]] at H'
  apply Nat.le_of_mul_le_mul_left (c:=3^H) ?_ (by exact Nat.pow_pos (by decide))
  simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using H'

/-- After a paid top advance, a vacated empty nonliving donor cannot
gain a byte or become a leader by initiating a service into the still
empty new top. Before an incoming refill opportunity it cannot pay. -/
theorem vacated_outgoing_stays_empty {p c : Nat} (u v : Site p c)
    (hl : u.leader=false) (hu : u.stock=false) (hv : v.stock=false) :
    (pairStep u v).1.leader=false ∧ (pairStep u v).1.stock=false := by
  exact ⟨(pair_geometric_fields u v).2.1.trans hl,
    (WindowA0Rows.unstocked_nonleader_pair u v hl hu hv).1⟩

/-- Rebase at the refill edge: the active return's outgoing mark is
clockwise at offset D−I+2; the top-payment mark is at offset one.
Both are distinct from that return mark inside one short sector. -/
theorem separated_return_labels {n gap : Nat} (base : Fin n)
    (hg : 0<gap) (h : gap+2<n) :
    liftedSite base (gap+2) ≠ base ∧
    liftedSite base (gap+2) ≠ rightNeighbor base := by
  constructor
  · intro he
    have he0 := he.trans (liftedSite_zero base).symm
    have E := liftedSite_inj base h (by omega : 0<n) he0
    omega
  · intro he
    have hs : liftedSite base 1=rightNeighbor base := by
      rw [liftedSite_succ,liftedSite_zero]
    rw [←hs] at he
    have E := liftedSite_inj base h (by omega : 1<n) he
    omega

/-- A nonincreasing reserve with a strict decrease on one predictable
label gives at most n marks per unit. This applies both to outward
approach (distance to the old top) and return (distance to the door);
every early physical exit can carry reserve zero. -/
theorem nominated_mean {α : Type} {n : Nat} (next : α → Fin n → α)
    (done invariant : α → Prop) (work : α → Nat)
    (keep : ∀ x e, invariant x → ¬done x → invariant (next x e))
    (row : ∀ x, invariant x → ¬done x →
      (∃ e, work (next x e)+1≤work x) ∧ ∀ e, work (next x e)≤work x)
    (x : α) (hx : invariant x) :
    IIDExpectedHittingTimeAtMost next done x (n*work x) :=
  TripleControlled.mean_of_potential next done invariant work keep (by
    intro y hy hd
    obtain ⟨⟨e,h⟩,hall⟩ := row y hy hd
    exact TripleControlled.progress_raw_drift _ e _ h hall) x hx

/-- The guard's at-most-six raw labels. Its list may contain modular
aliases, but membership is a set test, not a multiset race weight. -/
def guardLabels {n : Nat} (farLeft : Fin n) : List (Fin n) :=
  (List.range 6).map (liftedSite farLeft)

/-- An unrequested label outside the guard cannot touch its five
interior sockets (offsets 1 through 5 from i−2). This is independent
of clock, residue, signals, or any unrelated protocol activity. -/
theorem step_off_guard {p c n : Nat} (x : Config p c n)
    (farLeft e : Fin n) (j : Nat) (hj : 1≤j) (hk : j≤5)
    (hout : e ∉ guardLabels farLeft) :
    step x e (liftedSite farLeft j)=x (liftedSite farLeft j) := by
  have hjmem : liftedSite farLeft j ∈ guardLabels farLeft :=
    List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),rfl⟩
  have hI : liftedSite farLeft j≠e := fun h => hout (h ▸ hjmem)
  have hR : liftedSite farLeft j≠rightNeighbor e := by
    intro he
    have hj' : j-1+1=j := by omega
    have N : rightNeighbor (liftedSite farLeft (j-1))=rightNeighbor e := by
      rw [←liftedSite_succ,hj',he]
    have N' := congrArg RearTrace.predecessor N
    simp only [RearTrace.predecessor_right] at N'
    exact hout (List.mem_map.mpr ⟨j-1,List.mem_range.mpr (by omega),N'⟩)
  simp [step,hI,hR]

/-- A waiting door at the untouched tail does not consume or recreate
the genuine worker. Its OUT rail, or one nonempty trail segment, is a
stable left input to the door; the old right socket is irrelevant. -/
theorem waiting_door_keeps_worker_or_trail {Q : Nat} (trip : FixedResidual.Trip Q)
    (right left : Rail)
    (h : left=FixedResidual.outward trip ∨ left=.t) :
    (patrol true true false (FixedResidual.waitingFor trip) left right).source =
      FixedResidual.waitingFor trip ∧
    (patrol true true false (FixedResidual.waitingFor trip) left right).left = left := by
  cases trip <;> rcases h with rfl|rfl <;> cases right <;> exact ⟨rfl,rfl⟩

/-- A literal trace needs only realize the three possible classified
motion updates. The return service either accepts or moves one site;
the unique adverse mark can be a harmless stutter, a charge of one,
or first contact (necessarily from exponent one). -/
structure LocalEvents {α : Type} {n H : Nat} (step : α → Fin n → α)
    (pos : α → Position) (x : α) (k : Nat) : Type where
  ret : Fin n
  adv : Fin n
  distinct : ret≠adv
  positive : 1≤k
  capped : k+2≤H
  returning : pos (step x ret)=.accepted ∨ pos (step x ret)=.active (k+2)
  adverse : pos (step x adv)=.accepted ∨ pos (step x adv)=.active k ∨
    pos (step x adv)=.active (k-1) ∨ (k=1 ∧ pos (step x adv)=.contact)
  other : ∀ e, e≠ret → e≠adv → pos (step x e)=.accepted ∨ pos (step x e)=.active k

/-- Physical first-contact theorem phrased by literal mark classes, not by
a presumed transition law for probabilities. The only missing physical
input at an application is closure and classification of the observer. -/
theorem contact_of_events {α : Type} {n H : Nat} (step : α → Fin n → α)
    (pos : α → Position) (good : α → Prop)
    (keep : ∀ x e k, good x → pos x=.active k → good (step x e))
    (row : ∀ x k, good x → pos x=.active k →
      Nonempty (LocalEvents (H:=H) step pos x k))
    (t : Nat) (x : α) (hx : good x) {k : Nat} (hp : pos x=.active k) :
    3*terminalMass step (fun y => done (pos y)) (fun y => pos y=.contact) t x≤2*n^t := by
  refine contact_two_thirds (H:=H) step pos good keep ?_ t x hx hp
  intro z j hG hP
  obtain ⟨L⟩ := row z j hG hP
  refine ⟨L.ret,L.adv,L.distinct,L.positive,L.capped,?_,?_,?_⟩
  · rcases L.returning with h|h <;> simp [h,credit]
  · rcases L.adverse with h|h|h|⟨he,h⟩
    · simp [h,credit]
    · rw [h]
      exact weight_mono (by omega) (by have := L.capped; omega)
    · simp [h,credit]
    · simp [h,he,credit,weight]
  · intro e hr ha
    rcases L.other e hr ha with h|h <;> simp [h,credit]

#print axioms contact_two_thirds

end L4.WindowA0Return
