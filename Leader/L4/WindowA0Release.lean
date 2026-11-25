import Leader.L4.WindowA0Return
import Leader.L4.WindowA0ReleaseCredit
import Leader.L4.SingletonFinish
import Leader.L4.FreshEpochAuthentication

/-! Literal local release scripts at a genuine A0 adjacency. -/
namespace L4.WindowA0Release
open FixedResidual

private theorem payFalse {p c : Nat} (u v : Site p c)
    (hL : u.leader=false) (hS : u.stock=false) : geometricPay u v=false := by
  cases h : geometricPay u v
  · rfl
  · have H := RearTrace.geometricPay_ready _ _ h
    simp [payer,hL,hS] at H

/-- Ordinary outward service when both endpoints are nonliving, the
initiator empty, and the responder's controller OFF. Ui is allowed
any X-free left neighbour; Uc needs E or T. -/
theorem outward_row {p c : Nat} (u v : Site p c) (q : Trip (2*c))
    (hm : u.mark=false) (hL : u.leader=false) (hR : v.leader=false)
    (hs : u.stock=false) (hr : v.residue=nextResidue u.residue) (hoff : v.source=.off)
    (hq : v.rail=outward q)
    (clean : match q with | .init => u.rail≠.x | .count _ => u.rail=.e ∨ u.rail=.t) :
    (pairStep u v).1.rail=outward q ∧ (pairStep u v).2.rail=.t ∧
    (pairStep u v).1.mark=false ∧ (pairStep u v).2.leader=false := by
  have A := SingletonFinish.alias_body_exact u v hm hL hR hr hs hoff
  have H := covered_pair_marks u v (by
    intro h
    rcases h with h|h
    · simp [hR] at h
    · exact (h hr).elim)
  simp only [payFalse u v hL hs, Bool.false_eq_true,if_false] at H
  refine ⟨?_,?_,H.1.trans hm,A.2.2⟩
  · cases q with
    | init => simpa [hq,outward,move] using A.1
    | count k => rcases clean with hc|hc <;> simpa [hq,outward,move,hc] using A.1
  · cases q with
    | init =>
      have C : (u.rail == .x) = false := by cases h : u.rail <;> first | rfl | exact (clean h).elim
      simpa [hq,outward,move,C] using A.2.1
    | count k => rcases clean with hc|hc <;> simpa [hq,outward,move,hc] using A.2.1

/-- The pinned turn of either genuine worker, including when unrelated
upstream source service concurrently launches a different worker. -/
theorem pinned_turn_row {p c : Nat} (u v : Site p c) (q : Trip (2*c))
    (hm : u.mark=true) (hL : u.leader=false) (hR : v.leader=false)
    (hs : u.stock=false) (hq : v.rail=outward q) :
    (pairStep u v).2.rail=inward q ∧ (pairStep u v).2.residue=v.residue := by
  have A := SingletonFinish.alias_pair_exact u v hm hL hR hs
  have R := pair_geometric_fields u v
  refine ⟨?_,?_⟩
  · cases q <;> simpa [hq,outward,inward,topRail] using A.2.1
  · simpa [payFalse u v hL hs] using R.2.2

/-- Release into an ordinary retained socket with E/T. The reservation
for the door case is separate; this row never treats the matching door
as an ordinary cell. -/
theorem release_body_row {p c : Nat} (u v : Site p c) (q : Trip (2*c))
    (hm : u.mark=false) (hL : u.leader=false) (hR : v.leader=false)
    (hs : u.stock=false) (hr : v.residue=nextResidue u.residue) (hoff : v.source=.off)
    (hq : u.rail=inward q) (trail : v.rail=.e ∨ v.rail=.t) :
    (pairStep u v).1.rail=.e ∧ (pairStep u v).2.rail=inward q := by
  have H := SingletonFinish.alias_body_exact u v hm hL hR hr hs hoff
  have A := WindowA0Rows.return_release_empty_or_trail (Q:=2*c) u.rail
    (by cases q <;> simp [hq,inward]) v.rail trail
  rw [body_exact] at A
  exact ⟨H.1.trans A.1,H.2.1.trans (A.2.trans hq)⟩

/-- A matching unpaid door accepts the released Di/Dc; that same service
may launch the next count or give the actual physical birth. -/
theorem release_door_row {p c : Nat} (u v : Site p c) (q : Trip (2*c))
    (hm : u.mark=true) (hL : u.leader=false) (hR : v.leader=false)
    (hs : u.stock=false) (hq : u.rail=inward q) (hw : v.source=waitingFor q) :
    let a := serviceDoor (waitingFor q) (inward q)
    (pairStep u v).1.rail=a.left ∧
      (pairStep u v).2.source=(if a.fire then .off else a.source) ∧
      (pairStep u v).2.leader=a.fire := by
  have H := SingletonFinish.alias_pair_exact u v hm hL hR hs
  simpa only [hq,hw] using And.intro H.1 H.2.2

/-- Literal paid-first script, from the old donor, old top, and adjacent
genuine worker; responder initially ordinary. The second requested
mark is pinned even if source reset wrote X into the vacated top. -/
theorem paid_adjacent_turn {p c : Nat} (a b w : Site p c) (q : Trip (2*c))
    (hm : a.mark=true) (hp : geometricPay a b=true) (hb : b.stock=false)
    (hw : w.leader=false) (hwq : w.rail=outward q) :
    let v := (pairStep a b).2
    let t := (pairStep v w).2
    v.mark=true ∧ v.stock=false ∧ v.leader=false ∧
      t.rail=inward q ∧ t.residue=w.residue := by
  have hM := covered_pair_marks a b (fun _ => hm)
  have hB := pair_geometric_fields a b
  simp only [hp,if_true] at hM hB
  have hS := (WindowA0Rows.marked_paid_empty a b hm hb hp).2
  exact ⟨hM.2.2,hS,hB.2.2.2,
    pinned_turn_row _ w q hM.2.2 hB.2.2.2 hw hS hwq⟩

/-- Literal unpaid-first script. The requested first mark moves the
worker onto the old top, and the re-used incoming donor is still the
original disabled donor provided no guarded intervening mark occurred. -/
theorem unpaid_adjacent_turn {p c : Nat} (a b w : Site p c) (q : Trip (2*c))
    (ham : a.mark=true) (hal : a.leader=false) (has : a.stock=false)
    (hbm : b.mark=false) (hbl : b.leader=false) (hbs : b.stock=false)
    (hwl : w.leader=false)
    (hres : w.residue=nextResidue b.residue) (hoff : w.source=.off)
    (hwq : w.rail=outward q)
    (clean : match q with | .init => b.rail≠.x | .count _ => b.rail=.e ∨ b.rail=.t) :
    let z := pairStep b w
    let t := (pairStep a z.1).2
    z.2.rail=.t ∧ t.rail=inward q ∧ t.residue=b.residue := by
  have O := outward_row b w q hbm hbl hwl hbs hres hoff hwq clean
  have L := (pair_geometric_fields b w).2.1.trans hbl
  have R := (pair_geometric_fields b w).1
  have T := pinned_turn_row a _ q ham hal L has O.1
  exact ⟨O.2.1,T.1,T.2.trans R⟩

/-- Inputs of the third service; a matching door is explicitly a
pinned controller, never an E/T receiver disguised as ordinary. -/
inductive LastPort {p c : Nat} (u v : Site p c) (q : Trip (2*c)) : Prop where
  | body (hm : u.mark=false) (res : v.residue=nextResidue u.residue)
    (off : v.source=.off) (trail : v.rail=.e ∨ v.rail=.t)
  | door (hm : u.mark=true) (wait : v.source=waitingFor q)

/-- Actual third-service outcome, including the exact A1/A2/L2 door
row, with its next source and final-count birth bit. -/
def Released {p c : Nat} (u v : Site p c) (q : Trip (2*c)) : Prop :=
  if u.mark then
    let a := serviceDoor (waitingFor q) (inward q)
    (pairStep u v).1.rail=a.left ∧
      (pairStep u v).2.source=(if a.fire then .off else a.source) ∧
      (pairStep u v).2.leader=a.fire
  else (pairStep u v).1.rail=.e ∧ (pairStep u v).2.rail=inward q

theorem release_last {p c : Nat} (u v : Site p c) (q : Trip (2*c))
    (hu : u.leader=false) (hv : v.leader=false) (hs : u.stock=false)
    (hq : u.rail=inward q) (h : LastPort u v q) : Released u v q := by
  cases h with
  | body hm hr hoff ht =>
    simpa [Released,hm] using release_body_row _ _ q hm hu hv hs hr hoff hq ht
  | door hm hw =>
    simpa [Released,hm] using release_door_row _ _ q hm hu hv hs hq hw

private theorem turn_bytes {p c : Nat} (u v : Site p c)
    (hl : u.leader=false) (hs : u.stock=false) (hm : u.mark=true) :
    (pairStep u v).2.stock=v.stock ∧ (pairStep u v).2.residue=v.residue ∧
    (pairStep u v).2.mark=v.mark := by
  have hr := pair_geometric_fields u v
  have hM := covered_pair_marks u v (fun _ => hm)
  simp only [payFalse _ _ hl hs, Bool.false_eq_true, if_false] at hr hM
  exact ⟨RearFrontStock.marked_right_stock _ _ hm,hr.2.2,hM.2⟩

private theorem last_of_bytes {p c : Nat} {u v w : Site p c} {q : Trip (2*c)}
    (hr : w.residue=u.residue) (hm : w.mark=u.mark) (h : LastPort u v q) :
    LastPort w v q := by
  cases h with
  | body a r t g => exact .body (hm.trans a) (by rwa [hr]) t g
  | door a h => exact .door (hm.trans a) h

/-- All three literal selected pairs on the paid-first branch.  The
branch uses the unpaid pinned turn on the newly marked, still-empty
old top. If that turn births a selected head, it is already a favorable
exit; otherwise the third service releases or accepts exactly once. -/
theorem paid_adjacent_release {p c : Nat} (a b w v : Site p c) (q : Trip (2*c))
    (hm : a.mark=true) (hp : geometricPay a b=true) (hb : b.stock=false)
    (hw : w.leader=false) (hws : w.stock=false) (hwq : w.rail=outward q)
    (hv : v.leader=false) (port : LastPort w v q) :
    let a' := (pairStep a b).2
    let z := (pairStep a' w).2
    z.leader=true ∨ Released z v q := by
  dsimp only
  have T := paid_adjacent_turn a b w q hm hp hb hw hwq
  dsimp only at T
  obtain ⟨hM,hS,hL,hq,hres⟩ := T
  have F := turn_bytes _ w hL hS hM
  by_cases e : (pairStep (pairStep a b).2 w).2.leader=true
  · exact .inl e
  · exact .inr (release_last _ _ q (Bool.eq_false_iff.mpr e) hv
      (F.1.trans hws) hq (last_of_bytes hres F.2.2 port))

/-- All three literal pairs on the unpaid branch. The disabled donor
is the same old socket at the second hit. The E/T release always uses
the T left behind by the first service. -/
theorem unpaid_adjacent_body_release {p c : Nat} (a b w : Site p c) (q : Trip (2*c))
    (ham : a.mark=true) (hal : a.leader=false) (has : a.stock=false)
    (hbm : b.mark=false) (hbl : b.leader=false) (hbs : b.stock=false)
    (hwl : w.leader=false) (hws : w.stock=false)
    (hres : w.residue=nextResidue b.residue) (hoff : w.source=.off)
    (hwq : w.rail=outward q)
    (clean : match q with | .init => b.rail≠.x | .count _ => b.rail=.e ∨ b.rail=.t) :
    let z := pairStep b w
    let t := (pairStep a z.1).2
    t.leader=true ∨ Released t z.2 q := by
  dsimp only
  have T := unpaid_adjacent_turn a b w q ham hal has hbm hbl hbs hwl hres hoff hwq clean
  dsimp only at T
  have O := outward_row b w q hbm hbl hwl hbs hres hoff hwq clean
  have L := (pair_geometric_fields b w).2.1.trans hbl
  have E := WindowA0Rows.unstocked_nonleader_pair b w hbl hbs hws
  have F := turn_bytes a (pairStep b w).1 hal has ham
  have P := pair_ports b w
  dsimp only at P
  have pNo : (pairStep b w).2.source=.off := by
    -- An ordinary OFF responder cannot acquire controller authority,
    -- independent of the consuming and forwarding rail rows.
    have h : ∀ (r : Bool) (s l : Rail),
        (patrol r false false (.off : Source (2*c)) s l).source=.off := by
      intro r s l
      cases r <;> cases s <;> cases l <;> rfl
    have M : (stepPrefix b w).1.mark=false := by
      have K := FreshEpochAuthentication.ordinary_prefix_flags b w hbm hres hwl
      exact K.1
    have K := FreshEpochAuthentication.ordinary_prefix_flags b w hbm hres hwl
    have hp : (pairStep b w).2.source =
      (patrol false false false w.source b.rail w.rail).source := by
      simpa [selectedPatrol,pinned,M,K.2] using P.2.2
    rw [hp,hoff]
    exact h _ _ _
  have R := pair_geometric_fields b w
  simp only [payFalse b w hbl hbs,Bool.false_eq_true,if_false] at R
  have Bmark := F.2.2.trans O.2.2.1
  have Hres : (pairStep b w).2.residue=nextResidue ((pairStep a (pairStep b w).1).2.residue) := by
    rw [T.2.2,R.2.2,hres]
  by_cases e : (pairStep a (pairStep b w).1).2.leader=true
  · exact .inl e
  · exact .inr (release_last _ _ q (Bool.eq_false_iff.mpr e) O.2.2.2
      (F.1.trans E.1) T.2.1 (.body Bmark Hres pNo (.inr T.1)))

/-- Gap one: a paid incoming service visibly puts a mark on the old
door donor, whose mark was already set. Thus the caller should detect
the selected retirement before trying to use any rail transitions. -/
theorem top_launch_paid_retires {p c n : Nat} (x : Config p c n) (e : Fin n)
    (door : (x (rightNeighbor e)).mark=true)
    (pay : geometricPay (x e) (x (rightNeighbor e))=true) :
    RankPhysical.retirement x e=true := by
  simp [RankPhysical.retirement,door,pay]

/-- Gap one, no payment: the first mark turns the already-top worker;
the next mark is the real matching door service, not an ordinary hop.
If the top itself is born during the turn, the script exits earlier. -/
theorem top_launch_unpaid_release {p c : Nat} (a b v : Site p c) (q : Trip (2*c))
    (ham : a.mark=true) (hal : a.leader=false) (has : a.stock=false)
    (hbm : b.mark=true) (hbl : b.leader=false) (hbs : b.stock=false)
    (hbq : b.rail=outward q) (hv : v.leader=false) (hwait : v.source=waitingFor q) :
    let z := (pairStep a b).2
    z.leader=true ∨ Released z v q := by
  dsimp only
  have T := pinned_turn_row a b q ham hal hbl has hbq
  have F := turn_bytes a b hal has ham
  by_cases H : (pairStep a b).2.leader=true
  · exact .inl H
  · exact .inr (release_last _ _ q (Bool.eq_false_iff.mpr H) hv (F.1.trans hbs)
      T.1 (.door (F.2.2.trans hbm) hwait))

/-- The actual five socket records that determine the three-hit
release, indexed from far left guard bond i−2. -/
def Agree {p c n : Nat} (farLeft : Fin n) (x y : Config p c n) : Prop :=
  ∀ j, 1≤j → j≤5 → x (liftedSite farLeft j)=y (liftedSite farLeft j)

theorem agree_symm {p c n : Nat} {farLeft : Fin n} {x y : Config p c n}
    (h : Agree farLeft x y) : Agree farLeft y x :=
  fun j a b => (h j a b).symm

theorem agree_trans {p c n : Nat} {farLeft : Fin n} {x y z : Config p c n}
    (h : Agree farLeft x y) (h' : Agree farLeft y z) : Agree farLeft x z :=
  fun j a b => (h j a b).trans (h' j a b)

/-- A raw mark outside the guard's six-label set really stutters on
these sockets, although the executable whole ring still advances. -/
theorem outside_agrees {p c n : Nat} (x : Config p c n) (farLeft e : Fin n)
    (h : e ∉ WindowA0Return.guardLabels farLeft) : Agree farLeft (step x e) x :=
  fun j a b => WindowA0Return.step_off_guard x farLeft e j a b h

/-- The three possible requested service labels are internal to the
five-socket view, so executing one of them respects agreement of two
distinct whole-ring snapshots. -/
theorem requested_agrees {p c n : Nat} (farLeft : Fin n) (j : Nat) (hj : 1≤j) (hk : j≤3)
    {x y : Config p c n} (h : Agree farLeft x y) :
    Agree farLeft (step x (liftedSite farLeft j)) (step y (liftedSite farLeft j)) := by
  intro k ha hb
  have hu := h j hj (by omega)
  have hv := h (j+1) (by omega) (by omega)
  rw [liftedSite_succ] at hv
  simp only [step,hu,hv,h k ha hb]

/-- A lockstep padding relation: after each requested mark, arbitrary
marks outside the fixed guard may intervene. These are still literal
physical marks in the first word, not redirected marks. -/
inductive ReleasePadding {n : Nat} (farLeft : Fin n) :
    List (Fin n) → List (Fin n) → Prop where
  | nil : ReleasePadding farLeft [] []
  | outside (e : Fin n) (h : e ∉ WindowA0Return.guardLabels farLeft) {w v : List (Fin n)}
      (rest : ReleasePadding farLeft w v) : ReleasePadding farLeft (e::w) v
  | requested (j : Nat) (hj : 1≤j) (hk : j≤3) {w v : List (Fin n)}
      (rest : ReleasePadding farLeft w v) :
      ReleasePadding farLeft (liftedSite farLeft j::w) (liftedSite farLeft j::v)

/-- Any unspoiled interleaving of either release script produces the
same actual five socket records as the isolated script. No quietness,
stock or type claim is made about the exterior. -/
theorem padded_release_agrees {p c n : Nat} {farLeft : Fin n}
    {w v : List (Fin n)} (h : ReleasePadding farLeft w v) (x y : Config p c n)
    (same : Agree farLeft x y) : Agree farLeft (run x w) (run y v) := by
  induction h generalizing x y with
  | nil => exact same
  | outside e he _ ih =>
    exact ih (step x e) y (agree_trans (outside_agrees x farLeft e he) same)
  | requested j hj hk _ ih =>
    exact ih _ _ (requested_agrees farLeft j hj hk same)

/-- Two three-hit release patterns on the same six-mark guard. -/
inductive Kind where
  | paid | unpaid

def offset : Kind → Fin 3 → Nat
  | .paid, k => k.val+1
  | .unpaid, k => if k.val=1 then 1 else 2

def asked {n : Nat} (farLeft : Fin n) (s : Kind) (k : Fin 3) : Fin n :=
  liftedSite farLeft (offset s k)

theorem asked_inside {n : Nat} (farLeft : Fin n) (s : Kind) (k : Fin 3) :
    asked farLeft s k ∈ WindowA0Return.guardLabels farLeft := by
  apply List.mem_map.mpr
  refine ⟨offset s k, List.mem_range.mpr ?_, rfl⟩
  cases s <;> simp [offset]
  · have := k.isLt; omega
  · split <;> decide

abbrev PhysicalMonitor (p c n : Nat) :=
  Config p c n × WindowA0ReleaseCredit.Phase

open WindowA0ReleaseCredit in
/-- Every raw mark executes the physical pair. An exterior designated
physical exit may count as success before the selected request, whereas
a competing guarded mark ends this particular attempt in failure. -/
def monitorNext {p c n : Nat} (farLeft : Fin n) (s : Kind)
    (early : Config p c n → Fin n → Bool)
    (x : PhysicalMonitor p c n) (e : Fin n) : PhysicalMonitor p c n :=
  (step x.1 e,
    match x.2 with
    | .success => .success
    | .failed => .failed
    | .waiting k =>
      if early x.1 e then .success
      else if e=asked farLeft s k then
        if hk : k.val+1<3 then .waiting ⟨k.val+1,hk⟩ else .success
      else if e ∈ WindowA0Return.guardLabels farLeft then .failed else .waiting k)

/-- The actual raw-word release monitor implements Frame exactly. This
counts completion of the ordered script or an earlier positive exit;
authenticity of entry and the full-ledger closure are separate. -/
def release_frame {p c n : Nat} (farLeft : Fin n) (s : Kind)
    (early : Config p c n → Fin n → Bool)
    (x : PhysicalMonitor p c n) (k : Fin 3)
    (hp : x.2=.waiting k) :
    WindowA0ReleaseCredit.Frame (monitorNext farLeft s early)
      Prod.snd (WindowA0Return.guardLabels farLeft) x k := by
  open WindowA0ReleaseCredit in
  refine ⟨asked farLeft s k,asked_inside farLeft s k,?_,?_⟩
  · by_cases h : early x.1 (asked farLeft s k)=true
    · have hk : 6*score (.waiting k)≤216 := by
        have L : k.val+1≤3 := by have := k.isLt; omega
        rw [Nat.mul_comm]
        exact Nat.le_trans (by simp [score,Nat.pow_succ])
          (Nat.pow_le_pow_right (by decide : 0<6) L)
      simpa [monitorNext,hp,h,score] using hk
    · by_cases hh : k.val+1<3
      · simp [monitorNext,hp,h,hh,score,Nat.pow_succ,Nat.mul_comm]
      · have hk : k.val=2 := by have := k.isLt; omega
        simp [monitorNext,hp,h,score,hk]
  · intro e hd
    have he : e≠asked farLeft s k := fun h => hd (h ▸ asked_inside farLeft s k)
    by_cases H : early x.1 e=true <;> simp [monitorNext,hp,H,he,hd]

open WindowA0ReleaseCredit TripleRenewal in
/-- Uniform first-terminal failure bound under the unmodified scheduler
for the entered three-hit script, with the usual first-hit padding.
The script success is justified by literal prepared socket conditions. -/
theorem script_failure_mass {p c n : Nat} (farLeft : Fin n) (s : Kind)
    (early : Config p c n → Fin n → Bool) (x : Config p c n) (t : Nat) :
    216*terminalMass (monitorNext farLeft s early)
      (fun y => done y.2) (fun y => y.2=.failed) t (x,.waiting 0)≤215*n^t := by
  have hh : (WindowA0Return.guardLabels farLeft).length≤6 := by
    simp [WindowA0Return.guardLabels]
  have H := finite_credit (monitorNext farLeft s early) Prod.snd
    (WindowA0Return.guardLabels farLeft) hh (fun _ => True)
    (fun _ _ _ _ _ => trivial) (fun y k _ => release_frame farLeft s early y k) t (x,.waiting 0) trivial
  change _ + 1*n^t ≤ 216*n^t at H
  rw [Nat.one_mul] at H
  omega

#print axioms release_frame

#print axioms paid_adjacent_turn
#print axioms unpaid_adjacent_turn
#print axioms paid_adjacent_release
#print axioms unpaid_adjacent_body_release
#print axioms top_launch_unpaid_release
#print axioms padded_release_agrees
end L4.WindowA0Release
