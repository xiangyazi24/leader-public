import Leader.L4.Height.ObserverBits
import Leader.L4.Height.ObserverLine
import Leader.L4.Height.ObserverTrip

/-! Literal physical realization of the generated trip. -/
namespace L4.Height.ObserverMachine

open AllSizeProtocol ObserverDirty ObserverGeometry ObserverPhysical ObserverLine ObserverBits
open ObserverTrip (Stage Shape advance HasCarrier)
open ObserverDirty.Decoded (slot terminalSeen)

noncomputable section

variable {a : LargeParams} {n : Nat}
variable {r : Fin n} {b : LargeRows a} {x : Ring a n}

abbrev FixedRing (b : LargeRows a) (r : Fin n) := {x : Ring a n // Fixed b x r}

def seen (r : Fin n) (x : Ring a n) (i : Nat) : Bool := token r x i == 3

private theorem slot_front_iff (t : Nat) :
    slot t=.front ↔ BStarLapTransfer.front t=true := by
  by_cases h : BStarLapTransfer.front t=true
  · simp [slot,h]
  · rw [slot,if_neg h,Bool.eq_false_iff.mpr h]
    by_cases d : t=4
    · rw [if_pos d]
      decide
    · by_cases p : t=5
      · rw [if_neg d,if_pos p]
        decide
      · by_cases trail : t=1
        · rw [if_neg d,if_neg p,if_pos trail]
          decide
        · rw [if_neg d,if_neg p,if_neg trail]
          decide

private theorem waiting_iff {t : Nat} : Decoded.control t=.waiting ↔ t=1 := by
  by_cases w : t=1
  · simp [Decoded.control,w]
  · by_cases p : t=2 <;> simp [Decoded.control,w,p]

private theorem pending_iff {t : Nat} : Decoded.control t=.pending ↔ t=2 := by
  by_cases w : t=1
  · simp [Decoded.control,w]
  · by_cases p : t=2 <;> simp [Decoded.control,w,p]

private theorem issue_of_control {t : Nat} (bound : t≤2) (h : Decoded.control t=.issue) : t=0 := by
  have wait : t≠1 := by intro t1; simp [Decoded.control,t1] at h
  have pend : t≠2 := by intro t2; simp [Decoded.control,t2] at h
  omega

private theorem token_front {j : Nat} (h : (line r x).slot j=.front) :
    BStarLapTransfer.front (token r x j)=true :=
  (slot_front_iff _).mp h

theorem literal_pulse (hp : 0<a.p) (h : Fixed b x r) (k : Fin n) :
    pulse b hp x (edge r k)=commitBit (slots x (pos r k.val)) (decide (k.val=0)) := by
  by_cases first : k.val=0
  · have eq := (root_source r k).2 first
    simp only [commitBit,first,decide_true,Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    rw [incoming_pulse b hp h,beq_iff_eq,responder,eq]
    simp [ObserverGeometry.first]
  · have no : rightNeighbor (edge r k)≠r := by
      rw [responder]
      exact fun he => first ((root_source r k).1 he)
    simp only [commitBit,first,decide_false,Bool.false_and]
    apply Bool.eq_false_iff.mpr
    intro bad
    exact no ((incoming_pulse b hp h _).mp bad).1

theorem post_marks (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)
    (h : Fixed b x r) (k : Fin n) :
    let e := edge r k
    let j := pos r k.val
    let y := next b x e
    (pub hp y e).mark =
      ((ordinaryMarks hp x e).1 || commitBit (slots x j) (decide (k.val=0))) ∧
    (pub hp y j).mark = (ordinaryMarks hp x e).2 := by
  dsimp only
  rw [(joined_step hn b hp bind x (edge r k)).2,literal_pulse hp h k]
  have neq : pos r k.val≠edge r k := by
    rw [← responder]
    exact endpoints_ne hn _
  constructor
  · simp only [seeded,step,if_pos rfl,ordinaryMarks,if_true]
  · simp only [seeded,step,if_neg neq,responder,ordinaryMarks,if_true]

private theorem token_left (r k : Fin n) (x : Ring a n) :
    token r x (k.val+1)=leftSlot (decide (k.val+1=n)) (slots x (edge r k)) := by
  have K := k.isLt
  by_cases last : k.val+1=n
  · have root := (root_dest r k).mpr last
    simp [token,last,leftSlot,root]
  · have sh : k.val+1<n := by omega
    simp [token,sh,last,leftSlot,edge]

private theorem token_first (r : Fin n) (x : Ring a n) :
    token r x 0=(slots x r).a := by
  have posn := Nat.zero_lt_of_lt r.isLt
  simp [token,posn,ObserverGeometry.first]

theorem launch_eq (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)
    (h : Fixed b x r) (k : Fin n) (launch : Launches (line r x) k) :
    let e := edge r k
    let j := pos r k.val
    seen r (next b x e) 0 =
      seesLeft 2 (before hp x e) (ordinaryMarks hp x e)
        (commitBit (slots x j) (decide (k.val=0))) := by
  dsimp only
  have atRoot := (root_dest r k).mpr launch.1
  have issue := issue_of_control (Decoded.decode_bounded (BStarLapTransfer.get (x r).guard)).2.2
    launch.2
  have pair := congrArg Prod.fst (pair_at hn b hp bind h k)
  simp only [launch.1,decide_true] at pair
  have eq := launch_bit (slots x (edge r k)) (slots x (pos r k.val))
    (decide (k.val=0)) (before hp x (edge r k)) (ordinaryMarks hp x (edge r k))
    (by rw [atRoot]; exact issue)
  change (slots (next b x (edge r k)) (edge r k)) =
    leftAfter (slots x (edge r k)) (slots x (pos r k.val))
      true (decide (k.val=0)) (before hp x (edge r k)) (ordinaryMarks hp x (edge r k)) at pair
  have tokenEq := congrArg BStarLapTransfer.Site.a
    ((congrArg (slots (next b x (edge r k))) atRoot.symm).trans pair)
  unfold seen
  rw [token_first,tokenEq,eq]
  cases seesLeft 2 (before hp x (edge r k)) (ordinaryMarks hp x (edge r k))
    (commitBit (slots x (pos r k.val)) (decide (k.val=0))) <;> rfl

private theorem flag_eq {c : Nat} {v : Bool} (h : c=BStarLapTransfer.flag v) :
    (c==3)=v := by
  subst c
  cases v <;> rfl

/-- On an outward-to-outward mark the front hops, observes the selected
left endpoint while stationary, or is outside the selected bond. -/
theorem outward_read (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)
    (h : Fixed b x r) (k : Fin n) {j l : Nat}
    (good : Shape n (line r x) (.out j))
    (stage : advance (line r x) k (.out j)=.out l) :
    let e := edge r k
    let v := pos r k.val
    let y := next b x e
    let μ := before hp x e
    let μ' := ordinaryMarks hp x e
    let seed := commitBit (slots x v) (decide (k.val=0))
    (j=k.val ∧ l=k.val+1 ∧ seen r y l=seesHop (token r x j) μ μ' seed) ∨
    (l=j ∧ pos r l=e ∧ seen r y l=seesLeft (token r x j) μ μ' seed) ∨
    (l=j ∧ pos r l≠e ∧ pos r l≠v ∧ seen r y l=seen r x j) := by
  dsimp only
  let e := edge r k
  let v := pos r k.val
  let y := next b x e
  let μ := before hp x e
  let μ' := ordinaryMarks hp x e
  let rb := decide (k.val=0)
  let ra := decide (k.val+1=n)
  have P : slots y e=leftAfter (slots x e) (slots x v) ra rb μ μ' :=
    congrArg Prod.fst (pair_at hn b hp bind h k)
  have K := k.isLt
  by_cases walks : k.val=j
  · subst j
    have L : l=k.val+1 := by simpa [advance] using stage.symm
    subst l
    left
    refine ⟨rfl,rfl,?_⟩
    have code : token r x k.val=(slots x v).a := by simp [token,K,v]
    have front := token_front good.2.2.1
    rw [code] at front
    have H := hop_bit (slots x e) (slots x v) ra rb μ μ' front
    unfold seen
    rw [token_left r k y,P,code]
    exact flag_eq H
  · have stays : ¬(k.val=0 ∧ j=n) := by
      intro obs
      rw [advance,if_neg walks,if_pos obs] at stage
      exact nomatch stage
    have L : l=j := by simpa [advance,walks,stays] using stage.symm
    subst l
    have bound := good.2.1
    by_cases left : pos r j=e
    · right; left
      refine ⟨rfl,left,?_⟩
      by_cases prev : j=k.val+1
      · subst j
        have code := token_left r k x
        have F : BStarLapTransfer.front (leftSlot ra (slots x e))=true :=
          code ▸ token_front good.2.2.1
        have trail := good.2.2.2 k.val (by omega : k.val<k.val+1)
        rw [old_source r k x] at trail
        have noFront : BStarLapTransfer.front (slots x v).a=false := by
          apply Bool.eq_false_iff.mpr
          intro f
          have clash := (slot_front_iff _).2 f
          rw [trail] at clash
          contradiction
        have R := left_stay_bit (slots x e) (slots x v) ra rb μ μ' F noFront
        unfold seen
        rw [token_left r k y,P,code]
        exact flag_eq R
      · have strictly : j<n := by
          by_cases isTerm : j=n
          · have q : e=r := left.symm.trans (by rw [isTerm,ObserverGeometry.terminal])
            have eq := (root_dest r k).1 q
            exact (prev (isTerm.trans eq.symm)).elim
          · omega
        have last : k.val+1=n := by
          by_cases H : k.val+1=n
          · exact H
          · exact (prev (pos_inj r strictly (by omega : k.val+1<n) left)).elim
        have root : e=r := (root_dest r k).2 last
        have zero : j=0 :=
          pos_inj r strictly (by omega : 0<n) (left.trans (root.trans (ObserverGeometry.first r).symm))
        subst j
        have code : token r x 0=(slots x e).a :=
          (token_first r x).trans (congrArg (fun i => (slots x i).a) root.symm)
        have F : BStarLapTransfer.front (slots x e).a=true := by
          rw [← code]
          exact token_front good.2.2.1
        have W : (slots x e).pc=1 := by
          rw [root]
          exact waiting_iff.mp good.1
        have R := door_stay_bit (slots x e) (slots x v) rb μ μ' W F
        have localPair : slots y e=leftAfter (slots x e) (slots x v) true rb μ μ' := by
          simpa only [ra,last,decide_true] using P
        have out := congrArg BStarLapTransfer.Site.a ((congrArg (slots y) root.symm).trans localPair)
        unfold seen
        rw [token_first,out,code]
        exact flag_eq R
    · have right : pos r j≠v := by
        intro eq
        by_cases small : j<n
        · exact walks (pos_inj r small K eq).symm
        · have J : j=n := by omega
          have q : v=r := eq.symm.trans (by rw [J,ObserverGeometry.terminal])
          exact stays ⟨(root_source r k).1 q,J⟩
      right; right
      refine ⟨rfl,left,right,?_⟩
      by_cases small : j<n
      · unfold seen
        simp only [token,if_pos small,frame b x r k _ left right]
      · have J : j=n := by omega
        subst j
        rw [ObserverGeometry.terminal] at left right
        unfold seen
        simp only [token,if_neg (Nat.lt_irrefl n),frame b x r k _ left right]

private theorem seesLeft_post {t : Nat} {μ μ' : Pair Bool} {seed : Bool}
    (hit : (μ'.1 || seed)=true) : seesLeft t μ μ' seed=true := by
  rcases Bool.or_eq_true_iff.mp hit with h|h <;> simp [seesLeft,h]

private theorem seesHop_post {t : Nat} {μ μ' : Pair Bool} {seed : Bool}
    (hit : (μ'.1 || seed)=true) : seesHop t μ μ' seed=true := by
  rcases Bool.or_eq_true_iff.mp hit with h|h <;> simp [seesHop,h]

theorem outward_observes (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)
    (h : Fixed b x r) (k : Fin n) {j l : Nat}
    (good : Shape n (line r x) (.out j))
    (stage : advance (line r x) k (.out j)=.out l) :
    let e := edge r k
    let y := next b x e
    seen r x j=true ∨
      (pos r l=e ∧ (pub hp y e).mark=true) ∨
      (pos r l=rightNeighbor e ∧ (pub hp y (rightNeighbor e)).mark=true) ∨
      (pos r l=e ∧ pos r j=rightNeighbor e ∧ crosses hp x e=true) →
    seen r y l=true := by
  dsimp only
  have localMarks := post_marks hn b hp bind h k
  have read := outward_read hn b hp bind h k good stage
  have unequal := endpoints_ne hn (edge r k)
  intro observed
  rcases read with ⟨_, L, eq⟩ | ⟨same, sameLeft, eq⟩ | ⟨_, notLeft, notRight, eq⟩
  · rcases observed with old | ⟨_,left⟩ | ⟨right,_⟩ | ⟨_,_,cross⟩
    · have bit : (token r x j==3)=true := old
      simp [eq,seesHop,bit]
    · rw [eq]
      exact seesHop_post (localMarks.1.symm.trans left)
    · exact (unequal (right.symm.trans (congrArg (pos r) L))).elim
    · have hit : crossing (before hp x (edge r k)) (ordinaryMarks hp x (edge r k))=true := cross
      simp [eq,seesHop,hit]
  · rcases observed with old | ⟨_,left⟩ | ⟨right,_⟩ | ⟨_,right,_⟩
    · have bit : (token r x j==3)=true := old
      simp [eq,seesLeft,bit]
    · rw [eq]
      exact seesLeft_post (localMarks.1.symm.trans left)
    · exact (unequal (right.symm.trans sameLeft)).elim
    · exact (unequal (right.symm.trans ((congrArg (pos r) same.symm).trans sameLeft))).elim
  · rcases observed with old | ⟨left,_⟩ | ⟨right,_⟩ | ⟨left,_,_⟩
    · exact eq.trans old
    · exact (notLeft left).elim
    · exact (notRight (right.trans (responder r k))).elim
    · exact (notLeft left).elim

private theorem marked_next (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)
    (x : Ring a n) (e i : Fin n) (old : (pub hp x i).mark=true) :
    ∃ j, (pub hp (next b x e) j).mark=true :=
  ObserverTrip.carrier_nonempty_step (carrier_step hn b hp bind x e) ⟨i,old⟩

theorem outward_sound (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)
    (h : Fixed b x r) (k : Fin n) {j l : Nat}
    (good : Shape n (line r x) (.out j))
    (stage : advance (line r x) k (.out j)=.out l)
    (new : seen r (next b x (edge r k)) l=true) :
    seen r x j=true ∨ ∃ i, (pub hp (next b x (edge r k)) i).mark=true := by
  have marks := post_marks hn b hp bind h k
  let e := edge r k
  let v := pos r k.val
  have right (hm : (ordinaryMarks hp x e).2=true) :
      ∃ i, (pub hp (next b x e) i).mark=true := ⟨v,marks.2.trans hm⟩
  have left (hm : ((ordinaryMarks hp x e).1 ||
      commitBit (slots x v) (decide (k.val=0)))=true) :
      ∃ i, (pub hp (next b x e) i).mark=true := ⟨e,marks.1.trans hm⟩
  rcases outward_read hn b hp bind h k good stage with ⟨_,_,eq⟩ | ⟨_,_,eq⟩ | ⟨_,_,_,eq⟩
  · rw [eq] at new
    simp only [seesHop,Bool.or_eq_true] at new
    rcases new with ((((old|atOld)|atNew)|pulse)|swap)
    · exact .inl old
    · exact .inr (marked_next hn b hp bind x e _ atOld)
    · exact .inr (left (Bool.or_eq_true_iff.mpr (.inl atNew)))
    · exact .inr (left (Bool.or_eq_true_iff.mpr (.inr pulse)))
    · simp only [crossing,Bool.and_eq_true] at swap
      exact .inr (right swap.2)
  · rw [eq] at new
    simp only [seesLeft,Bool.or_eq_true] at new
    rcases new with (((old|atOld)|atNew)|pulse)
    · exact .inl old
    · exact .inr (marked_next hn b hp bind x e _ atOld)
    · exact .inr (left (Bool.or_eq_true_iff.mpr (.inl atNew)))
    · exact .inr (left (Bool.or_eq_true_iff.mpr (.inr pulse)))
  · exact .inl (eq.symm.trans new)

theorem launch_observes (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)
    (h : Fixed b x r) (k : Fin n) (launch : Launches (line r x) k)
    (post : (pub hp (next b x (edge r k)) r).mark=true) :
    seen r (next b x (edge r k)) 0=true := by
  have root := (root_dest r k).2 launch.1
  rw [launch_eq hn b hp bind h k launch]
  have H := (post_marks hn b hp bind h k).1
  have yes : (pub hp (next b x (edge r k)) (edge r k)).mark=true :=
    (congrArg (fun i => (pub hp (next b x (edge r k)) i).mark) root).trans post
  exact seesLeft_post (H.symm.trans yes)

theorem launch_sound (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)
    (h : Fixed b x r) (k : Fin n) (launch : Launches (line r x) k)
    (positive : seen r (next b x (edge r k)) 0=true) :
    ∃ i, (pub hp (next b x (edge r k)) i).mark=true := by
  rw [launch_eq hn b hp bind h k launch] at positive
  simp only [seesLeft,Bool.or_eq_true] at positive
  let e := edge r k
  have H := (post_marks hn b hp bind h k).1
  rcases positive with (((impossible|atOld)|atNew)|seed)
  · contradiction
  · exact marked_next hn b hp bind x e e atOld
  · exact ⟨e,H.trans (Bool.or_eq_true_iff.mpr (.inl atNew))⟩
  · exact ⟨e,H.trans (Bool.or_eq_true_iff.mpr (.inr seed))⟩

private theorem turn_eq (hp : 0<a.p) (k : Fin n) (first : k.val=0) :
    ObserverLine.turn hp r x k = (seen r x n || (before hp x (edge r k)).2 ||
      (ordinaryMarks hp x (edge r k)).2) := by
  have root := (root_source r k).2 first
  simp [ObserverLine.turn,terminalSeen,seen,token,root]

theorem turn_sound (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)
    (h : Fixed b x r) (k : Fin n) (first : k.val=0)
    (positive : ObserverLine.turn hp r x k=true) :
    seen r x n=true ∨ ∃ i, (pub hp (next b x (edge r k)) i).mark=true := by
  rw [turn_eq hp k first] at positive
  simp only [Bool.or_eq_true] at positive
  rcases positive with ((old|atOld)|atNew)
  · exact .inl old
  · exact .inr (marked_next hn b hp bind x _ _ atOld)
  · exact .inr ⟨pos r k.val,(post_marks hn b hp bind h k).2.trans atNew⟩

/-- The observer executes the packed transition on the forward-closed
class with a fixed private reference. -/
def machine (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)
    (r : Fin n) : ObserverTrip.Machine (FixedRing b r) r where
  next x k := ⟨next b x.val (edge r k),fixed_step x.property _⟩
  line x := line r x.val
  carrier x i := (pub hp x.val i).mark
  seen x j := seen r x.val j
  turnBit x k := ObserverLine.turn hp r x.val k
  exchange x k := crosses hp x.val (edge r k)
  seed x k := pulse b hp x.val (edge r k)
  line_update x k := update hn b hp bind x.property k
  carrier_step x k := carrier_step hn b hp bind x.val (edge r k)
  seed_exact x k := by
    rw [incoming_pulse b hp x.property, responder, root_source]
    simp only [line,pending_iff]
  launch_observes x k h := launch_observes hn b hp bind x.property k h
  front_observes x k _ _ h stage := outward_observes hn b hp bind x.property k h stage
  turn_observes x k _ first positive := by
    simp [turn_eq hp k first,positive]
  launch_sound x k h := launch_sound hn b hp bind x.property k h
  front_sound x k _ _ h stage := outward_sound hn b hp bind x.property k h stage
  turn_sound x k _ first := turn_sound hn b hp bind x.property k first
  seed_marks x k positive := by
    have hit := (literal_pulse hp x.property k).symm.trans positive
    exact ⟨edge r k,(post_marks hn b hp bind x.property k).1.trans
      (Bool.or_eq_true_iff.mpr (.inr hit))⟩

end
end L4.Height.ObserverMachine
