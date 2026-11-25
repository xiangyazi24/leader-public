import Leader.L4.Height.ObserverGeometry
import Leader.L4.Height.ObserverDirty

/-! Carrier observation during a generated observer lap. The front is
indexed counterclockwise from the source. A surviving carrier is lifted
clockwise from the same source until its first encounter with the front. -/
namespace L4.Height.ObserverTrip

/-- Physical position of a front after (k) outward hops. The initial
door and final terminal are distinct slots at this same physical site. -/
abbrev lapSite {n : Nat} (root : Fin n) (k : Nat) := ObserverGeometry.pos root k

theorem lapSite_link {n : Nat} (root : Fin n) {k : Nat} (hk : k<n) :
    rightNeighbor (lapSite root (k+1)) = lapSite root k :=
  ObserverGeometry.responder root ⟨k,hk⟩

/-- A marked carrier still strictly precedes the front in the lift.
The lift starts immediately clockwise from the source and ends at the source. -/
def Separated {n : Nat} (root : Fin n) (carrier : Fin n → Bool) (k : Nat) : Prop :=
  ∃ j, k+j<n ∧ carrier (liftedSite root j)=true

/-- The tracked carrier either survives at its old site, or the selected
edge deletes its initiator's ordinary mark and keeps the responder marked.
The Boolean exchange signal is read before the observer's seed OR. -/
def CarrierMove {n : Nat} (e : Fin n) (before after : Fin n → Bool)
    (exchange : Bool) : Prop :=
  ∀ i, before i=true →
    after i=true ∨ (i=e ∧ after (rightNeighbor e)=true ∧ exchange=true)

theorem carrier_nonempty_step {n : Nat} {e : Fin n} {before after : Fin n → Bool}
    {exchange : Bool} (step : CarrierMove e before after exchange)
    (hasCarrier : ∃ i, before i=true) : ∃ i, after i=true := by
  obtain ⟨i, hi⟩ := hasCarrier
  rcases step i hi with h | ⟨_, h, _⟩
  · exact ⟨i,h⟩
  · exact ⟨rightNeighbor e,h⟩

/-- A fresh launch already sees a carrier at the source. Otherwise a
carrier elsewhere begins strictly before the front in the lift. -/
theorem initial_separation {n : Nat} {root : Fin n} {carrier : Fin n → Bool}
    (hasCarrier : ∃ i, carrier i=true) :
    carrier root=true ∨ Separated root carrier 0 := by
  by_cases atRoot : carrier root=true
  · exact .inl atRoot
  · obtain ⟨i, hi⟩ := hasCarrier
    obtain ⟨j, hj, hji⟩ := liftedSite_of_site root i
    exact .inr ⟨j, by omega, hji.symm ▸ hi⟩

/-- The front stays in its slot or moves counterclockwise on the
selected edge. Only outward transitions, before any terminal turn,
are included. -/
inductive Outward {n : Nat} (root e : Fin n) : Nat → Nat → Prop
  | stay (k : Nat) : Outward root e k k
  | hop {k : Nat} (left : lapSite root (k+1)=e) : Outward root e k (k+1)

/-- Every first encounter is seen at a touched post-mark vertex, or
is the opposite crossing on the very edge the front traverses. -/
theorem separation_step {n : Nat} {root e : Fin n} {before after : Fin n → Bool}
    {exchange : Bool} {k k' : Nat} (old : Separated root before k)
    (front : Outward root e k k') (carrier : CarrierMove e before after exchange) :
    Separated root after k' ∨
      (lapSite root k'=e ∧ after e=true) ∨
      (lapSite root k'=rightNeighbor e ∧ after (rightNeighbor e)=true) ∨
      (lapSite root k'=e ∧ lapSite root k=rightNeighbor e ∧ exchange=true) := by
  obtain ⟨j,hj,hmark⟩ := old
  have hk : k<n := by omega
  rcases carrier _ hmark with same | ⟨oldLeft,newRight,crossed⟩
  · cases front with
    | stay =>
      exact .inl ⟨j,hj,same⟩
    | hop hl =>
      by_cases hs : k+1+j<n
      · exact .inl ⟨j,hs,same⟩
      · have eq : lapSite root (k+1)=liftedSite root j := by
          change liftedSite root (n-(k+1))=_
          rw [show n-(k+1)=j by omega]
        exact .inr (.inl ⟨hl, (eq.symm.trans hl) ▸ same⟩)
  · have newPos : liftedSite root (j+1)=rightNeighbor e := by
      rw [liftedSite_succ,oldLeft]
    have newMark : after (liftedSite root (j+1))=true := newPos.symm ▸ newRight
    cases front with
    | stay =>
      by_cases hs : k+(j+1)<n
      · exact .inl ⟨j+1,hs,newMark⟩
      · have eq : lapSite root k=liftedSite root (j+1) := by
          change liftedSite root (n-k)=_
          rw [show n-k=j+1 by omega]
        exact .inr (.inr (.inl ⟨eq.trans newPos,newRight⟩))
    | hop hl =>
      by_cases hs : k+1+(j+1)<n
      · exact .inl ⟨j+1,hs,newMark⟩
      · by_cases he : k+1+(j+1)=n
        · have eq : lapSite root (k+1)=liftedSite root (j+1) := by
            change liftedSite root (n-(k+1))=_
            rw [show n-(k+1)=j+1 by omega]
          exact .inr (.inr (.inl ⟨eq.trans newPos,newRight⟩))
        · exact .inr (.inr (.inr ⟨hl, by rw [← hl, lapSite_link root hk], crossed⟩))

/-- At the terminal a surviving carrier has already been observed.
There is no strictly preceding lift after all outward hops. -/
theorem terminal_observed {n : Nat} {root : Fin n} {carrier : Fin n → Bool} {seen : Bool}
    (h : seen=true ∨ Separated root carrier n) : seen=true := by
  rcases h with positive | ⟨j,hj,_⟩
  · exact positive
  · omega

section Line

open ObserverDirty

def TrailBelow (x : Line) (j : Nat) : Prop :=
  ∀ i<j, x.slot i=.trail

def EmptyAbove (x : Line) (j n : Nat) : Prop :=
  ∀ i, j<i → i≤n → x.slot i=.empty

def EmptyLine (x : Line) (n : Nat) : Prop :=
  ∀ i≤n, x.slot i=.empty

inductive Stage where
  | idle | out (j : Nat) | back (j : Nat) | pending
  deriving DecidableEq

def Shape (n : Nat) (x : Line) : Stage → Prop
  | .idle => x.pc=.issue ∧ EmptyLine x n
  | .out j => x.pc=.waiting ∧ j≤n ∧ x.slot j=.front ∧ TrailBelow x j
  | .back j => x.pc=.waiting ∧ j≤n ∧
      (x.slot j=.negative ∨ x.slot j=.positive) ∧ TrailBelow x j ∧ EmptyAbove x j n
  | .pending => x.pc=.pending ∧ EmptyLine x n

def rank (n : Nat) : Stage → Nat
  | .idle => 0
  | .out j => 2*n+3-j
  | .back j => j+2
  | .pending => 1

/-- Ghost cursor on the raw mark. The selected link, terminal, and
controller are all served from the same old state. -/
def advance {n : Nat} (x : Line) (k : Fin n) : Stage → Stage
  | .idle => if (k : Nat)+1=n then .out 0 else .idle
  | .out j =>
      if (k : Nat)=j then .out (j+1)
      else if (k : Nat)=0 ∧ j=n then .back n else .out j
  | .back j =>
      if (k : Nat)+1=j then .back k
      else if j=0 ∧ (k : Nat)+1=n then
        if x.slot 0=.negative then .pending else .idle
      else .back j
  | .pending => if (k : Nat)=0 then .idle else .pending

theorem shape_after_launch {n : Nat} (hn : 1<n) (x : Line) (k : Fin n) (seen : Bool)
    (launch : Launches x k) : Shape n (ObserverDirty.move x k seen) (.out 0) := by
  have shape := move_launch (by omega) x k seen launch
  exact ⟨shape.2,Nat.zero_le _,shape.1,fun i hi => (Nat.not_lt_zero i hi).elim⟩

private theorem waiting_while_door_holds {n : Nat} {x : Line} (k : Fin n) (seen : Bool)
    (waiting : x.pc=.waiting) (active : x.slot 0=.front ∨ x.slot 0=.trail) :
    (ObserverDirty.move x k seen).pc=.waiting := by
  rcases active with h|h <;> simp [ObserverDirty.move,waiting,h,door,commit]

private theorem trails_keep {n j : Nat} {x : Line} (k : Fin n) (seen : Bool)
    (waiting : x.pc=.waiting) (old : TrailBelow x j) (bound : j≤n)
    (boundary : (k : Nat)+1=j → (hop (x.slot k) (x.slot ((k : Nat)+1))).1=.trail) :
    TrailBelow (ObserverDirty.move x k seen) j := by
  intro i hi
  by_cases left : i=(k : Nat)
  · subst i
    rw [move_left]
    by_cases edge : (k : Nat)+1=j
    · exact boundary edge
    · simp [hop, old _ hi, old ((k : Nat)+1) (by omega)]
  · by_cases right : i=(k : Nat)+1
    · subst i
      rw [move_right]
      rw [old (k : Nat) (by omega),old ((k : Nat)+1) hi] <;> rfl
    · have noTerm : ¬((k : Nat)=0 ∧ i=n) := by omega
      by_cases atDoor : (k : Nat)+1=n ∧ i=0
      · obtain ⟨last,rfl⟩ := atDoor
        rw [move_door (by omega) x k seen last,waiting,old _ hi] <;> rfl
      · simpa only [ObserverDirty.move,if_neg left,if_neg right,if_neg noTerm,if_neg atDoor] using old i hi

private theorem empty_suffix_keep {n j : Nat} {x : Line} (k : Fin n) (seen : Bool)
    (old : EmptyAbove x j n)
    (boundary : (k : Nat)=j → (hop (x.slot k) (x.slot ((k : Nat)+1))).2=.empty) :
    EmptyAbove (ObserverDirty.move x k seen) j n := by
  intro i ahead bound
  have kBound := k.isLt
  by_cases left : i=(k : Nat)
  · subst i
    rw [move_left]
    simp [hop, old _ ahead bound, old ((k : Nat)+1) (by omega) (by omega)]
  · by_cases right : i=(k : Nat)+1
    · subst i
      rw [move_right]
      by_cases h : (k : Nat)=j
      · exact boundary h
      · simp [hop, old k (by omega) (by omega), old _ ahead bound]
    · have noDoor : ¬((k : Nat)+1=n ∧ i=0) := by omega
      by_cases turn : (k : Nat)=0 ∧ i=n
      · obtain ⟨first,eq⟩ := turn
        subst i
        rw [move_terminal (by omega) x k seen first,old n ahead bound] <;> rfl
      · simpa only [ObserverDirty.move,if_neg left,if_neg right,if_neg turn,if_neg noDoor] using old i ahead bound

theorem outward_shape_step {n j : Nat} (hn : 1<n) {x : Line}
    (k : Fin n) (seen : Bool) (good : Shape n x (.out j)) :
    Shape n (ObserverDirty.move x k seen) (advance x k (.out j)) := by
  obtain ⟨waiting,bound,front,trail⟩ := good
  have kBound := k.isLt
  have held : (ObserverDirty.move x k seen).pc=.waiting := by
    apply waiting_while_door_holds k seen waiting
    by_cases atDoor : j=0
    · exact .inl (atDoor ▸ front)
    · exact .inr (trail 0 (by omega))
  have prefixHeld : TrailBelow (ObserverDirty.move x k seen) j :=
    trails_keep k seen waiting trail bound fun edge => by simp [hop, edge, front, trail k (by omega)]
  by_cases hopNow : (k : Nat)=j
  · have markedTrail : (ObserverDirty.move x k seen).slot j=.trail := by
      rw [←hopNow,move_left,hopNow]
      simp [hop,front]
    have frontNext : (ObserverDirty.move x k seen).slot (j+1)=.front := by
      rw [←hopNow,move_right,hopNow]
      simp [hop,front]
    rw [advance,if_pos hopNow]
    refine ⟨held,by omega,frontNext,?_⟩
    intro i hi
    by_cases endpoint : i=j
    · exact endpoint.symm ▸ markedTrail
    · exact prefixHeld i (by omega)
  · by_cases turn : (k : Nat)=0 ∧ j=n
    · obtain ⟨first,eq⟩ := turn
      subst j
      rw [advance,if_neg hopNow,if_pos ⟨first,rfl⟩]
      refine ⟨held,Nat.le_refl _,?_,prefixHeld,fun i low high => False.elim (by omega)⟩
      have effect : (ObserverDirty.move x k seen).slot n = if seen then .positive else .negative := by
        rw [move_terminal (by omega) x k seen first,front]
        rfl
      rw [effect]
      cases seen <;> simp
    · rw [advance,if_neg hopNow,if_neg turn]
      have frontHeld : (ObserverDirty.move x k seen).slot j=.front := by
        by_cases prev : (k : Nat)+1=j
        · rw [←prev,move_right,prev]
          simp [hop, front, trail k (by omega)]
        · by_cases source : (k : Nat)+1=n ∧ j=0
          · obtain ⟨last,rfl⟩ := source
            rw [move_door (by omega) x k seen last,waiting,front] <;> rfl
          · simpa only [ObserverDirty.move,if_neg (Ne.symm hopNow),if_neg (Ne.symm prev),
              if_neg turn,if_neg source] using front
      exact ⟨held,bound,frontHeld,prefixHeld⟩

private theorem clear_stays_clear {n : Nat} {x : Line} (k : Fin n) (seen : Bool)
    (old : EmptyLine x n)
    (noLaunch : (k : Nat)+1=n → x.pc≠.issue) :
    EmptyLine (ObserverDirty.move x k seen) n := by
  intro i hi
  have kBound := k.isLt
  have link : hop (x.slot k) (x.slot ((k : Nat)+1))=(.empty,.empty) := by
    rw [old k (by omega),old ((k : Nat)+1) (by omega)]
    rfl
  by_cases left : i=(k : Nat)
  · subst i
    rw [move_left,link]
  · by_cases right : i=(k : Nat)+1
    · subst i
      rw [move_right,link]
    · by_cases atTerm : (k : Nat)=0 ∧ i=n
      · obtain ⟨first,eq⟩ := atTerm
        subst i
        rw [move_terminal (by omega) x k seen first,old n hi] <;> rfl
      · by_cases atDoor : (k : Nat)+1=n ∧ i=0
        · obtain ⟨last,rfl⟩ := atDoor
          have ne := noLaunch last
          cases pc : x.pc with
          | issue => exact (ne pc).elim
          | waiting => rw [move_door (by omega) x k seen last,pc,old 0 hi] <;> rfl
          | pending => rw [move_door (by omega) x k seen last,pc,old 0 hi] <;> rfl
        · simpa only [ObserverDirty.move,if_neg left,if_neg right,if_neg atTerm,if_neg atDoor] using old i hi

theorem idle_shape_step {n : Nat} (hn : 1<n) {x : Line} (k : Fin n) (seen : Bool)
    (good : Shape n x .idle) : Shape n (ObserverDirty.move x k seen) (advance x k .idle) := by
  obtain ⟨issue,empty⟩ := good
  by_cases last : (k : Nat)+1=n
  · rw [advance,if_pos last]
    exact shape_after_launch hn x k seen ⟨last,issue⟩
  · rw [advance,if_neg last]
    exact ⟨by simp [ObserverDirty.move,last,issue,commit],
      clear_stays_clear k seen empty (fun h => (last h).elim)⟩

theorem pending_shape_step {n : Nat} (hn : 1<n) {x : Line} (k : Fin n) (seen : Bool)
    (good : Shape n x .pending) : Shape n (ObserverDirty.move x k seen) (advance x k .pending) := by
  obtain ⟨pending,empty⟩ := good
  have staysEmpty := clear_stays_clear k seen empty (fun _ => by simp [pending])
  by_cases first : (k : Nat)=0
  · have notLast : (1 : Nat)≠n := by omega
    rw [advance,if_pos first]
    exact ⟨by simp [ObserverDirty.move,first,notLast,pending,commit],staysEmpty⟩
  · rw [advance,if_neg first]
    exact ⟨by simp [ObserverDirty.move,first,pending,door],staysEmpty⟩

private theorem hop_reply_left {d : Slot} (reply : d=.negative ∨ d=.positive) :
    hop d .empty=(d,.empty) := by
  rcases reply with h|h <;> simp [h,hop]

private theorem hop_reply_right {d : Slot} (reply : d=.negative ∨ d=.positive) :
    hop .trail d=(d,.empty) := by
  rcases reply with h|h <;> simp [h,hop]

private theorem terminal_reply {d : Slot} (reply : d=.negative ∨ d=.positive) (seen : Bool) :
    terminal seen d=d := by
  rcases reply with h|h <;> simp [h,terminal]

theorem return_shape_step {n j : Nat} (hn : 1<n) {x : Line}
    (k : Fin n) (seen : Bool) (good : Shape n x (.back j)) :
    Shape n (ObserverDirty.move x k seen) (advance x k (.back j)) ∧
      (∀ l, advance x k (.back j)=.back l → (ObserverDirty.move x k seen).slot l=x.slot j) := by
  obtain ⟨waiting,bound,reply,trails,empty⟩ := good
  have kBound := k.isLt
  have suffix : EmptyAbove (ObserverDirty.move x k seen) j n :=
    empty_suffix_keep k seen empty fun edge => by
      rw [empty ((k : Nat)+1) (by omega) (by omega),edge,hop_reply_left reply]
  by_cases reverseNow : (k : Nat)+1=j
  · have arrived : hop (x.slot k) (x.slot ((k : Nat)+1))=(x.slot j,.empty) := by
      rw [trails k (by omega),reverseNow,hop_reply_right reply]
    have atNext : (ObserverDirty.move x k seen).slot k=x.slot j := by
      rw [move_left,arrived]
    have cleared : (ObserverDirty.move x k seen).slot j=.empty := by
      rw [←reverseNow,move_right,arrived]
    rw [advance,if_pos reverseNow]
    refine ⟨⟨waiting_while_door_holds k seen waiting (.inr (trails 0 (by omega))),
      by omega,atNext.symm ▸ reply,?_,?_⟩,?_⟩
    · apply trails_keep k seen waiting (fun i hi => trails i (by omega)) (by omega)
      omega
    · intro i low high
      by_cases atOld : i=j
      · exact atOld.symm ▸ cleared
      · exact suffix i (by omega) high
    · intro l h
      injection h with eq
      exact eq ▸ atNext
  · by_cases accepts : j=0 ∧ (k : Nat)+1=n
    · obtain ⟨rfl,last⟩ := accepts
      rw [advance,if_neg reverseNow,if_pos ⟨rfl,last⟩]
      rcases reply with negative|positive
      · rw [if_pos negative]
        refine ⟨⟨by simp [ObserverDirty.move,last,waiting,negative,door],?_⟩,fun l h => nomatch h⟩
        intro i hi
        by_cases z : i=0
        · subst i
          rw [move_door (by omega) x k seen last,waiting,negative] <;> rfl
        · exact suffix i (by omega) hi
      · have notNegative : x.slot 0≠.negative := by simp [positive]
        rw [if_neg notNegative]
        refine ⟨⟨by simp [ObserverDirty.move,last,waiting,positive,door],?_⟩,fun l h => nomatch h⟩
        intro i hi
        by_cases z : i=0
        · subst i
          rw [move_door (by omega) x k seen last,waiting,positive] <;> rfl
        · exact suffix i (by omega) hi
    · rw [advance,if_neg reverseNow,if_neg accepts]
      have holdControl : (ObserverDirty.move x k seen).pc=.waiting := by
        by_cases z : j=0
        · have notLast : (k : Nat)+1≠n := fun last => accepts ⟨z,last⟩
          simp [ObserverDirty.move,notLast,waiting,commit]
        · exact waiting_while_door_holds k seen waiting (.inr (trails 0 (by omega)))
      have holdReply : (ObserverDirty.move x k seen).slot j=x.slot j := by
        by_cases current : (k : Nat)=j
        · rw [←current,move_left,
            empty ((k : Nat)+1) (by omega) (by omega),current,hop_reply_left reply]
        · by_cases turn : (k : Nat)=0 ∧ j=n
          · obtain ⟨first,eq⟩ := turn
            subst j
            rw [move_terminal (by omega) x k seen first,terminal_reply reply seen]
          · have notDoor : ¬((k : Nat)+1=n ∧ j=0) := fun h => accepts ⟨h.2,h.1⟩
            simp only [ObserverDirty.move,if_neg (Ne.symm current),if_neg (Ne.symm reverseNow),
              if_neg turn,if_neg notDoor]
      refine ⟨⟨holdControl,bound,holdReply.symm ▸ reply,?_,suffix⟩,?_⟩
      · exact trails_keep k seen waiting trails bound (fun h => (reverseNow h).elim)
      · intro l h
        injection h with eq
        exact eq ▸ holdReply

theorem shape_step {n : Nat} (hn : 1<n) {x : Line} (k : Fin n) (seen : Bool)
    (st : Stage) (good : Shape n x st) :
    Shape n (ObserverDirty.move x k seen) (advance x k st) := by
  cases st with
  | idle => exact idle_shape_step hn k seen good
  | out j => exact outward_shape_step hn k seen good
  | back j => exact (return_shape_step hn k seen good).1
  | pending => exact pending_shape_step hn k seen good

theorem rank_step {n : Nat} {x : Line} (k : Fin n) {st : Stage}
    (good : Shape n x st) (live : st≠.idle) :
    rank n (advance x k st) ≤ rank n st := by
  cases st with
  | idle => exact (live rfl).elim
  | out j =>
    have bound := good.2.1
    simp only [advance]
    split
    · simp [rank]
      omega
    · split
      · simp [rank]
        omega
      · exact Nat.le_refl _
  | back j =>
    simp only [advance]
    split
    · simp [rank]
      omega
    · split
      · split <;> simp [rank] <;> omega
      · exact Nat.le_refl _
  | pending =>
    simp only [advance]
    split <;> simp [rank]

theorem nominated_step {n : Nat} (hn : 1<n) {x : Line} {st : Stage}
    (good : Shape n x st) (live : st≠.idle) :
    ∃ k : Fin n, rank n (advance x k st) < rank n st := by
  cases st with
  | idle => exact (live rfl).elim
  | out j =>
    have bound := good.2.1
    by_cases short : j<n
    · refine ⟨⟨j,short⟩,?_⟩
      simp [advance,rank]
      omega
    · have eq : j=n := by omega
      subst j
      refine ⟨⟨0,by omega⟩,?_⟩
      simp [advance,rank,show 0≠n by omega]
      omega
  | back j =>
    have bound := good.2.1
    cases j with
    | zero =>
      refine ⟨⟨n-1,by omega⟩,?_⟩
      have last : n-1+1=n := by omega
      have nz : n≠0 := by omega
      simp only [advance,last,if_neg nz,true_and,if_true]
      split <;> simp [rank]
    | succ j =>
      refine ⟨⟨j,by omega⟩,?_⟩
      simp [advance,rank]
  | pending => exact ⟨⟨0,by omega⟩,by simp [advance,rank]⟩

theorem outward_move {n j j' : Nat} {root : Fin n} {x : Line} (k : Fin n)
    (h : advance x k (.out j)=.out j') :
    Outward root (lapSite root ((k : Nat)+1)) j j' := by
  by_cases hopNow : (k : Nat)=j
  · rw [advance,if_pos hopNow] at h
    injection h with next
    rw [←next,hopNow]
    constructor
    rfl
  · by_cases turn : (k : Nat)=0 ∧ j=n
    · rw [advance,if_neg hopNow,if_pos turn] at h
      exact nomatch h
    · rw [advance,if_neg hopNow,if_neg turn] at h
      injection h with next
      rw [←next]
      exact .stay _

theorem turn_reply {n j l : Nat} (hn : 1<n) {x : Line} (k : Fin n) (seen : Bool)
    (old : Shape n x (.out j)) (h : advance x k (.out j)=.back l) :
    j=n ∧ l=n ∧ (ObserverDirty.move x k seen).slot l=(if seen then .positive else .negative) := by
  by_cases hopNow : (k : Nat)=j
  · rw [advance,if_pos hopNow] at h
    exact nomatch h
  · by_cases turn : (k : Nat)=0 ∧ j=n
    · rw [advance,if_neg hopNow,if_pos turn] at h
      injection h with next
      obtain ⟨first,eq⟩ := turn
      subst j
      subst l
      rw [move_terminal (by omega) x k seen first, old.2.2.1]
      exact ⟨rfl,rfl,rfl⟩
    · rw [advance,if_neg hopNow,if_neg turn] at h
      exact nomatch h

end Line

section Guard

open ObserverDirty

/-- A view of raw marks at a fixed reference. The observer line omits
the bit on an outward front, so that bit is read separately from the
same physical state. Labels are the outward link indices; no extra
terminal, door, or return marks are added. -/
structure Machine (X : Type) {n : Nat} (root : Fin n) where
  next : X → Fin n → X
  line : X → Line
  carrier : X → Fin n → Bool
  seen : X → Nat → Bool
  turnBit : X → Fin n → Bool
  exchange : X → Fin n → Bool
  seed : X → Fin n → Bool
  line_update : ∀ x (k : Fin n), line (next x k)=ObserverDirty.move (line x) k (turnBit x k)
  carrier_step : ∀ x (k : Fin n), CarrierMove (lapSite root ((k : Nat)+1))
    (carrier x) (carrier (next x k)) (exchange x k)
  seed_exact : ∀ x (k : Fin n), seed x k=true ↔ (k : Nat)=0 ∧ (line x).pc=.pending
  launch_observes : ∀ x (k : Fin n), Launches (line x) k →
    carrier (next x k) root=true → seen (next x k) 0=true
  front_observes : ∀ x (k : Fin n) j j', Shape n (line x) (.out j) →
    advance (line x) k (.out j)=.out j' →
    let e := lapSite root ((k : Nat)+1)
    seen x j=true ∨
      (lapSite root j'=e ∧ carrier (next x k) e=true) ∨
      (lapSite root j'=rightNeighbor e ∧ carrier (next x k) (rightNeighbor e)=true) ∨
      (lapSite root j'=e ∧ lapSite root j=rightNeighbor e ∧ exchange x k=true) →
    seen (next x k) j'=true
  turn_observes : ∀ x (k : Fin n), Shape n (line x) (.out n) →
    (k : Nat)=0 → seen x n=true → turnBit x k=true
  launch_sound : ∀ x (k : Fin n), Launches (line x) k → seen (next x k) 0=true →
    ∃ i, carrier (next x k) i=true
  front_sound : ∀ x (k : Fin n) j j', Shape n (line x) (.out j) →
    advance (line x) k (.out j)=.out j' →
    seen (next x k) j'=true → seen x j=true ∨ ∃ i, carrier (next x k) i=true
  turn_sound : ∀ x (k : Fin n), Shape n (line x) (.out n) →
    (k : Nat)=0 → turnBit x k=true → seen x n=true ∨ ∃ i, carrier (next x k) i=true
  seed_marks : ∀ x (k : Fin n), seed x k=true → ∃ i, carrier (next x k) i=true

variable {X : Type} {n : Nat} {root : Fin n}

def HasCarrier (m : Machine X root) (x : X) : Prop :=
  ∃ i, m.carrier x i=true

theorem hasCarrier_step (m : Machine X root) (x : X) (k : Fin n)
    (h : HasCarrier m x) : HasCarrier m (m.next x k) :=
  carrier_nonempty_step (m.carrier_step x k) h

theorem machine_shape_step (m : Machine X root) (hn : 1<n) (x : X) (k : Fin n)
    (st : Stage) (h : Shape n (m.line x) st) :
    Shape n (m.line (m.next x k)) (advance (m.line x) k st) := by
  rw [m.line_update]
  exact shape_step hn k (m.turnBit x k) st h

def Positive (m : Machine X root) (x : X) : Stage → Prop
  | .idle => HasCarrier m x
  | .out j => (m.seen x j=true ∨ Separated root (m.carrier x) j) ∧ HasCarrier m x
  | .back j => (m.line x).slot j=.positive ∧ HasCarrier m x
  | .pending => False

private theorem positive_outward (m : Machine X root) {x : X} (k : Fin n) {j j' : Nat}
    (old : Shape n (m.line x) (.out j)) (positive : Positive m x (.out j))
    (a : advance (m.line x) k (.out j)=.out j') :
    Positive m (m.next x k) (.out j') := by
  refine ⟨?_,hasCarrier_step m x k positive.2⟩
  rcases positive.1 with seen | track
  · exact .inl (m.front_observes x k j j' old a (.inl seen))
  · rcases separation_step track (outward_move k a) (m.carrier_step x k) with track | observed
    · exact .inr track
    · exact .inl (m.front_observes x k j j' old a (.inr observed))

theorem positive_step (m : Machine X root) (hn : 1<n) (x : X) (k : Fin n)
    (st : Stage) (old : Shape n (m.line x) st) (positive : Positive m x st) :
    Positive m (m.next x k) (advance (m.line x) k st) := by
  cases st with
  | idle =>
    have marked := hasCarrier_step m x k positive
    by_cases launch : (k : Nat)+1=n
    · rw [advance,if_pos launch]
      refine ⟨?_,marked⟩
      rcases initial_separation (root:=root) marked with atRoot|track
      · exact .inl (m.launch_observes x k ⟨launch,old.1⟩ atRoot)
      · exact .inr track
    · rw [advance,if_neg launch]
      exact marked
  | out j =>
    by_cases hopNow : (k : Nat)=j
    · have a : advance (m.line x) k (.out j)=.out (j+1) := by simp [advance,hopNow]
      rw [a]
      exact positive_outward m k old positive a
    · by_cases turns : (k : Nat)=0 ∧ j=n
      · obtain ⟨first,eq⟩ := turns
        subst j
        have a : advance (m.line x) k (.out n)=.back n := by rw [advance,if_neg hopNow,if_pos ⟨first,rfl⟩]
        have seen := terminal_observed positive.1
        have yes := m.turn_observes x k old first seen
        rw [a]
        refine ⟨?_,hasCarrier_step m x k positive.2⟩
        rw [m.line_update,(turn_reply hn k (m.turnBit x k) old a).2.2,yes] <;> rfl
      · have a : advance (m.line x) k (.out j)=.out j := by simp [advance,hopNow,turns]
        rw [a]
        exact positive_outward m k old positive a
  | back j =>
    have keep := (return_shape_step hn k (m.turnBit x k) old).2
    have marked := hasCarrier_step m x k positive.2
    by_cases reverseNow : (k : Nat)+1=j
    · have a : advance (m.line x) k (.back j)=.back k := by simp [advance,reverseNow]
      rw [a]
      exact ⟨by rw [m.line_update,keep _ a,positive.1],marked⟩
    · by_cases accepts : j=0 ∧ (k : Nat)+1=n
      · obtain ⟨rfl,last⟩ := accepts
        have positiveReply : (m.line x).slot 0=.positive := positive.1
        rw [advance,if_neg reverseNow,if_pos ⟨rfl,last⟩]
        simpa [positiveReply,Positive] using marked
      · have a : advance (m.line x) k (.back j)=.back j := by simp [advance,reverseNow,accepts]
        rw [a]
        exact ⟨by rw [m.line_update,keep _ a,positive.1],marked⟩
  | pending => exact positive.elim

def run (m : Machine X root) (x : X) : List (Fin n) → X
  | [] => x
  | k::w => run m (m.next x k) w

private theorem guard_step (m : Machine X root) (x : X) (k : Fin n)
    (st : Stage) (old : Shape n (m.line x) st) (positive : Positive m x st) :
    m.seed x k=false := by
  cases st with
  | pending => exact positive.elim
  | idle | out | back =>
    apply Bool.eq_false_iff.mpr
    intro h
    have pending := ((m.seed_exact x k).mp h).2
    have pc := old.1
    rw [pending] at pc
    contradiction

/-- Every finite continuation from a clean marked handoff stays out
of PENDING. In particular, an incomplete future lap cannot seed. -/
theorem no_seed_on_continuation (m : Machine X root) (hn : 1<n) {x : X}
    (idle : Shape n (m.line x) .idle) (marked : HasCarrier m x) (w : List (Fin n)) (k : Fin n) :
    m.seed (run m x w) k=false := by
  have aux (y : X) (st : Stage) (old : Shape n (m.line y) st) (p : Positive m y st)
      (w : List (Fin n)) : m.seed (run m y w) k=false := by
    induction w generalizing y st with
    | nil => exact guard_step m y k st old p
    | cons e rest ih =>
      exact ih _ _ (machine_shape_step m hn y e st old) (positive_step m hn y e st old p)
  exact aux x .idle idle marked w

theorem no_pending_on_continuation (m : Machine X root) (hn : 1<n) {x : X}
    (idle : Shape n (m.line x) .idle) (marked : HasCarrier m x) (w : List (Fin n)) :
    (m.line (run m x w)).pc≠.pending := by
  intro pending
  let incoming : Fin n := ⟨0,by omega⟩
  have yes := (m.seed_exact (run m x w) incoming).2 ⟨rfl,pending⟩
  have no := no_seed_on_continuation m hn idle marked w incoming
  rw [no] at yes
  contradiction

/-- A positive reading has a physical carrier witness. A negative
reply is allowed on the first trip, which started before a mark was
known to exist. -/
def Sound (m : Machine X root) (x : X) : Stage → Prop
  | .idle => HasCarrier m x
  | .out j => m.seen x j=true → HasCarrier m x
  | .back j => (m.line x).slot j=.positive → HasCarrier m x
  | .pending => True

theorem sound_after_launch (m : Machine X root) (hn : 1<n) (x : X) (k : Fin n)
    (launch : Launches (m.line x) k) :
    Shape n (m.line (m.next x k)) (.out 0) ∧ Sound m (m.next x k) (.out 0) := by
  refine ⟨?_,m.launch_sound x k launch⟩
  rw [m.line_update]
  exact shape_after_launch hn (m.line x) k (m.turnBit x k) launch

private theorem positive_sound (m : Machine X root) (x : X) (st : Stage)
    (p : Positive m x st) : Sound m x st := by
  cases st with
  | idle => exact p
  | out j => exact fun _ => p.2
  | back j => exact fun _ => p.2
  | pending => exact True.intro

private theorem sound_outward (m : Machine X root) {x : X} (k : Fin n) {j l : Nat}
    (old : Shape n (m.line x) (.out j)) (s : Sound m x (.out j))
    (a : advance (m.line x) k (.out j)=.out l) : Sound m (m.next x k) (.out l) := by
  intro yes
  rcases m.front_sound x k j l old a yes with seen|marked
  · exact hasCarrier_step m x k (s seen)
  · exact marked

private theorem sound_return (m : Machine X root) (hn : 1<n) {x : X} (k : Fin n) {j l : Nat}
    (old : Shape n (m.line x) (.back j)) (s : Sound m x (.back j))
    (a : advance (m.line x) k (.back j)=.back l) : Sound m (m.next x k) (.back l) := by
  intro yes
  have keep := (return_shape_step hn k (m.turnBit x k) old).2 l a
  rw [m.line_update,keep] at yes
  exact hasCarrier_step m x k (s yes)

theorem sound_step (m : Machine X root) (hn : 1<n) (x : X) (k : Fin n)
    (st : Stage) (old : Shape n (m.line x) st) (s : Sound m x st) :
    Sound m (m.next x k) (advance (m.line x) k st) := by
  cases st with
  | idle => exact positive_sound m _ _ (positive_step m hn x k .idle old s)
  | out j =>
    by_cases hopNow : (k : Nat)=j
    · have a : advance (m.line x) k (.out j)=.out (j+1) := by simp [advance,hopNow]
      rw [a]
      exact sound_outward m k old s a
    · by_cases turns : (k : Nat)=0 ∧ j=n
      · obtain ⟨first,eq⟩ := turns
        subst j
        have a : advance (m.line x) k (.out n)=.back n := by rw [advance,if_neg hopNow,if_pos ⟨first,rfl⟩]
        rw [a]
        intro positive
        have turn := (turn_reply hn k (m.turnBit x k) old a).2.2
        rw [m.line_update,turn] at positive
        have seen : m.turnBit x k=true := by
          cases bit : m.turnBit x k with
          | true => rfl
          | false => simp [bit] at positive
        rcases m.turn_sound x k old first seen with seen|marked
        · exact hasCarrier_step m x k (s seen)
        · exact marked
      · have a : advance (m.line x) k (.out j)=.out j := by simp [advance,hopNow,turns]
        rw [a]
        exact sound_outward m k old s a
  | back j =>
    by_cases reverseNow : (k : Nat)+1=j
    · have a : advance (m.line x) k (.back j)=.back k := by simp [advance,reverseNow]
      rw [a]
      exact sound_return m hn k old s a
    · by_cases accepts : j=0 ∧ (k : Nat)+1=n
      · obtain ⟨rfl,last⟩ := accepts
        rw [advance,if_neg reverseNow,if_pos ⟨rfl,last⟩]
        rcases old.2.2.1 with negative|positive
        · rw [if_pos negative]
          exact True.intro
        · have no : (m.line x).slot 0≠.negative := by simp [positive]
          rw [if_neg no]
          exact hasCarrier_step m x k (s positive)
      · have a : advance (m.line x) k (.back j)=.back j := by simp [advance,reverseNow,accepts]
        rw [a]
        exact sound_return m hn k old s a
  | pending =>
    by_cases first : (k : Nat)=0
    · rw [advance,if_pos first]
      exact m.seed_marks x k ((m.seed_exact x k).mpr ⟨first,old.1⟩)
    · rw [advance,if_neg first]
      exact True.intro

/-- Once the generated trip has returned to its empty ISSUE line, a
carrier is present and all later raw marks have zero seed pulse. -/
theorem completed_handoff (m : Machine X root) (hn : 1<n) {x : X}
    (clean : Shape n (m.line x) .idle) (sound : Sound m x .idle) :
    HasCarrier m x ∧ ∀ w k, m.seed (run m x w) k=false :=
  ⟨sound,no_seed_on_continuation m hn clean sound⟩

end Guard

end L4.Height.ObserverTrip
