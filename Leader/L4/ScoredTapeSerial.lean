import Leader.L4.OrderedRaceTape

namespace L4.ScoredTapeSerial
open ResetReturnIID
abbrev Word (n : Nat) := List (Fin n)

/-- A stopped tape reader. On continuation at acceptance it transfers
its final score, and never changes or consumes extra scheduler labels. -/
structure Reader (n a b A : Nat) where
  State : Type
  start : State
  tick : State→Fin n→State
  word : State→Word n
  word_start : word start=[]
  word_step : ∀ y e, word (tick y e)=appendTape (word y) e
  valid : State→Prop
  valid_start : valid start
  done : State→Prop
  valid_step : ∀ y e,valid y→¬done y→valid (tick y e)
  reject : State→Prop
  credit : State→Nat
  initial_credit : credit start=a
  cap : ∀ y,valid y→credit y≤729
  lost : ∀ y,valid y→done y→reject y→credit y=0
  paid : ∀ y,valid y→done y→¬reject y→credit y=b
  localLaw : ∀ y,valid y→¬done y→AdaptiveDoorCredit.LocalLaw tick credit y
  mean : Height.IIDExpectedHittingTimeAtMost tick done start A

namespace Reader
variable {n a b c A B : Nat} (L : Reader n a b A)
abbrev Passed := {x : L.State // L.valid x ∧ L.done x ∧ ¬L.reject x}
variable (R : Passed L→Reader n b c B)

abbrev Joined := Sum L.State (Sigma fun x : Passed L => (R x).State)

noncomputable def enter (x : L.State) : Joined L R := by
  classical
  exact if H : L.valid x ∧ L.done x ∧ ¬L.reject x then .inr ⟨⟨x,H⟩,(R ⟨x,H⟩).start⟩ else .inl x

def jWord : Joined L R→Word n
  | .inl x => L.word x
  | .inr ⟨x,y⟩ => L.word x.1 ++ (R x).word y

def jValid : Joined L R→Prop
  | .inl x => L.valid x ∧ ¬(L.valid x ∧ L.done x ∧ ¬L.reject x)
  | .inr ⟨x,y⟩ => (R x).valid y

def jDone : Joined L R→Prop
  | .inl x => L.done x
  | .inr ⟨x,y⟩ => (R x).done y

def jReject : Joined L R→Prop
  | .inl x => L.reject x
  | .inr ⟨x,y⟩ => (R x).reject y

def jCredit : Joined L R→Nat
  | .inl x => L.credit x
  | .inr ⟨x,y⟩ => (R x).credit y

noncomputable def jTick : Joined L R→Fin n→Joined L R
  | .inl x,e => enter L R (L.tick x e)
  | .inr ⟨x,y⟩,e => .inr ⟨x,(R x).tick y e⟩

theorem word_enter (x : L.State) : jWord L R (enter L R x)=L.word x := by
  classical
  unfold enter
  split
  · simp [jWord,Reader.word_start]
  · rfl

theorem valid_enter (x : L.State) (H : L.valid x) : jValid L R (enter L R x) := by
  classical
  unfold enter
  split
  · rename_i S
    exact (R ⟨x,S⟩).valid_start
  · rename_i N
    exact ⟨H,N⟩

theorem credit_enter (x : L.State) (H : L.valid x) : jCredit L R (enter L R x)=L.credit x := by
  classical
  unfold enter
  split
  · rename_i S
    exact (R ⟨x,S⟩).initial_credit.trans (L.paid x H S.2.1 S.2.2).symm
  · rfl

theorem jword_step (y : Joined L R) (e : Fin n) :
    jWord L R (jTick L R y e)=appendTape (jWord L R y) e := by
  cases y with
  | inl x => rw [jTick,word_enter,L.word_step]; rfl
  | inr xy =>
    obtain ⟨x,y⟩ := xy
    simp [jTick,jWord,(R x).word_step,appendTape,List.append_assoc]

theorem jvalid_step (y : Joined L R) (e : Fin n) (H : jValid L R y) (N : ¬jDone L R y) :
    jValid L R (jTick L R y e) := by
  cases y with
  | inl x => exact valid_enter L R _ (L.valid_step x e H.1 N)
  | inr xy => exact (R xy.1).valid_step xy.2 e H N

theorem jlocal (y : Joined L R) (H : jValid L R y) (N : ¬jDone L R y) :
    AdaptiveDoorCredit.LocalLaw (jTick L R) (jCredit L R) y := by
  cases y with
  | inl x =>
    have E (e : Fin n) : jCredit L R (jTick L R (.inl x) e)=L.credit (L.tick x e) :=
      credit_enter L R _ (L.valid_step x e H.1 N)
    rcases L.localLaw x H.1 N with mono|⟨win,l₁,l₂,H₁,H₂,H₃,pay,stay⟩
    · exact .inl (fun e=>by rw [E]; exact mono e)
    · refine .inr ⟨win,l₁,l₂,H₁,H₂,H₃,?_,?_⟩
      · rw [E]; exact pay
      · intro e w u v; rw [E]; exact stay e w u v
  | inr xy => exact (R xy.1).localLaw xy.2 H N

def bridge : Joined L R→Prop
  | .inl _ => False
  | .inr ⟨x,y⟩ => y=(R x).start

private theorem reached (x : L.State) (d : L.done x) :
    bridge L R (enter L R x) ∨ jDone L R (enter L R x) := by
  classical
  unfold enter
  split
  · exact .inl rfl
  · exact .inr d

private theorem stage_left :
    ∀ t x, Height.iidHitCost (jTick L R) (fun y=>bridge L R y∨jDone L R y) t (enter L R x)
      ≤ Height.iidHitCost L.tick L.done t x := by
  classical
  intro t
  induction t with
  | zero => intro x; exact Nat.le_refl _
  | succ t ih =>
    intro x
    by_cases endL : L.done x
    · rw [Height.iidHitCost_of_target _ (fun y=>bridge L R y∨jDone L R y) _ (reached L R x endL)]
      exact Nat.zero_le _
    · have E : enter L R x=.inl x := by simp [enter,endL]
      have M : ¬(bridge L R (.inl x)∨jDone L R (.inl x)) :=
        fun h=>h.elim False.elim endL
      rw [E]
      simp only [Height.iidHitCost,if_neg endL,if_neg M,jTick]
      exact Nat.add_le_add_left (ControllerTapeIID.sum_mono (fun e=>ih (L.tick x e))) _

private theorem stage_right (x : Passed L) :
    ∀ t y, Height.iidHitCost (jTick L R) (jDone L R) t (.inr ⟨x,y⟩) ≤
      Height.iidHitCost (R x).tick (R x).done t y := by
  classical
  intro t
  induction t with
  | zero => intro y; exact Nat.le_refl _
  | succ t ih =>
    intro y
    by_cases T : (R x).done y
    · rw [Height.iidHitCost_of_target _ _ _ (show jDone L R (.inr ⟨x,y⟩) from T)]
      exact Nat.zero_le _
    · have U : ¬jDone L R (.inr ⟨x,y⟩) := T
      simp only [Height.iidHitCost,if_neg T,if_neg U,jTick]
      exact Nat.add_le_add_left (ControllerTapeIID.sum_mono (fun e=>ih ((R x).tick y e))) _

/-- Serial composition on one tape. The accepted checkpoint chooses the
continuation immediately, before any future mark has been sampled. -/
noncomputable def bind (hn : 0<n) : Reader n a c (A+B) where
  State := Joined L R
  start := enter L R L.start
  tick := jTick L R
  word := jWord L R
  word_start := (word_enter L R _).trans L.word_start
  word_step := jword_step L R
  valid := jValid L R
  valid_start := valid_enter L R _ L.valid_start
  valid_step := jvalid_step L R
  done := jDone L R
  reject := jReject L R
  credit := jCredit L R
  initial_credit := (credit_enter L R _ L.valid_start).trans L.initial_credit
  cap := by
    intro y H
    cases y with
    | inl x => exact L.cap x H.1
    | inr xy => exact (R xy.1).cap xy.2 H
  lost := by
    intro y H D F
    cases y with
    | inl x => exact L.lost x H.1 D F
    | inr xy => exact (R xy.1).lost xy.2 H D F
  paid := by
    intro y H D F
    cases y with
    | inl x => exact (H.2 ⟨H.1,D,F⟩).elim
    | inr xy => exact (R xy.1).paid xy.2 H D F
  localLaw := jlocal L R
  mean := by
    apply Height.iid_stage_le (jTick L R) hn _ (bridge L R) (jDone L R) A B
      (fun t=>Nat.le_trans (stage_left L R t _) (L.mean t))
    intro y H
    cases y with
    | inl x => exact H.elim
    | inr xy =>
      obtain ⟨x,y⟩ := xy
      change y=(R x).start at H
      subst y
      exact fun t=>Nat.le_trans (stage_right L R x t _) ((R x).mean t)

theorem accepted_bind (hn : 0<n) (y : (bind L R hn).State)
    (V : (bind L R hn).valid y) (D : (bind L R hn).done y) (F : ¬(bind L R hn).reject y) :
    ∃ (x : Passed L) (z : (R x).State),
      y=.inr ⟨x,z⟩ ∧ (R x).valid z ∧ (R x).done z ∧ ¬(R x).reject z ∧
      (bind L R hn).word y=L.word x.1++(R x).word z := by
  cases y with
  | inl x => exact (V.2 ⟨V.1,D,F⟩).elim
  | inr xy => exact ⟨xy.1,xy.2,rfl,V,D,F,rfl⟩

end Reader

#print axioms Reader.bind
#print axioms Reader.accepted_bind
end L4.ScoredTapeSerial
