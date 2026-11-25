import Leader.L4.ShortPrefixFailure

namespace L4.ShortPrefixTrial
open Classical

variable {X : Type} {n : Nat}

structure Setup (X : Type) (n : Nat) where
  word : List (Fin n)
  watch : Fin n→Bool
  parked : X→Prop
  actual : (X×Bool)→Fin n→(X×Bool)

structure Active (X : Type) (n : Nat) where
  anchor : X×Bool
  remain : Option (List (Fin n))
  cut : Bool

structure RenewalState (X : Type) (n : Nat) where
  real : X×Bool
  active : Option (Active X n)

variable (S : Setup X n)
variable (Good : X→Prop)

noncomputable def initialise (x : X×Bool) : RenewalState X n :=
  ⟨x,if x.2=true ∨ S.parked x.1 then some ⟨x,some S.word,true⟩ else none⟩

def trialState (y : RenewalState X n) (a : Active X n) : State X n := ⟨y.real,a.remain⟩

noncomputable def advance (y : RenewalState X n) (e : Fin n) : RenewalState X n :=
  match y.active with
  | none => initialise S (S.actual y.real e)
  | some a =>
    let z := next S.actual S.watch (trialState y a) e
    ⟨z.real,some ⟨a.anchor,z.remain,false⟩⟩

def prepared (y : RenewalState X n) : Prop :=
  ∃ a, y.active=some a ∧ a.cut=true

def halt (y : RenewalState X n) : Prop :=
  ∃ a, y.active=some a ∧ ready (trialState y a)

def valid (y : RenewalState X n) : Prop :=
  Good y.real.1 ∧ match y.active with
  | none => ¬(y.real.2=true ∨ S.parked y.real.1)
  | some a => Good a.anchor.1 ∧ (a.anchor.2=true ∨ S.parked a.anchor.1) ∧
      reach S.actual Good S.watch a.anchor S.word (trialState y a) ∧
      (a.cut=true → trialState y a=start a.anchor S.word)

theorem initialise_valid (x : X×Bool) (G : Good x.1) :
    valid S Good (initialise S x) := by
  unfold initialise valid
  split
  · rename_i H
    exact ⟨G,G,H,reach_start S.actual Good S.watch x S.word G,fun _=>rfl⟩
  · rename_i H
    exact ⟨G,H⟩

theorem step_project (y : RenewalState X n) (e : Fin n) :
    (advance S y e).real=S.actual y.real e := by
  unfold advance
  split <;> rfl

private theorem already_seen_replay (x : X×Bool)
    (sticky : ∀ z e,z.2=true→(S.actual z e).2=true) (F : x.2=true) :
    Replay S.actual S.watch x S.word :=
  fun w _=>Height.runWord_of_closed S.actual (fun z=>z.2=true) sticky x w F

theorem valid_next
    (closed : ∀ z e,Good z.1→Good (S.actual z e).1)
    (sticky : ∀ z e,z.2=true→(S.actual z e).2=true)
    (watched : ∀ e∈S.word,S.watch e=true)
    (replay : ∀ x,Good x.1→S.parked x.1→Replay S.actual S.watch x S.word)
    (y : RenewalState X n) (e : Fin n) (Y : valid S Good y) :
    valid S Good (advance S y e) := by
  have C := closed y.real e Y.1
  cases A : y.active with
  | none => simpa only [advance,A] using initialise_valid S Good (S.actual y.real e) C
  | some a =>
    have T : Good a.anchor.1 ∧ (a.anchor.2=true ∨ S.parked a.anchor.1) ∧
      reach S.actual Good S.watch a.anchor S.word (trialState y a) ∧
      (a.cut=true → trialState y a = start a.anchor S.word) := by
      have K := Y.2
      rw [A] at K
      exact K
    have R := T.2.1.elim (already_seen_replay S a.anchor sticky) (replay a.anchor T.1)
    have Z := reach_next S.actual Good closed sticky S.watch a.anchor S.word watched R (trialState y a) e T.2.2.1
    unfold advance
    rw [A]
    exact ⟨C,T.1,T.2.1,Z,by simp⟩

private theorem halt_iff {y : RenewalState X n} {a : Active X n} (H : y.active=some a) :
    halt y ↔ ready (trialState y a) := by
  constructor
  · rintro ⟨b,B,K⟩
    have E := Option.some.inj (H.symm.trans B)
    subst b
    exact K
  · exact fun R=>⟨a,H,R⟩

private theorem prefix_next {y : RenewalState X n} {a : Active X n} (A : y.active=some a)
    (e : Fin n) :
    let p:=next S.actual S.watch (trialState y a) e
    (advance S y e).active=some ⟨a.anchor,p.remain,false⟩ ∧
    trialState (advance S y e) ⟨a.anchor,p.remain,false⟩=p := by
  unfold advance
  rw [A]
  exact ⟨rfl,rfl⟩

private theorem trial_cost (y : RenewalState X n) (a : Active X n) (A : y.active=some a) (t : Nat) :
    iidHitCost (advance S) halt t y = iidHitCost (next S.actual S.watch) ready t (trialState y a) := by
  induction t generalizing y a with
  | zero => rfl
  | succ t ih =>
    by_cases T : halt y
    · simp [iidHitCost,T,(halt_iff A).mp T]
    · simp only [iidHitCost,if_neg T,if_neg (fun U=>T ((halt_iff A).mpr U))]
      congr 2
      apply congrArg List.ofFn
      funext e
      obtain ⟨H,R⟩ := prefix_next S A e
      rw [ih _ _ H,R]

private theorem trial_mass (y : RenewalState X n) (a : Active X n) (A : y.active=some a) (t : Nat) :
    TripleRenewal.terminalMass (advance S) halt (fun z=>z.real.2≠true) t y =
      TripleRenewal.terminalMass (next S.actual S.watch) ready (fun z=>z.real.2≠true) t (trialState y a) := by
  induction t generalizing y a with
  | zero =>
    have P : (trialState y a).real.2=y.real.2 := rfl
    by_cases T : ready (trialState y a) <;> cases E : y.real.2 <;>
      simp [TripleRenewal.terminalMass,halt_iff A,T,P,E]
  | succ t ih =>
    by_cases T : halt y
    · have P : (trialState y a).real.2=y.real.2 := rfl
      cases E : y.real.2 <;> simp [TripleRenewal.terminalMass,T,(halt_iff A).mp T,P,E]
    · simp only [TripleRenewal.terminalMass,if_neg T,if_neg (fun U=>T ((halt_iff A).mpr U)),TaggedTail.sumEdge]
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext e
      obtain ⟨H,R⟩ := prefix_next S A e
      rw [ih _ _ H,R]

private theorem initial_boundary (z : X×Bool) :
    (initialise S z).active=none ∨ prepared (initialise S z) := by
  unfold initialise
  split
  · exact .inr ⟨_,rfl,rfl⟩
  · exact .inl rfl

private theorem ready_not_none {y : RenewalState X n} (A : y.active=none) : ¬halt y := by
  rintro ⟨a,B,_⟩
  rw [A] at B
  cases B

private theorem prep_cost_le (base : X→Fin n→X)
    (project : ∀ z e,(S.actual z e).1=base z.1 e)
    (closed : ∀ z e,Good z.1→Good (S.actual z e).1)
    (t : Nat) (y : RenewalState X n) (Y : valid S Good y)
    (B : y.active=none ∨ prepared y) :
    iidHitCost (advance S) prepared t y ≤ iidHitCost base S.parked t y.real.1 := by
  induction t generalizing y with
  | zero => simp [iidHitCost]
  | succ t ih =>
    rcases B with N|P
    · have NP : ¬prepared y := by rintro ⟨a,A,_⟩; rw [N] at A; cases A
      have K : ¬S.parked y.real.1 := by
        have V := Y.2
        rw [N] at V
        exact fun H=> V (.inr H)
      simp only [iidHitCost,if_neg NP,if_neg K]
      apply Nat.add_le_add_left
      apply Height.sum_ofFn_le
      intro e
      unfold advance
      rw [N,←project y.real e]
      exact ih _ (initialise_valid S Good _ (closed y.real e Y.1)) (initial_boundary S _)
    · simp [iidHitCost,P]

/-- Trial cut is instantaneous as an observation, not a new raw mark.
Probability bounds are invoked only at the first cut, never at a
reachable state already stopped in failure. -/
theorem renewal_expected (base : X→Fin n→X)
    (project : ∀ z e,(S.actual z e).1=base z.1 e)
    (closed : ∀ z e,Good z.1→Good (S.actual z e).1)
    (sticky : ∀ z e,z.2=true→(S.actual z e).2=true)
    (watched : ∀ e∈S.word,S.watch e=true)
    (replay : ∀ x,Good x.1→S.parked x.1→Replay S.actual S.watch x S.word)
    (nonempty : S.word≠[])
    (W : cardinal S.watch≤50) (M : S.word.length≤116) (R : Nat)
    (regenerate : ∀ x,Good x→IIDExpectedHittingTimeAtMost base S.parked x R)
    (x : X×Bool) (G : Good x.1) :
    IIDExpectedHittingTimeAtMost S.actual (fun z=>z.2=true) x ((50^116)*(R+116*n)) := by
  let Q := valid S Good
  let init := initialise S
  let nx := advance S
  let hit := fun z : X×Bool=>z.2=true
  let adm := fun z : X×Bool=>Good z.1
  have stay := valid_next S Good closed sticky watched replay
  have startOk (z : X×Bool) (Z : adm z) : Q (init z) := initialise_valid S Good z Z
  apply TripleRenewal.expected_of_uniform_attempts S.actual hit adm (R+116*n) (50^116) (by decide) _ x G
  intro z Z H
  let st : TripleRenewal.Stage S.actual z :=
    ⟨RenewalState X n,init z,nx,RenewalState.real,halt,Q,rfl,step_project S,startOk z Z,stay⟩
  refine ⟨⟨st,?_,?_,?_,?_⟩⟩
  · change ¬halt (init z)
    unfold init initialise
    split
    · rintro ⟨a,A,B⟩
      have E : a=⟨z,some S.word,true⟩ := (Option.some.inj A).symm
      subst a
      rcases B with B|B|B
      · exact H B
      · cases B
      · exact nonempty (Option.some.inj B)
    · exact ready_not_none rfl
  · intro y Y _ _
    exact Y.1
  · intro t
    have cutMean (y : RenewalState X n) (Y : Q y) (P : prepared y) (u : Nat) :
        iidHitCost nx halt u y≤(116*n)*n^u := by
      obtain ⟨a,A,K⟩ := P
      have J := Y.2
      rw [A] at J
      have E := J.2.2.2 K
      have RP := J.2.1.elim (already_seen_replay S a.anchor sticky) (replay a.anchor J.1)
      have U := trial_mean closed sticky watched RP (trialState y a) J.2.2.1 u
      rw [trial_cost S y a A]
      apply Nat.le_trans U
      apply Nat.mul_le_mul_right
      rw [E,Nat.mul_comm 116 n]
      apply Nat.mul_le_mul_left
      cases Z : a.anchor.2 <;> simp [rank,start,Z,M]
    have T := TripleRenewal.glue_until_stop nx nx id (fun _ _=>rfl)
      halt prepared Q stay (116*n) t (fun y u Y P _ _=>cutMean y Y P u)
        t (Nat.le_refl _) (init z) (startOk z Z)
    have C := prep_cost_le S Good base project closed t (init z) (startOk z Z) (initial_boundary S z)
    have U := (regenerate z.1 Z) t
    have L := TripleRenewal.terminalMass_le_total nx prepared (fun y=>¬halt y) t (init z)
    rw [Nat.add_mul]
    exact Nat.le_trans T (Nat.add_le_add (Nat.le_trans C U) (Nat.mul_le_mul_left _ L))
  · intro t
    have cutFail (y : RenewalState X n) (Y : Q y) (P : prepared y) (u : Nat) :
        (50^116)*TripleRenewal.terminalMass nx halt (fun k=>k.real.2≠true) u y≤(50^116-1)*n^u := by
      obtain ⟨a,A,K⟩ := P
      have J := Y.2
      rw [A] at J
      have E := J.2.2.2 K
      have RP := J.2.1.elim (already_seen_replay S a.anchor sticky) (replay a.anchor J.1)
      rw [trial_mass S y a A,E]
      exact parked_failure closed sticky watched RP J.1 W M u
    have F (u : Nat) (y : RenewalState X n) (Y : Q y) (B : y.active=none ∨ prepared y) :
        (50^116)*TripleRenewal.terminalMass nx halt (fun k=>k.real.2≠true) u y≤(50^116-1)*n^u := by
      induction u generalizing y with
      | zero =>
        rcases B with A|P
        · simp [TripleRenewal.terminalMass,ready_not_none A]
        · exact cutFail y Y P 0
      | succ u ih =>
        rcases B with A|P
        · simp only [TripleRenewal.terminalMass,ready_not_none A,if_false,TaggedTail.sumEdge,
            ←Height.sum_ofFn_mul_left]
          have C (e : Fin n) : (nx y e).active=none ∨ prepared (nx y e) := by
            unfold nx advance
            rw [A]
            exact initial_boundary S _
          have M := Height.sum_ofFn_le _ (fun _ : Fin n=>(50^116-1)*n^u)
            (fun e=>ih _ (stay y e Y) (C e))
          rw [Height.sum_ofFn_const] at M
          calc
            _ ≤ n*((50^116-1)*n^u) := M
            _ = _ := by rw [Nat.pow_succ n u]; ac_rfl
        · exact cutFail y Y P (u+1)
    exact F t (init z) (startOk z Z) (initial_boundary S z)

-- CHECK: ShortPrefixFailure.lean:101-133;
-- ShortFiveFailurePotential.lean:12-15,41-46.
theorem parked_failure_param {step : (X×Bool)→Fin n→(X×Bool)}
    {Gd : X→Prop} {watch : Fin n→Bool}
    {x : X×Bool} {word : List (Fin n)}
    (closed : ∀ z e,Gd z.1→Gd (step z e).1)
    (sticky : ∀ z e,z.2=true→(step z e).2=true)
    (H : ∀ e∈word,watch e=true) (RP : Replay step watch x word)
    (G : Gd x.1) (Wcap Mcap : Nat) (Wpos : 0<Wcap)
    (W : cardinal watch≤Wcap) (M : word.length≤Mcap) (t : Nat) :
    (Wcap^Mcap)*TripleRenewal.terminalMass (next step watch) ready
      (fun z=>z.real.2≠true) t (start x word) ≤
        (Wcap^Mcap-1)*n^t := by
  have B : potential (Wcap^Mcap) (cardinal watch) (start x word) ≤
      Wcap^Mcap-1 := by
    cases Z : x.2 with
    | true => simp [potential,start,Z]
    | false =>
      cases word with
      | nil => simp [potential,start,Z,ShortFiveFailurePotential.at_zero]
      | cons a u =>
        have Q := cardinal_pos watch a (H a (by simp))
        have pow : (cardinal watch)^(a::u).length≤Wcap^Mcap :=
          Nat.le_trans (Nat.pow_le_pow_left W _) (Nat.pow_le_pow_right Wpos M)
        simpa only [potential,start,Z,Bool.false_eq_true,if_false] using
          (ShortFiveFailurePotential.start_le (Wcap^Mcap)
            (cardinal watch) (a::u).length Q pow)
  exact Nat.le_trans (failure_mass closed sticky H RP (Wcap^Mcap) (start x word)
    (reach_start step Gd watch x word G) t) (Nat.mul_le_mul_right _ B)

-- CHECK: ShortPrefixRenewal.lean:183-274. Same pinned argument,
-- with all numeric literals replaced by the two bounds.
theorem renewal_expected_param (base : X→Fin n→X)
    (project : ∀ z e,(S.actual z e).1=base z.1 e)
    (closed : ∀ z e,Good z.1→Good (S.actual z e).1)
    (sticky : ∀ z e,z.2=true→(S.actual z e).2=true)
    (watched : ∀ e∈S.word,S.watch e=true)
    (replay : ∀ x,Good x.1→S.parked x.1→Replay S.actual S.watch x S.word)
    (nonempty : S.word≠[])
    (Wcap Mcap : Nat) (Wpos : 0<Wcap)
    (W : cardinal S.watch≤Wcap) (M : S.word.length≤Mcap) (R : Nat)
    (regenerate : ∀ x,Good x→IIDExpectedHittingTimeAtMost base S.parked x R)
    (x : X×Bool) (G : Good x.1) :
    IIDExpectedHittingTimeAtMost S.actual (fun z=>z.2=true) x ((Wcap^Mcap)*(R+Mcap*n)) := by
  let Q := valid S Good
  let init := initialise S
  let nx := advance S
  let hit := fun z : X×Bool=>z.2=true
  let adm := fun z : X×Bool=>Good z.1
  have stay := valid_next S Good closed sticky watched replay
  have startOk (z : X×Bool) (Z : adm z) : Q (init z) := initialise_valid S Good z Z
  apply TripleRenewal.expected_of_uniform_attempts S.actual hit adm (R+Mcap*n) (Wcap^Mcap) (Nat.pow_pos Wpos) _ x G
  intro z Z H
  let st : TripleRenewal.Stage S.actual z :=
    ⟨RenewalState X n,init z,nx,RenewalState.real,halt,Q,rfl,step_project S,startOk z Z,stay⟩
  refine ⟨⟨st,?_,?_,?_,?_⟩⟩
  · change ¬halt (init z)
    unfold init initialise
    split
    · rintro ⟨a,A,B⟩
      have E : a=⟨z,some S.word,true⟩ := (Option.some.inj A).symm
      subst a
      rcases B with B|B|B
      · exact H B
      · cases B
      · exact nonempty (Option.some.inj B)
    · exact ready_not_none rfl
  · intro y Y _ _
    exact Y.1
  · intro t
    have cutMean (y : RenewalState X n) (Y : Q y) (P : prepared y) (u : Nat) :
        iidHitCost nx halt u y≤(Mcap*n)*n^u := by
      obtain ⟨a,A,K⟩ := P
      have J := Y.2
      rw [A] at J
      have E := J.2.2.2 K
      have RP := J.2.1.elim (already_seen_replay S a.anchor sticky) (replay a.anchor J.1)
      have U := trial_mean closed sticky watched RP (trialState y a) J.2.2.1 u
      rw [trial_cost S y a A]
      apply Nat.le_trans U
      apply Nat.mul_le_mul_right
      rw [E,Nat.mul_comm Mcap n]
      apply Nat.mul_le_mul_left
      cases Z : a.anchor.2 <;> simp [rank,start,Z,M]
    have T := TripleRenewal.glue_until_stop nx nx id (fun _ _=>rfl)
      halt prepared Q stay (Mcap*n) t (fun y u Y P _ _=>cutMean y Y P u)
        t (Nat.le_refl _) (init z) (startOk z Z)
    have C := prep_cost_le S Good base project closed t (init z) (startOk z Z) (initial_boundary S z)
    have U := (regenerate z.1 Z) t
    have L := TripleRenewal.terminalMass_le_total nx prepared (fun y=>¬halt y) t (init z)
    rw [Nat.add_mul]
    exact Nat.le_trans T (Nat.add_le_add (Nat.le_trans C U) (Nat.mul_le_mul_left _ L))
  · intro t
    have cutFail (y : RenewalState X n) (Y : Q y) (P : prepared y) (u : Nat) :
        (Wcap^Mcap)*TripleRenewal.terminalMass nx halt (fun k=>k.real.2≠true) u y≤(Wcap^Mcap-1)*n^u := by
      obtain ⟨a,A,K⟩ := P
      have J := Y.2
      rw [A] at J
      have E := J.2.2.2 K
      have RP := J.2.1.elim (already_seen_replay S a.anchor sticky) (replay a.anchor J.1)
      rw [trial_mass S y a A,E]
      exact parked_failure_param closed sticky watched RP J.1 Wcap Mcap Wpos W M u
    have F (u : Nat) (y : RenewalState X n) (Y : Q y) (B : y.active=none ∨ prepared y) :
        (Wcap^Mcap)*TripleRenewal.terminalMass nx halt (fun k=>k.real.2≠true) u y≤(Wcap^Mcap-1)*n^u := by
      induction u generalizing y with
      | zero =>
        rcases B with A|P
        · simp [TripleRenewal.terminalMass,ready_not_none A]
        · exact cutFail y Y P 0
      | succ u ih =>
        rcases B with A|P
        · simp only [TripleRenewal.terminalMass,ready_not_none A,if_false,TaggedTail.sumEdge,
            ←Height.sum_ofFn_mul_left]
          have C (e : Fin n) : (nx y e).active=none ∨ prepared (nx y e) := by
            unfold nx advance
            rw [A]
            exact initial_boundary S _
          have M := Height.sum_ofFn_le _ (fun _ : Fin n=>(Wcap^Mcap-1)*n^u)
            (fun e=>ih _ (stay y e Y) (C e))
          rw [Height.sum_ofFn_const] at M
          calc
            _ ≤ n*((Wcap^Mcap-1)*n^u) := M
            _ = _ := by rw [Nat.pow_succ n u]; ac_rfl
        · exact cutFail y Y P (u+1)
    exact F t (init z) (startOk z Z) (initial_boundary S z)

end L4.ShortPrefixTrial
