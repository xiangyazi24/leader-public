import Leader.L4.ReportPulseRecode
namespace L4.ReportPulseRounds
open ReportPulseRecode
universe u
variable {G : Type u}
structure Scan where
  next : Nat
  waiting : Option Nat
  rounds : List (Nat × Nat)
variable [DecidableEq G]
def Scan.step (g : G) (a : Scan) (e : Option (Event G)) : Scan :=
  let bumped := {a with next:=a.next+1}
  match e with
  | none => bumped
  | some (.start h) => if h=g then {bumped with waiting:=some a.next} else bumped
  | some (.complete h) =>
    if h=g then
      match a.waiting with
      | none => bumped
      | some i => {bumped with waiting:=none,rounds:=a.rounds++[(i,a.next)]}
    else bumped
def scan (g : G) (a : Scan) (w : List (Option (Event G))) : Scan :=
  w.foldl (Scan.step g) a
def extract (g : G) (J : Nat) (w : List (Option (Event G))) : List (Nat × Nat) :=
  let rs := (scan g ⟨0,none,[]⟩ w).rounds
  rs.drop (rs.length-J)

theorem extract_known_suffix (g : G) (w : List (Option (Event G))) (J : Nat)
    (prior suffix : List (Nat × Nat))
    (H : (scan g ⟨0,none,[]⟩ w).rounds=prior++suffix)
    (L : suffix.length=J) : extract g J w=suffix := by
  unfold extract
  dsimp only
  rw [H,List.length_append,L,Nat.add_sub_cancel]
  simp

def Quiet (g : G) (e : Option (Event G)) : Prop :=
  e≠some (.start g) ∧ e≠some (.complete g)

theorem step_quiet (g : G) (a : Scan) (e : Option (Event G)) (Q : Quiet g e) :
    a.step g e={a with next:=a.next+1} := by
  cases e with
  | none => rfl
  | some t =>
    cases t with
    | start h =>
      have H : h≠g := fun E=>Q.1 (by rw [E])
      simp [Scan.step,H]
    | complete h =>
      have H : h≠g := fun E=>Q.2 (by rw [E])
      simp [Scan.step,H]

inductive OpenRound (g : G) : List (Option (Event G)) → Bool → Prop
  | nil : OpenRound g [] false
  | quiet {w b e} : OpenRound g w b → Quiet g e → OpenRound g (w++[e]) b
  | start {w} : OpenRound g w false → OpenRound g (w++[some (.start g)]) true

inductive ClosedRounds (g : G) : Nat → List (Option (Event G)) → Prop
  | zero : ClosedRounds g 0 []
  | snoc {J u v} : ClosedRounds g J u → OpenRound g v true →
    ClosedRounds g (J+1) ((u++v)++[some (.complete g)])

theorem openRound_scan (g : G) (w : List (Option (Event G))) (b : Bool)
    (H : OpenRound g w b) (i : Nat) (rs : List (Nat × Nat)) :
    let a := scan g ⟨i,none,rs⟩ w
    a.next=i+w.length ∧ a.rounds=rs ∧
      (if b then ∃ k, a.waiting=some (i+k) ∧ k<w.length ∧ w[k]?=some (some (.start g))
       else a.waiting=none) := by
  induction H with
  | nil => simp [scan]
  | @quiet w b e B Q IH =>
    dsimp only at IH ⊢
    rw [show scan g ⟨i,none,rs⟩ (w++[e])=(scan g ⟨i,none,rs⟩ w).step g e by
      simp only [scan,List.foldl_append,List.foldl_cons,List.foldl_nil]]
    rw [step_quiet g _ _ Q]
    refine ⟨by simp only [List.length_append,List.length_singleton,IH.1]; omega,IH.2.1,?_⟩
    cases b with
    | false => exact IH.2.2
    | true =>
      obtain ⟨k,A,K,E⟩ := IH.2.2
      refine ⟨k,A,by simp only [List.length_append,List.length_singleton]; omega,?_⟩
      rw [List.getElem?_append_left K]
      exact E
  | @start w W IH =>
    dsimp only at IH ⊢
    rw [show scan g ⟨i,none,rs⟩ (w++[some (.start g)])=
      (scan g ⟨i,none,rs⟩ w).step g (some (.start g)) by
      simp only [scan,List.foldl_append,List.foldl_cons,List.foldl_nil]]
    simp only [Scan.step,if_true,IH.1,IH.2.1,List.length_append,List.length_singleton]
    refine ⟨by omega,trivial,w.length,rfl,by omega,?_⟩
    simp

def PairAt (g : G) (i : Nat) (w : List (Option (Event G))) (entry : Nat × Nat) : Prop :=
  ∃ j k, entry=(i+j,i+k) ∧ j<k ∧ k<w.length ∧
    w[j]?=some (some (.start g)) ∧ w[k]?=some (some (.complete g))

omit [DecidableEq G] in
theorem pair_append (g : G) (i : Nat) (u v : List (Option (Event G))) (entry : Nat × Nat)
    (H : PairAt g i u entry) : PairAt g i (u++v) entry := by
  obtain ⟨j,k,E,J,K,A,B⟩ := H
  exact ⟨j,k,E,J,by simp; omega,by rw [List.getElem?_append_left (Nat.lt_trans J K)]; exact A,
    by rw [List.getElem?_append_left K]; exact B⟩

theorem closedRounds_scan (g : G) (J : Nat) (w : List (Option (Event G)))
    (H : ClosedRounds g J w) (i : Nat) (prior : List (Nat × Nat)) :
    ∃ fresh, fresh.length=J ∧
      (scan g ⟨i,none,prior⟩ w=⟨i+w.length,none,prior++fresh⟩) ∧
      ∀ pair∈fresh, PairAt g i w pair := by
  induction H with
  | zero => exact ⟨[],rfl,by simp [scan],by simp⟩
  | @snoc J u v U V IH =>
    obtain ⟨old,L,E,Cert⟩ := IH
    obtain ⟨Next,Rs,k,K,Bound,Mark⟩ := openRound_scan g v true V (i+u.length) (prior++old)
    unfold scan at E ⊢
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,E]
    let atV := scan g ⟨i+u.length,none,prior++old⟩ v
    change ∃ fresh : List (Nat × Nat), fresh.length=J+1 ∧ (atV.step g (some (.complete g)))=_ ∧ _
    refine ⟨old++[(i+u.length+k,i+u.length+v.length)],by simp [L],?_,?_⟩
    change atV.next=i+u.length+v.length at Next
    change atV.rounds=prior++old at Rs
    change atV.waiting=some (i+u.length+k) at K
    · simp only [Scan.step,if_true,K,Rs,Next,List.length_append,List.length_singleton,List.append_assoc]
      congr 1 <;> omega
    · intro pair Mem
      rw [List.mem_append] at Mem
      rcases Mem with In|Last
      · exact pair_append g i (u++v) _ pair (pair_append g i u v pair (Cert pair In))
      · have One : pair=(i+u.length+k,i+u.length+v.length) := by simpa using Last
        refine ⟨u.length+k,u.length+v.length,?_,by omega,by simp,?_,?_⟩
        · simpa only [Nat.add_assoc] using One
        · rw [List.getElem?_append_left (by simp; omega),List.getElem?_append_right (by omega)]
          rw [show u.length+k-u.length=k by omega]
          exact Mark
        · simp

#print axioms extract_known_suffix
#print axioms openRound_scan
#print axioms closedRounds_scan

theorem scan_next (g : G) (a : Scan) (w : List (Option (Event G))) :
    (scan g a w).next=a.next+w.length := by
  have one (a : Scan) (e : Option (Event G)) : (a.step g e).next=a.next+1 := by
    cases e with
    | none => rfl
    | some t =>
      cases t with
      | start h => by_cases E : h=g <;> simp [Scan.step,E]
      | complete h => by_cases E : h=g <;> cases W : a.waiting <;> simp [Scan.step,E,W]
  induction w generalizing a with
  | nil => simp [scan]
  | cons e w IH =>
    change (scan g (a.step g e) w).next=_
    rw [IH,one]
    simp only [List.length_cons]
    omega

theorem scan_skeleton_pending {Z : Type} (g : G) (s : Armed G)
    (w : List (Label G Z)) (a : Scan) (A : s g=false → a.waiting=none) :
    skeletonState s w g=false → (scan g a (skeleton s w)).waiting=none := by
  induction w generalizing s a with
  | nil => exact A
  | cons e w IH =>
    have one : (skeletonStep s e).1 g=false → (a.step g (skeletonStep s e).2).waiting=none := by
      cases e with
      | inr z => exact A
      | inl ib =>
        obtain ⟨h,b⟩ := ib
        by_cases E : g=h
        · subst h
          cases S : s g <;> cases b <;> cases W : a.waiting <;>
            simp [skeletonStep,advance,S,Scan.step,W]
        · have E' : h≠g := Ne.symm E
          cases S : s h <;> cases b <;> simp [skeletonStep,advance,S,Scan.step,E,E'] <;> exact A
    exact IH _ _ one

theorem skeleton_length {Z : Type} (s : Armed G) (w : List (Label G Z)) :
    (skeleton s w).length=w.length := by
  induction w generalizing s with
  | nil => rfl
  | cons e w IH => simp only [skeleton,List.length_cons,IH]

theorem skeleton_append {Z : Type} (s : Armed G) (u v : List (Label G Z)) :
    skeleton s (u++v)=skeleton s u++skeleton (skeletonState s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons e u IH => simp only [List.cons_append,skeleton,skeletonState,IH]

theorem scan_append (g : G) (s : Scan) (u v : List (Option (Event G))) :
    scan g s (u++v)=scan g (scan g s u) v :=
  List.foldl_append

theorem scan_eta (a : Scan) (i : Nat) (N : a.next=i) (W : a.waiting=none) :
    a=⟨i,none,a.rounds⟩ := by
  cases a
  simp_all

theorem extract_closed_suffix {Z : Type} (g : G) (J : Nat) (s : Armed G)
    (pre post : List (Label G Z))
    (E : skeletonState s pre g=false)
    (C : ClosedRounds g J (skeleton (skeletonState s pre) post)) :
    let pairs := extract g J (skeleton s (pre++post))
    pairs.length=J ∧
      ∀ pair∈pairs, PairAt g pre.length (skeleton (skeletonState s pre) post) pair := by
  let prior := scan g ⟨0,none,[]⟩ (skeleton s pre)
  have W : prior.waiting=none := scan_skeleton_pending g s pre _ (fun _=>rfl) E
  have N : prior.next=pre.length := by
    unfold prior
    rw [scan_next, Nat.zero_add,skeleton_length]
  have B := scan_eta prior pre.length N W
  obtain ⟨fresh,L,F,Cert⟩ := closedRounds_scan g J _ C pre.length prior.rounds
  have Eq : (scan g ⟨0,none,[]⟩ (skeleton s (pre++post))).rounds=prior.rounds++fresh := by
    rw [skeleton_append,scan_append]
    change (scan g prior (skeleton (skeletonState s pre) post)).rounds=_
    exact congrArg Scan.rounds ((congrArg (fun a=>scan g a (skeleton (skeletonState s pre) post)) B).trans F)
  rw [extract_known_suffix g _ J prior.rounds fresh Eq L]
  exact ⟨L,Cert⟩

#print axioms extract_closed_suffix
end L4.ReportPulseRounds
