import Leader.L4.PhysicalCustodyH1Auth

namespace L4.PhysicalCustody.H1
open L4.AllSizeProtocol PhysicalMIS

abbrev Role := Fin 5

def roleCode (x : Byte) : Role := ⟨role x, by unfold role; split <;> omega⟩

def rolePair (a b : Role) : Role × Role :=
  if a=0 ∧ b=0 then (3,1)
  else if a=1 ∧ (b=0 ∨ b=4) then (2,4)
  else (if a=2 ∨ a=1 ∨ a=3 then 0 else a,
        if b=2 ∨ b=1 ∨ b=4 then 0 else b)

theorem exact_role_pair : ∀ x y : Byte,
    (roleCode (next (x,y)).1, roleCode (next (x,y)).2) =
      rolePair (roleCode x) (roleCode y) := by
  decide +kernel

abbrev Window := Fin 5 → Role

def localStep (x : Window) (e : Fin 4) : Window :=
  let a : Fin 5 := ⟨e.val, by omega⟩
  let b : Fin 5 := ⟨e.val+1, by omega⟩
  let y := rolePair (x a) (x b)
  fun i => if i=a then y.1 else if i=b then y.2 else x i

def localRun (x : Window) (w : List (Fin 4)) : Window :=
  w.foldl localStep x

/-- The tile labels 0,1,2,3 act on sites 0–1, 1–2, 2–3, 3–4;
site 2 is the centre. Put the centre idle, name its left helper,
and make its right neighbor idle or ready to help. -/
def forcing (x : Window) : List (Fin 4) :=
  let p : List (Fin 4) :=
    if x 2=0 then [] else if x 2=3 then [2]
    else if x 2=4 ∧ x 1=1 then [1,1] else [1]
  let y := localRun x p
  let q : List (Fin 4) :=
    if y 1=0 then [] else if y 1=3 then [1]
    else if y 1=4 ∧ y 0=1 then [0,0] else [0]
  let z := localRun y q
  let r : List (Fin 4) := if z 3=0 ∨ z 3=4 then []
    else if z 3=1 ∧ (z 4=0 ∨ z 4=4) then [3,3] else [3]
  p++q++r++[1,2]

def fiveRoles (a b c d e : Role) : Window :=
  fun i => if i=0 then a else if i=1 then b else if i=2 then c else if i=3 then d else e

/-- Complete symbolic role alphabet, not a sample of scheduler words.
Appending label 1 commits the armed centre. All four used labels lie
in the six labels incident to the five-site window. -/
theorem fiveRoles_arm : ∀ (a b c d e : Role),
    let x := fiveRoles a b c d e
    (forcing x).length+1≤9 ∧ localRun x (forcing x) 2=2 := by
  decide +kernel

theorem window_arm (x : Window) :
    (forcing x).length+1≤9 ∧ localRun x (forcing x) 2=2 := by
  have E : x=fiveRoles (x 0) (x 1) (x 2) (x 3) (x 4) := by
    funext i
    have H : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases H with H|H|H|H|H <;> subst i <;> simp [fiveRoles]
  exact E.symm ▸ fiveRoles_arm (x 0) (x 1) (x 2) (x 3) (x 4)

open L4.AllSizeS1Geometry

def tileLeft (e : Fin 4) : Fin 5 := ⟨e.val,by omega⟩
def tileRight (e : Fin 4) : Fin 5 := ⟨e.val+1,by omega⟩

def observe {n : Nat} (p : Fin 5 → Fin n) (x : State n) : Window :=
  fun i => roleCode (x (p i))

theorem observe_step {n : Nat} (p : Fin 5 → Fin n)
    (inj : ∀ {i j}, p i=p j → i=j)
    (edge : ∀ e, rightNeighbor (p (tileLeft e))=p (tileRight e))
    (x : State n) (e : Fin 4) :
    observe p (physicalStep x (p (tileLeft e)))=localStep (observe p x) e := by
  have same (i j : Fin 5) : p i=p j ↔ i=j := ⟨inj, congrArg p⟩
  funext i
  change roleCode (if p i=p (tileLeft e) then
      (next (x (p (tileLeft e)),x (rightNeighbor (p (tileLeft e))))).1
    else if p i=rightNeighbor (p (tileLeft e)) then
      (next (x (p (tileLeft e)),x (rightNeighbor (p (tileLeft e))))).2
    else x (p i)) = _
  rw [edge]
  simp only [same]
  change _ = if i=tileLeft e then (rolePair (roleCode (x (p (tileLeft e))))
      (roleCode (x (p (tileRight e))))).1
    else if i=tileRight e then (rolePair (roleCode (x (p (tileLeft e))))
      (roleCode (x (p (tileRight e))))).2 else roleCode (x (p i))
  have E := exact_role_pair (x (p (tileLeft e))) (x (p (tileRight e)))
  split
  · exact congrArg Prod.fst E
  · split
    · exact congrArg Prod.snd E
    · rfl

theorem observe_run {n : Nat} (p : Fin 5 → Fin n)
    (inj : ∀ {i j}, p i=p j → i=j)
    (edge : ∀ e, rightNeighbor (p (tileLeft e))=p (tileRight e))
    (x : State n) (w : List (Fin 4)) :
    observe p (L4.BStarResetSchedule.run physicalStep x
      (w.map (fun e => p (tileLeft e))))=localRun (observe p x) w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    change observe p (L4.BStarResetSchedule.run physicalStep
      (physicalStep x (p (tileLeft e))) (w.map (fun e => p (tileLeft e)))) =
      localRun (localStep (observe p x) e) w
    rw [ih,observe_step p inj edge]

/-- A fixed tape depending on the old five role bytes arms the centre
in at most eight marks, then the designated incoming mark commits it. -/
theorem apt_service_word {n : Nat} (p : Fin 5 → Fin n)
    (inj : ∀ {i j}, p i=p j → i=j)
    (edge : ∀ e, rightNeighbor (p (tileLeft e))=p (tileRight e))
    (x : State n) :
    ∃ w : List (Fin n), w.length+1≤9 ∧
      (∀ e∈w, ∃ q : Fin 4, e=p (tileLeft q)) ∧
      role (L4.BStarResetSchedule.run physicalStep x w (p 2))=2 := by
  let q := forcing (observe p x)
  have H := window_arm (observe p x)
  refine ⟨q.map (fun e=>p (tileLeft e)), by simpa [q] using H.1, ?_, ?_⟩
  · intro e he
    obtain ⟨i,_,E⟩ := List.mem_map.mp he
    exact ⟨i,E.symm⟩
  · have E := congrFun (observe_run p inj edge x q) (2 : Fin 5)
    rw [H.2] at E
    exact congrArg Fin.val E

end L4.PhysicalCustody.H1
