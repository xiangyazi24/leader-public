import Leader.L4.BStarParkedSteering
import Leader.L4.BStarPaceCount

namespace L4.Height.AdmissionMask
open BStarSteeredLikelihood BStarSteeringSupport BStarParkedSteering BStarPaceCount BStarAdmitIncidentGeometry
open BStarClearanceRaceMark BStarLongClaims BStarH6Ordinal
open Classical
noncomputable section

variable {n : Nat}

/-- A credit follows one owner. Its input predicates inspect the old emitted
prefix and the physical firing. The credit begins empty at the query. -/
def advanceCredit (credit : Bool) (issue hit : Prop) : Bool :=
  if issue then true else if hit then false else credit

def creditRun (issue hit : Word n → Fin n → Prop) :
    Word n → Bool → Word n → Bool
  | _,b,[] => b
  | a,b,e::v => creditRun issue hit (a++[e])
      (advanceCredit b (issue a e) (hit a e)) v

def credit (issue hit : Word n → Fin n → Prop) (a : Word n) :=
  creditRun issue hit [] false a

private theorem run_append (issue hit : Word n → Fin n → Prop) (a u v : Word n) (b : Bool) :
    creditRun issue hit a b (u++v) =
      creditRun issue hit (a++u) (creditRun issue hit a b u) v := by
  induction u generalizing a b with
  | nil => simp [creditRun]
  | cons e u ih => simp only [List.cons_append,creditRun,ih,List.append_assoc,List.nil_append]

theorem credit_snoc (issue hit : Word n → Fin n → Prop) (a : Word n) (e : Fin n) :
    credit issue hit (a++[e])=advanceCredit (credit issue hit a) (issue a e) (hit a e) := by
  simp [credit,run_append,creditRun]

def hitAt (gate : Fin n) (live : Word n → Prop) (a : Word n) (e : Fin n) : Prop :=
  live a ∧ ∃ s, e=incident gate s

def mask (h : Fin n → Bool) (hh : ∃ i,h i=true) (gate : Fin 5 → Fin n)
    (issue : Fin 5 → Word n → Fin n → Prop) (live : Fin 5 → Word n → Prop)
    (pick : Word n → Fin n → Side) :=
  redirectTo h hh (fun a i => ∃ j, i=gate j ∧ live j a ∧
    credit (issue j) (hitAt (gate j) (live j)) a=true) pick

private theorem decision_source (h : Fin n → Bool) (hh : ∃ i,h i=true) (gate : Fin 5 → Fin n)
    (issue : Fin 5 → Word n → Fin n → Prop) (live : Fin 5 → Word n → Prop)
    (pick : Word n → Fin n → Side) (a : Word n) (e : Fin n)
    (p : ∃ f, mask h hh gate issue live pick a f=some e) :
    ∃ j, credit (issue j) (hitAt (gate j) (live j)) a=true ∧ hitAt (gate j) (live j) a e := by
  obtain ⟨f,F⟩ := p
  obtain ⟨i,s,_,⟨j,rfl,liveNow,armed⟩,_,mate⟩ :=
    redirectTo_isFresh h hh _ pick a f e F
  exact ⟨j,armed,liveNow,⟨opposite s,mate⟩⟩

/-- A genuine launch funds its first eligible incident mark independently of
the old credit and of any unrelated marks between launch and gate. -/
theorem credit_after_launch (issue hit : Word n → Fin n → Prop) (a : Word n) (e : Fin n)
    (w : Word n) (I : issue a e)
    (untouched : ∀ u f v, w=u++f::v → ¬hit ((a++[e])++u) f) :
    credit issue hit ((a++[e])++w)=true := by
  have keep (p t : Word n) (b : credit issue hit p=true)
      (no : ∀ u f v, t=u++f::v → ¬hit (p++u) f) : credit issue hit (p++t)=true := by
    induction t generalizing p with
    | nil => simpa using b
    | cons f v ih =>
      have off : ¬hit p f := by simpa using no [] f v rfl
      have funded : credit issue hit (p++[f])=true := by
        rw [credit_snoc]
        by_cases new : issue p f <;> simp [advanceCredit,new,off,b]
      have later (u : Word n) (j : Fin n) (z : Word n) (eq : v=u++j::z) : ¬hit ((p++[f])++u) j := by
        simpa only [List.append_assoc,List.singleton_append,List.nil_append] using no (f::u) j z (congrArg (List.cons f) eq)
      simpa only [List.append_assoc,List.singleton_append,List.nil_append] using ih _ funded later
  apply keep _ _ _ untouched
  simp [credit_snoc,advanceCredit,I]

private def paid (issue hit : Word n → Fin n → Prop) (a : Word n) (e : Fin n) :=
  if credit issue hit a=true ∧ hit a e then 1 else 0

private theorem spends (issue hit : Word n → Fin n → Prop) (a v : Word n) :
    charges (paid issue hit) a v ≤
      (credit issue hit a).toNat + charges (fun p e => if issue p e then 1 else 0) a v := by
  induction v generalizing a with
  | nil => simp [charges]
  | cons e v ih =>
    have tail := ih (a++[e])
    rw [credit_snoc] at tail
    simp only [charges]
    cases cb : credit issue hit a <;> by_cases i : issue a e <;> by_cases h : hit a e <;>
      simp [paid,cb,advanceCredit,i,h] at tail ⊢ <;> omega

private theorem five_le_sum (f : Fin 5 → Nat) (i : Fin 5) :
    f i ≤ f 0+f 1+f 2+f 3+f 4 := by
  match i with
  | ⟨0,_⟩ => change f 0 ≤ _; omega
  | ⟨1,_⟩ => change f 1 ≤ _; omega
  | ⟨2,_⟩ => change f 2 ≤ _; omega
  | ⟨3,_⟩ => change f 3 ≤ _; omega
  | ⟨4,_⟩ => change f 4 ≤ _; omega

theorem decisions_le_issues (h : Fin n → Bool) (hh : ∃ i,h i=true) (gate : Fin 5 → Fin n)
    (issue : Fin 5 → Word n → Fin n → Prop) (live : Fin 5 → Word n → Prop)
    (pick : Word n → Fin n → Side) (v : Word n) :
    let cnt := fun j : Fin 5 => charges (fun p e => if issue j p e then 1 else 0) [] v
    decisions (prescribed (mask h hh gate issue live pick)) [] v ≤
      5 + ((cnt 0-1)+(cnt 1-1)+(cnt 2-1)+(cnt 3-1)+(cnt 4-1)) := by
  let R := mask h hh gate issue live pick
  let use (j : Fin 5) := paid (issue j) (hitAt (gate j) (live j))
  let U (j : Fin 5) := charges (use j)
  have every (a : Word n) (e : Fin n) : prescribed R a e ≤
      use 0 a e+use 1 a e+use 2 a e+use 3 a e+use 4 a e := by
    by_cases P : ∃ f,R a f=some e
    · rw [prescribed,if_pos P]
      obtain ⟨j,armed,active⟩ := decision_source h hh gate issue live pick a e P
      have one : use j a e=1 := by simp [use,paid,armed,active]
      exact one ▸ five_le_sum (fun k => use k a e) j
    · simp [prescribed,P]
  have all (a w : Word n) : decisions (prescribed R) a w ≤
      U 0 a w+U 1 a w+U 2 a w+U 3 a w+U 4 a w := by
    induction w generalizing a with
    | nil => simp [decisions,U,charges]
    | cons e w ih =>
      have E := every a e
      have T := ih (a++[e])
      simp only [U,decisions,charges] at T ⊢
      omega
  have per (j : Fin 5) : U j [] v ≤
      charges (fun p e => if issue j p e then 1 else 0) [] v := by
    simpa [U,use,credit,creditRun] using spends (issue j) (hitAt (gate j) (live j)) [] v
  have H := all [] v
  have p₀ := per 0
  have p₁ := per 1
  have p₂ := per 2
  have p₃ := per 3
  have p₄ := per 4
  dsimp only
  change decisions (prescribed R) [] v ≤ _
  omega

#print axioms decisions_le_issues
end
end L4.Height.AdmissionMask
