import Leader.L4.BStarRevealCompletion
import Leader.L4.BStarPhysicalPairLaw

namespace L4.BStarPhysicalCompletion
open L4.Height L4.Height.Couple
open BStarRevealCompletion BStarPhysicalPairLaw
open Classical

def copyBit {n : Nat} : Fin (n+n) → Bool :=
  Fin.addCases (fun _=>false) (fun _=>true)

def swapCopy {n : Nat} : Fin (n+n) → Fin (n+n) :=
  Fin.addCases (Fin.natAdd n) (Fin.castAdd n)

/-- Auxiliary completions use only the otherwise ignored copy bit.
This does not require parity of the actual number of raw ring marks. -/
def copyAux (n : Nat) : Auxiliary (n+n) where
  bit := copyBit
  flip := swapCopy
  invol e := by
    refine Fin.addCases (fun i=>?_) (fun i=>?_) e <;>
      simp only [swapCopy,Fin.addCases_left,Fin.addCases_right]
  opposite e := by
    refine Fin.addCases (fun i=>?_) (fun i=>?_) e <;>
      simp only [swapCopy,copyBit,Fin.addCases_left,Fin.addCases_right,Bool.not_true,Bool.not_false]

theorem copy_swap_raw {n : Nat} (e : Fin (n+n)) :
    rawLabel (swapCopy e)=rawLabel e := by
  refine Fin.addCases (fun i=>?_) (fun i=>?_) e <;>
    simp only [swapCopy,rawLabel,Fin.addCases_left,Fin.addCases_right]

private def mapReveal {ι κ : Type} (coord : ι → Option κ) :
    Option (ι × Bool) → Option (κ × Bool)
  | none => none
  | some (i,b) => (coord i).map (fun k=>(k,b))

/-- Monitor just the chosen keys; relabeling is computed on old keys
and cannot depend on their dispatched BIT value. -/
def project {α ι κ : Type} {n : Nat} (S : PairedSource α ι n) (coord : ι → Option κ) :
    PairedSource α κ n where
  next := S.next
  bitOf x e := mapReveal coord (S.bitOf x e)
  flip := S.flip
  half := S.half
  alphabet_even := S.alphabet_even
  flip_invol := S.flip_invol
  flip_reveal := by
    intro x e k v H
    cases E : S.bitOf x e with
    | none => simp [E,mapReveal] at H
    | some p =>
      obtain ⟨i,b⟩ := p
      rw [S.flip_reveal x e i b E]
      simp only [E,mapReveal] at H
      cases F : coord i with
      | none => simp [F] at H
      | some j =>
        simp only [F,Option.map_some,Option.some.injEq,Prod.mk.injEq] at H
        rcases H with ⟨rfl,rfl⟩
        simp [mapReveal,F]

theorem first_project {α ι κ : Type} {n : Nat} [DecidableEq ι] [DecidableEq κ]
    (S : PairedSource α ι n) (coord : ι→Option κ) (i : ι) (k : κ)
    (unique : ∀ j, coord j=some k ↔ j=i)
    (x : α) (w : List (Fin n)) :
    firstReveal (project S coord) k x w=firstReveal S i x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    cases E : S.bitOf x e with
    | none =>
      simp [firstReveal,project,mapReveal,E]
      exact ih (S.next x e)
    | some p =>
      obtain ⟨j,b⟩ := p
      cases F : coord j with
      | none =>
        have J : j≠i := by
          intro J
          have H := (unique j).2 J
          rw [F] at H
          contradiction
        simp [firstReveal,project,mapReveal,E,F,J]
        exact ih (S.next x e)
      | some q =>
        have J : q=k ↔ j=i := by simpa [F] using unique j
        simp [firstReveal,project,mapReveal,E,F,J]
        split <;> first | rfl | exact ih (S.next x e)

open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- Quarter transfer on the actual n-letter ring scheduler. Only
observed first values constrain completions. The comparison hypothesis
must hold for all such assignments, not just the zero completion. -/
theorem raw_quarter_of_compatible {K : Nat}
    (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (initialTime : Fin n→Nat) (history : List (Fin n)) (t : Nat)
    (coord : Key n→Option (Fin K)) (key : Fin K→Key n)
    (fiber : ∀ k j, coord j=some k ↔ j=key k)
    (E : List (Fin n)→Prop) (F : (Fin K→Bool)→Prop)
    (bad : List (Fin K→Bool)) (distinct : bad.Nodup)
    (exactBad : ∀ a,a∈bad ↔ F a) (quarter : 4*bad.length≤2^K)
    (compare : ∀ u, u.length=t → E u → ∀ a,
      (∀ k b, firstRaw (reveal hp base hh x (ownerAt hp base hh) initialTime)
        (key k) history u=some b → a k=b) → F a) :
    4*wordSum (fun u=>if E u then 1 else 0) t≤n^t := by
  classical
  let S := source hp base hh x (ownerAt hp base hh) initialTime
  let T := project S coord
  have positive : 0<n := by obtain ⟨i,_⟩ := hh; exact Nat.zero_lt_of_lt i.isLt
  have hx (u : List (Fin (n+n))) (a : Fin K→Bool)
      (h : Compatible T history u a) :
      ∀ k b, firstRaw (reveal hp base hh x (ownerAt hp base hh) initialTime)
        (key k) history (u.map rawLabel)=some b → a k=b := by
    intro k b raw
    apply h k b
    rw [first_project S coord _ _ (fiber k), firstReveal_projects]
    exact raw
  have out := quarter_of_compatible T (copyAux n) history t (by omega)
    (fun w=>E (w.map rawLabel)) F bad distinct exactBad quarter
    (fun w len event a fit=>compare _ (by simpa using len) event a (hx w a fit))
  let f : List (Fin n)→Nat := fun w=>if E w then 1 else 0
  change 4*wordSum (fun w=>f (w.map rawLabel)) t≤(n+n)^t at out
  rw [doubled_wordSum,←Nat.two_mul,Nat.mul_pow,Nat.mul_left_comm 4 (2^t)] at out
  exact Nat.le_of_mul_le_mul_left out (Nat.pow_pos (by decide))

#print axioms copy_swap_raw
#print axioms project
#print axioms first_project
#print axioms raw_quarter_of_compatible
end L4.BStarPhysicalCompletion
