import Leader.L4.BStarCommitOperands

namespace L4.BStarAcquireBirthUnique
open AllSizeProtocol BStarTrace BStarLongGrant BStarLongClaims BStarLongLayout BStarLongWork BStarLongToken BStarLongCommand
open BStarGrantBirth BStarCommitOperands BStarH6WordChart

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

theorem win_old_clear (o release ask : Ports) (j : Fin 3)
    (h : win o release ask j=true) : o j=false := by
  cases H : o 1
  · by_cases J : j=1
    · rwa [J]
    · simp [win,canonical,H,J,Bool.and_eq_true] at h
      exact h.1.2
  · by_cases J : j=1
    · subst j
      simp [win,canonical,H] at h
    · simp [win,canonical,H,J] at h

theorem won_old_clear {x : X} {e i : Fin n} {j : Fin 3}
    (h : WonAt hp x e i j) : bit x i j=0 := by
  obtain ⟨side,rfl,_,W,_⟩ := h
  have clear := win_old_clear _ _ _ _ W
  have E : atOld ((x e).long,(x (rightNeighbor e)).long) side =
      (x (site e side)).long := by cases side <;> rfl
  rw [E] at clear
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have K : k=0 := by omega
  subst k
  exact clear

/-- On a single mark word two acquisitions of the same physical bit
that are continuous to the same cut have the very same birth mark.
The winner must see the old bit clear, not merely a successful reply. -/
theorem same_birth {x : X} {i : Fin n} {j : Fin 3}
    {w l r ls rs : List (Fin n)} {e f : Fin n}
    (L : w=l++e::ls) (R : w=r++f::rs)
    (Hl : WonAt hp (run x l) e i j) (Hr : WonAt hp (run x r) f i j)
    (Cl : Continuous hp (step (run x l) e) i j ls)
    (Cr : Continuous hp (step (run x r) f) i j rs) :
    l=r ∧ e=f ∧ ls=rs := by
  have noEarlier (a b asuf bsuf : List (Fin n)) (u v : Fin n)
      (A : w=a++u::asuf) (D : w=b++v::bsuf)
      (C : Continuous hp (step (run x a) u) i j asuf)
      (W : WonAt hp (run x b) v i j) : ¬a.length<b.length := by
    intro lt
    have E : w=(a++[u])++asuf := by simpa [List.append_assoc] using A
    rcases List.append_eq_append_iff.mp (E.symm.trans D) with ⟨q,Q,T⟩|⟨q,Q,T⟩
    · have alive := C q (v::bsuf) T
      have S : run (step (run x a) u) q=run x b := by
        rw [Q, BStarResetSchedule.run_append step x (a++[u]) q,
          BStarResetSchedule.run_append step x a [u]]
        rfl
      exact alive (S.symm ▸ won_old_clear hp W)
    · have lengths := congrArg List.length Q
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      have eq : q=[] := List.length_eq_zero_iff.mp (show q.length=0 by omega)
      subst q
      simp only [List.append_nil] at Q
      have alive := C [] asuf (List.nil_append _).symm
      have S : run (step (run x a) u) []=run x b := by
        rw [←Q,BStarResetSchedule.run_append]
        rfl
      exact alive (S.symm ▸ won_old_clear hp W)
  have le := Nat.le_of_not_gt (noEarlier r l rs ls f e R L Cr Hl)
  have ge := Nat.le_of_not_gt (noEarlier l r ls rs e f L R Cl Hr)
  have E := congrArg (List.take l.length) (L.symm.trans R)
  rw [List.take_append_of_le_length (Nat.le_refl l.length),List.take_length,
      List.take_append_of_le_length le,List.take_of_length_le ge] at E
  subst r
  have tails : e::ls=f::rs := by simpa only [List.append_right_inj] using L.symm.trans R
  exact ⟨rfl,List.cons.inj tails⟩

theorem same_acquisition {x : X} {cut w : List (Fin n)}
    {i : Fin n} {j : Fin 3} (A D : Acquisition hp x cut w i j) :
    A.lead=D.lead ∧ A.mark=D.mark ∧ A.post=D.post :=
  same_birth hp A.exactTape D.exactTape A.won D.won A.live D.live

/-- A witness from the full prepublication word may be compared with
a shorter physical COPY witness. It is enough to know its birth lies
inside the shorter word; all later continuity obligations can be cropped. -/
theorem same_birth_extended {x : X} {cut w more r rs : List (Fin n)}
    {i : Fin n} {j : Fin 3} {f : Fin n}
    (A : Acquisition hp x cut w i j)
    (E : w++more=r++f::rs) (born : r.length<w.length)
    (H : WonAt hp (run x r) f i j)
    (C : Continuous hp (step (run x r) f) i j rs) :
    A.lead=r ∧ A.mark=f ∧ rs=A.post++more := by
  have Et : w++more=(r++[f])++rs := by simpa [List.append_assoc] using E
  have crop : ∃ mid,w=(r++[f])++mid ∧ rs=mid++more := by
    rcases List.append_eq_append_iff.mp Et with ⟨q,Q,F⟩|⟨q,Q,F⟩
    · have L := congrArg List.length Q
      simp only [List.length_append,List.length_cons,List.length_nil] at L
      have eq : q=[] := List.length_eq_zero_iff.mp (show q.length=0 by omega)
      subst q
      exact ⟨[],by simpa using Q.symm,by simpa using F.symm⟩
    · exact ⟨q,Q,F⟩
  obtain ⟨mid,G,F⟩ := crop
  have CC : Continuous hp (step (run x r) f) i j mid := by
    intro u v UV
    exact C u (v++more) (by rw [F,UV,List.append_assoc])
  have R : w=r++f::mid := by simpa [List.append_assoc] using G
  obtain ⟨W,M,V⟩ := same_birth hp A.exactTape R A.won H A.live CC
  exact ⟨W,M,F.trans (congrArg (·++more) V.symm)⟩

#print axioms win_old_clear
#print axioms won_old_clear
#print axioms same_birth
#print axioms same_acquisition
#print axioms same_birth_extended
end L4.BStarAcquireBirthUnique
