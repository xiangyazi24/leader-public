import Leader.L4.GGTiming

namespace L4.UnisonStages

/-- Literal consequences of the five prioritized normalized signed
rows, kept as an interface for the round arithmetic. The caller must
establish this interface for its chosen serial atomic activation. -/
structure Rows (α : Type) (m : Nat) where
  P : Int
  value : α → Fin m → Int
  error : α → Fin m → Prop
  next : α → Fin m → α
  near : Fin m → Fin m → Prop
  symm : ∀ {u v}, near u v → near v u
  good : α → Prop
  quiet : α → Prop
  legal : α → Prop
  good_step : ∀ x e, good x → good (next x e)
  quiet_step : ∀ x e, good x → quiet x → quiet (next x e)
  frame : ∀ x e v, v≠e → value (next x e) v=value x v ∧
    (error (next x e) v ↔ error x v)
  negative : ∀ x v, good x → error x v → value x v<0
  error_step : ∀ x v, good x → quiet x → error (next x v) v →
    (error x v ∧ value (next x v) v=value x v) ∨
    ∃ u, near u v ∧ error x u ∧ value (next x v) v=value x u+1 ∧
      value (next x v) v<value x v
  raise_step : ∀ x u v, good x → quiet x → near u v → error x u →
    value x v≤value x u+1 → value (next x v) v≤value x u+1
  prop_on_gap : ∀ x u v, good x → quiet x → near u v → error x u →
    value x u+1<0 → value x u+1<value x v →
    value (next x v) v≤value x u+1
  no_correct_lower_gap : ∀ x u v, good x → quiet x → near u v →
    ¬error x u → error x v → value x v≤value x u+1
  clear : ∀ x v, good x → quiet x → error x v →
    (∀ u, near u v → value x u≤value x v+1 ∧ value x v≤value x u+1) →
    (∀ u, near u v → error x u → value x u≤value x v) →
    ¬error (next x v) v
  quiet_no_errors : ∀ x, good x → quiet x → (∀ v, ¬error x v) → legal x

variable {α : Type} {m : Nat}

def Flood (S : Rows α m) (h : Int) (x : α) : Prop :=
  ∀ u v, S.near u v → S.error x u → S.value x u<h → S.value x v≤S.value x u+1

def Frozen (S : Rows α m) (x : α) : Prop :=
  ∀ u v, S.near u v → S.error x u → S.value x v≤S.value x u+1

def Below (S : Rows α m) (h : Int) (x : α) : Prop :=
  ∀ u, S.error x u → S.value x u<h

def floodDomain (S : Rows α m) (h : Int) (x : α) : Prop :=
  S.good x ∧ S.quiet x ∧ Flood S h x

theorem low_step (S : Rows α m) (h : Int) (x : α) (e u : Fin m)
    (hx : floodDomain S h x) (he : S.error (S.next x e) u)
    (hl : S.value (S.next x e) u≤h) :
    S.error x u ∧ S.value (S.next x e) u=S.value x u := by
  by_cases H : u=e
  · subst u
    rcases S.error_step x e hx.1 hx.2.1 he with ha|⟨v,hn,hE,hV,hd⟩
    · exact ha
    · have hg := hx.2.2 v e hn hE (by omega)
      omega
  · obtain ⟨hV,heq⟩ := S.frame x e u H
    exact ⟨heq.mp he,hV⟩

private theorem cap_step (S : Rows α m) (x : α) (e u v : Fin m)
    (hGood : S.good x) (hQuiet : S.quiet x) (hn : S.near u v)
    (hE : S.error x u) (hU : S.value (S.next x e) u=S.value x u)
    (hCap : S.value x v≤S.value x u+1) :
    S.value (S.next x e) v≤S.value (S.next x e) u+1 := by
  rw [hU]
  by_cases h : v=e
  · subst v
    exact S.raise_step x u e hGood hQuiet hn hE hCap
  · rw [(S.frame x e v h).1]
    exact hCap

theorem flood_closed (S : Rows α m) (h : Int) (x : α) (e : Fin m)
    (hx : floodDomain S h x) : floodDomain S h (S.next x e) := by
  refine ⟨S.good_step x e hx.1,S.quiet_step x e hx.1 hx.2.1,?_⟩
  intro u v hn he hl
  obtain ⟨ho,hu⟩ := low_step S h x e u hx he (by omega)
  exact cap_step S x e u v hx.1 hx.2.1 hn ho hu (hx.2.2 u v hn ho (by omega))

private theorem low_and_cap_run (S : Rows α m) (h : Int) (x : α) (w : List (Fin m))
    (hx : floodDomain S h x) (u v : Fin m) (hn : S.near u v)
    (he : S.error (GGTiming.runMarks S.next x w) u)
    (hl : S.value (GGTiming.runMarks S.next x w) u≤h) :
    S.error x u ∧ S.value (GGTiming.runMarks S.next x w) u=S.value x u ∧
      (S.value x v≤S.value x u+1 →
        S.value (GGTiming.runMarks S.next x w) v≤
          S.value (GGTiming.runMarks S.next x w) u+1) := by
  induction w generalizing x with
  | nil => exact ⟨he,rfl,id⟩
  | cons e w ih =>
    simp only [GGTiming.runMarks] at he hl ⊢
    obtain ⟨hE,hV,hP⟩ := ih (S.next x e) (flood_closed S h x e hx) he hl
    obtain ⟨hO,hU⟩ := low_step S h x e u hx hE (by omega)
    exact ⟨hO,hV.trans hU,fun h => hP (cap_step S x e u v hx.1 hx.2.1 hn hO hU h)⟩

/-- One flood advance after any raw word containing each centre, not
just a particular permutation. Follow a final surviving low error
back through the cover, then preserve its local cap after service. -/
theorem flood_cover (S : Rows α m) (h : Int) (x : α) (w : List (Fin m))
    (hNeg : h+1<0) (hx : floodDomain S h x) (cover : ∀ e, e∈w) :
    Flood S (h+1) (GGTiming.runMarks S.next x w) := by
  intro u v hn he hl
  have aux (x : α) (w : List (Fin m)) (hx : floodDomain S h x)
      (hv : v∈w) (he : S.error (GGTiming.runMarks S.next x w) u)
      (hl : S.value (GGTiming.runMarks S.next x w) u≤h) :
      S.value (GGTiming.runMarks S.next x w) v≤
        S.value (GGTiming.runMarks S.next x w) u+1 := by
    induction w generalizing x with
    | nil => simp at hv
    | cons e w ih =>
      simp only [GGTiming.runMarks] at he hl ⊢
      have hNext := flood_closed S h x e hx
      by_cases hEq : e=v
      · subst e
        obtain ⟨hE,hV,hProp⟩ := low_and_cap_run S h (S.next x v) w hNext u v hn he hl
        obtain ⟨hOld,hU⟩ := low_step S h x v u hx hE (by omega)
        apply hProp
        by_cases hc : S.value x v≤S.value x u+1
        · exact cap_step S x v u v hx.1 hx.2.1 hn hOld hU hc
        · rw [hU]
          exact S.prop_on_gap x u v hx.1 hx.2.1 hn hOld (by omega) (by omega)
      · exact ih (S.next x e) hNext ((List.mem_cons.mp hv).resolve_left (Ne.symm hEq)) he hl
  exact aux x w hx (cover v) he (by omega)

theorem frozen_step (S : Rows α m) (x : α) (e u : Fin m)
    (hg : S.good x) (hq : S.quiet x) (hf : Frozen S x)
    (he : S.error (S.next x e) u) :
    S.error x u ∧ S.value (S.next x e) u=S.value x u := by
  by_cases h : u=e
  · subst u
    rcases S.error_step x e hg hq he with heq|⟨v,hn,hv,hV,hLt⟩
    · exact heq
    · have hh := hf v e hn hv
      omega
  · have hF := S.frame x e u h
    exact ⟨hF.2.mp he,hF.1⟩

def clearDomain (S : Rows α m) (h : Int) (x : α) : Prop :=
  S.good x ∧ S.quiet x ∧ Frozen S x ∧ Below S h x

theorem clear_closed (S : Rows α m) (h : Int) (x : α) (e : Fin m)
    (hx : clearDomain S h x) : clearDomain S h (S.next x e) := by
  refine ⟨S.good_step x e hx.1,S.quiet_step x e hx.1 hx.2.1,?_,?_⟩
  · intro u v hn he
    obtain ⟨hO,hV⟩ := frozen_step S x e u hx.1 hx.2.1 hx.2.2.1 he
    exact cap_step S x e u v hx.1 hx.2.1 hn hO hV (hx.2.2.1 u v hn hO)
  · intro u he
    obtain ⟨hO,hV⟩ := frozen_step S x e u hx.1 hx.2.1 hx.2.2.1 he
    rw [hV]
    exact hx.2.2.2 u hO

private theorem frozen_run (S : Rows α m) (h : Int) (x : α) (w : List (Fin m))
    (hx : clearDomain S h x) (u : Fin m) (he : S.error (GGTiming.runMarks S.next x w) u) :
    S.error x u ∧ S.value (GGTiming.runMarks S.next x w) u=S.value x u := by
  induction w generalizing x with
  | nil => exact ⟨he,rfl⟩
  | cons e w ih =>
    simp only [GGTiming.runMarks] at he ⊢
    obtain ⟨hE,hV⟩ := ih (S.next x e) (clear_closed S h x e hx) he
    obtain ⟨hO,hU⟩ := frozen_step S x e u hx.1 hx.2.1 hx.2.2.1 hE
    exact ⟨hO,hV.trans hU⟩

theorem clear_cover (S : Rows α m) (h : Int) (x : α) (w : List (Fin m))
    (hx : clearDomain S h x) (cover : ∀ e, e∈w) :
    Below S (h-1) (GGTiming.runMarks S.next x w) := by
  intro v he
  have aux (x : α) (w : List (Fin m)) (hx : clearDomain S h x)
      (hv : v∈w) (he : S.error (GGTiming.runMarks S.next x w) v) :
      S.value (GGTiming.runMarks S.next x w) v<h-1 := by
    induction w generalizing x with
    | nil => simp at hv
    | cons e w ih =>
      simp only [GGTiming.runMarks] at he ⊢
      have hNext := clear_closed S h x e hx
      by_cases hEq : e=v
      · subst e
        obtain ⟨hE,hV⟩ := frozen_run S h (S.next x v) w hNext v he
        obtain ⟨hO,hU⟩ := frozen_step S x v v hx.1 hx.2.1 hx.2.2.1 hE
        have hLt := hx.2.2.2 v hO
        by_cases hLow : S.value x v<h-1
        · omega
        have hCl := S.clear x v hx.1 hx.2.1 hO
          (fun u hn => ⟨hx.2.2.1 v u (S.symm hn) hO,by
            classical
            by_cases h : S.error x u
            · exact hx.2.2.1 u v hn h
            · exact S.no_correct_lower_gap x u v hx.1 hx.2.1 hn h hO⟩)
          (fun u _ hu => by have hh := hx.2.2.2 u hu; omega)
        exact (hCl hE).elim
      · exact ih (S.next x e) hNext ((List.mem_cons.mp hv).resolve_left (Ne.symm hEq)) he
  exact aux x w hx (cover v) he

end L4.UnisonStages
