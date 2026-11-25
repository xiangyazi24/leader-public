import Leader.L4.PhysicalCustodyCommonWord

namespace L4.PhysicalCustodySampledPass
open PhysicalCustody PhysicalCustodyCommonWord
open BStarRecoveryPass

abbrev W (n : Nat) := List (Fin n)

/-- Each argument is a real replay of a sampled segment, started at
its actual old raw state. The two word fields distinguish sampled
order from the order in which the local event is authenticated. -/
inductive Pass {s n : Nat} {Owner : Type} (E : Owner → Raw s n → W n → Prop) :
    Raw s n → List Owner → W n → W n → Prop where
  | nil (x) : Pass E x [] [] []
  | cons {x : Raw s n} {o : Owner} {os : List Owner} {a b u v : W n} :
      Commuted a b → 0<b.length → E o x b →
      Pass E (rawRun x a) os u v → Pass E x (o::os) (a++u) (b++v)

theorem one_pass {s n : Nat} {Owner : Type} {E : Owner→Raw s n→W n→Prop}
    {x : Raw s n} {owners : List Owner} {u v : W n} (P : Pass E x owners u v) :
    Commuted u v ∧ ∀ o∈owners, ∃ j k,j<k ∧ Credit (rawNext s) E o x v j k := by
  induction P with
  | nil x => exact ⟨.refl _,by simp⟩
  | @cons x o os a b u v warp L H _ ih =>
    refine ⟨commute_append warp ih.1,?_⟩
    intro p M
    rcases List.mem_cons.mp M with rfl|M
    · exact ⟨0,b.length,L,[],b,v,rfl,rfl,rfl,H⟩
    · obtain ⟨j,k,jk,A⟩ := ih.2 p M
      rw [rawRun_of_commuted x warp] at A
      exact ⟨b.length+j,b.length+k,by omega,credit_shift (rawNext s) b A⟩

/-- Both passes certify one chronological word and its unchanged complete
raw endpoint. The suffix is the actual subsequent sampled word. -/
theorem two_sampled_passes {s n : Nat} {Owner : Type} {E F : Owner→Raw s n→W n→Prop}
    {x : Raw s n} {owners : List Owner} {u v u' v' : W n} (tail : W n)
    (A : Pass E x owners u u') (B : Pass F (rawRun x u) owners v v') :
    rawRun x u = rawRun x u' ∧
    rawRun x ((u++v)++tail)=rawRun x ((u'++v')++tail) ∧
    (∀ o∈owners, ∃ a b, a<b ∧ b≤u'.length ∧
      Credit (rawNext s) E o x ((u'++v')++tail) a b) ∧
    (∀ o∈owners, ∃ a b, u'.length≤a ∧ a<b ∧ b≤(u'++v').length ∧
      Credit (rawNext s) F o x ((u'++v')++tail) a b) :=
  replay_two_passes x owners u v u' v' tail (one_pass A).1 (one_pass B).1 E F (one_pass A).2 (one_pass B).2

/-- For each explicit owner segment retain both words. The validity
test recurses from the actual sampled endpoint, not from an
independently chosen existential recovery state. -/
abbrev Segment (Owner : Type) (n : Nat) := Owner × W n × W n

def validSegments {s n : Nat} {Owner : Type} (E : Owner → Raw s n → W n → Prop) :
    Raw s n → List (Segment Owner n) → Prop
  | _, [] => True
  | x, (o,a,b)::rest =>
      Commuted a b ∧ 0<b.length ∧ E o x b ∧ validSegments E (rawRun x a) rest

theorem pass_of_segments {s n : Nat} {Owner : Type} (E : Owner→Raw s n→W n→Prop)
    (x : Raw s n) (ls : List (Segment Owner n)) (H : validSegments E x ls) :
    Pass E x (ls.map Prod.fst) (ls.flatMap fun t=>t.2.1) (ls.flatMap fun t=>t.2.2) := by
  induction ls generalizing x with
  | nil => exact .nil _
  | cons a ls ih =>
    obtain ⟨o,u,v⟩ := a
    obtain ⟨C,L,evt,T⟩ := H
    exact .cons C L evt (ih _ T)

end L4.PhysicalCustodySampledPass
