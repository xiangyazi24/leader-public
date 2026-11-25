import Leader.L4.BStarCommitGeneratedTail

namespace L4.BStarCommitTailScan
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongDoor BStarH6WordChart
open BStarLongWork BStarAcquireWaitControl
open BStarGeneratedOwner BStarGeneratedPCAncestry BStarCommitGeneratedTail
open BStarAcquireVisitOrder BStarResetControllerEntry

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

def pc (x : X) (i : Fin n) := (ctrlOp.read (x i).long).toNat

/-- Every cut, including the last, stays in the same successful attempt's
three pre-COMMIT source opcodes. Header here is literal, not a PC class. -/
def PreBand (x : X) (i : Fin n) (w : List (Fin n)) : Prop :=
  ∀ a b,w=a++b →
    let y := run x a
    oldH6 B y i=true ∧ 408≤pc y i ∧ pc y i≤410

private theorem bad_issue_pc {x : X} {addr : Nat → Pos n} {e : Fin n}
    (h : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e) (I : BStarClearanceSource.Issue (x (addr 0).1).long)
    (E : e=RearTrace.predecessor (addr 0).1)
    (bad : initial (pc x (addr 0).1) (x (addr 0).1).long=none) :
    pc (step x e) (addr 0).1=0 := by
  have R : rightNeighbor e=(addr 0).1 := E ▸ RearTrace.right_predecessor _
  let pair := (x e,x (rightNeighbor e))
  have hdr : (oldHeaders B pair.2).h6=true := by change oldH6 B x (rightNeighbor e)=true; rwa [R]
  have valid : LongDoorGuard.valid manifest pair.2.long=true := by
    change LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true
    rw [R]; exact I.1
  have phase : (ctrlPhase.read pair.2.long).toNat=1 := by
    change (ctrlPhase.read (x (rightNeighbor e)).long).toNat=1
    rw [R]; exact I.2
  have A := exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair hdr valid phase
  have bad' : initial (ctrlOp.read pair.2.long).toNat pair.2.long=none := by
    change initial (pc x (rightNeighbor e)) (x (rightNeighbor e)).long=none
    rwa [R]
  rw [bad'] at A
  have eq : step x e (addr 0).1=(largePair B pair).2 := by
    rw [←R]; simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
  exact congrArg (fun t : _ × BitVec 9 => t.2.toNat) (eq ▸ A)

private theorem consume_not_408 {x base : X} {addr : Nat → Pos n}
    {e : Fin n} {len op : Nat} (K : (addr 0).2=0) (h : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e) (lo : 408≤pc x (addr 0).1)
    (I : Current hp base addr len x (.busy op (.back 0)))
    (E : Event hp addr len x e (.busy op (.back 0)) .idle) :
    pc (step x e) (addr 0).1≠408 := by
  intro bad
  obtain ⟨A,_,_⟩ := consume_to_stage hp K h sep I E bad
  have P : pc x (addr 0).1=op := I.1.2.2.2
  omega

/-- Extract the accepted Pre-Choice tape directly from a same-word
generated trace and its cutwise PC band; no classification of the word
or descriptor equality is supplied by the caller. -/
theorem scan_before_choice {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (band : PreBand hp x (addr 0).1 w) :
    BeforeChoice hp base addr len x w := by
  induction T with
  | endpoint I => exact .nil _
  | @next x a e w b dest I E T ih =>
    have h := band [] (e::w) rfl
    have j := band [e] w rfl
    change oldH6 B x (addr 0).1=true ∧ 408≤pc x (addr 0).1 ∧ pc x (addr 0).1≤410 at h
    change oldH6 B (step x e) (addr 0).1=true ∧ 408≤pc (step x e) (addr 0).1 ∧ pc (step x e) (addr 0).1≤410 at j
    have rest : PreBand hp (step x e) (addr 0).1 w := by
      intro u v Q
      exact band (e::u) v (congrArg (List.cons e) Q)
    have t := ih rest
    have notClear : pc x (addr 0).1≠1 := by have := h.2.1; omega
    have foreign (z : e≠RearTrace.predecessor (addr 0).1) :
        rightNeighbor e≠(addr 0).1 := by
      intro Q
      exact z ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor Q))
    cases E with
    | idle_hold away =>
      exact .flight h.1 (sep e) I (.idle_hold away) notClear
        (fun C => foreign away C.2.2) (by intro; exact .inl (by intro A; cases A)) t
    | bad_issue own bad =>
      have Z := bad_issue_pc hp h.1 (sep e) I.1 own bad
      have J : 408≤pc (step x e) (addr 0).1 := j.2.1
      omega
    | launch own L =>
      exact .flight h.1 (sep e) I (.launch own L) notClear
        (fun C => by cases C.2.1) (by intro; exact .inl (by intro A; cases A)) t
    | transit op z d live S =>
      exact .flight h.1 (sep e) I (.transit op z d live S) notClear
        (fun C => by cases C.1) (by intro; exact .inr (by intro A; cases A)) t
    | arrived_hold op away =>
      exact .flight h.1 (sep e) I (.arrived_hold op away) notClear
        (fun C => by cases C.1) (by intro; exact .inr (by intro A; cases A)) t
    | consume op own clean =>
      have ev : Event hp addr len x e (.busy op (.back 0)) .idle := .consume op own clean
      have not409 : pc (step x e) (addr 0).1≠408 := consume_not_408 hp K h.1 (sep e) h.2.1 I ev
      have J : 408≤pc (step x e) (addr 0).1 ∧ pc (step x e) (addr 0).1≤410 := j.2
      exact .consume h.1 (sep e) I ev (show pc (step x e) (addr 0).1=409 ∨ pc (step x e) (addr 0).1=410 by omega) t

private theorem foreign_pc (x : X) (i e : Fin n)
    (h : oldH6 B x i=true) (ne : rightNeighbor e≠i) :
    pc (step x e) i=pc x i := by
  by_cases E : i=e
  · subst i
    let pair := (x e,x (rightNeighbor e))
    have h' : (oldHeaders B pair.1).h6=true := h
    have t := BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair h'
    unfold pc
    simp only [AllSizeS1Geometry.step,if_true]
    have Q := congrArg (fun y : BitVec 2 × BitVec 9 => y.2.toNat) t
    exact Q
  · unfold pc
    simp only [AllSizeS1Geometry.step,if_neg E,if_neg (Ne.symm ne)]

private theorem entry_411 {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {a b : Mode} (h : oldH6 B x (addr 0).1=true) (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x a)
    (J : Current hp base addr len (step x e) b)
    (E : Event hp addr len x e a b)
    (old : pc x (addr 0).1<411) (new : pc (step x e) (addr 0).1=411) :
    ∃ op, a=.busy op (.back 0) ∧ b=.idle ∧
      Current hp base addr len x (.busy op (.back 0)) ∧
      Event hp addr len x e (.busy op (.back 0)) .idle := by
  have away (A : e≠RearTrace.predecessor (addr 0).1) : False := by
    have F : rightNeighbor e≠(addr 0).1 := by
      intro R
      exact A ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor R))
    have Q := foreign_pc hp x (addr 0).1 e h F
    omega
  cases E with
  | idle_hold ne => exact (away ne).elim
  | bad_issue own bad =>
    have Z := bad_issue_pc hp h sep I.1 own bad
    omega
  | launch _ L =>
    have Q : pc (step x e) (addr 0).1=pc x (addr 0).1 :=
      congrArg (fun t : _ × BitVec 9 => t.2.toNat) L.2.choose_spec.2
    omega
  | transit op z d live S =>
    have Q : pc (step x e) (addr 0).1=pc x (addr 0).1 :=
      J.1.2.2.2.trans I.1.2.2.2.symm
    omega
  | arrived_hold _ ne => exact (away ne).elim
  | consume op own clear => exact ⟨op,rfl,rfl,I,.consume op own clear⟩

private theorem changed_nonzero {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {a b : Mode} (h : oldH6 B x (addr 0).1=true) (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x a)
    (J : Current hp base addr len (step x e) b)
    (E : Event hp addr len x e a b)
    (changed : pc (step x e) (addr 0).1≠pc x (addr 0).1)
    (new : pc (step x e) (addr 0).1≠0) :
    ∃ op, a=.busy op (.back 0) ∧ b=.idle ∧
      Current hp base addr len x (.busy op (.back 0)) ∧
      Event hp addr len x e (.busy op (.back 0)) .idle := by
  have away (A : e≠RearTrace.predecessor (addr 0).1) : False := by
    have F : rightNeighbor e≠(addr 0).1 := by
      intro R
      exact A ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor R))
    have Q := foreign_pc hp x (addr 0).1 e h F
    exact changed Q
  cases E with
  | idle_hold ne => exact (away ne).elim
  | bad_issue own bad =>
    have Z := bad_issue_pc hp h sep I.1 own bad
    exact (new Z).elim
  | launch _ L =>
    have Q : pc (step x e) (addr 0).1=pc x (addr 0).1 :=
      congrArg (fun t : _ × BitVec 9 => t.2.toNat) L.2.choose_spec.2
    exact (changed Q).elim
  | transit op z d live S =>
    have Q : pc (step x e) (addr 0).1=pc x (addr 0).1 :=
      J.1.2.2.2.trans I.1.2.2.2.symm
    exact (changed Q).elim
  | arrived_hold _ ne => exact (away ne).elim
  | consume op own clear => exact ⟨op,rfl,rfl,I,.consume op own clear⟩

/-- The whole live tail stays at H6 in opcodes 408 through 411. It
excludes re-entry after a reset; it does not assert when a tour succeeds. -/
def TailBand (x : X) (i : Fin n) (w : List (Fin n)) : Prop :=
  ∀ a b,w=a++b →
    let y := run x a
    oldH6 B y i=true ∧ 408≤pc y i ∧ pc y i≤411

private theorem current_head {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)} (T : GeneratedOwner hp base addr len x a w b) :
    Current hp base addr len x a := by cases T <;> assumption

/-- Find the first generated bank-selecting consume on the same
physical word. The returned prefix is certified BeforeChoice,
not an externally chosen descriptor-preserving split. -/
theorem first_411 {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (band : TailBand hp x (addr 0).1 w)
    (old : pc x (addr 0).1<411) (last : pc (run x w) (addr 0).1=411) :
    ∃ pre e post op, w=pre++e::post ∧ BeforeChoice hp base addr len x pre ∧ PreBand hp x (addr 0).1 pre ∧
      Current hp base addr len (run x pre) (.busy op (.back 0)) ∧
      Event hp addr len (run x pre) e (.busy op (.back 0)) .idle ∧
      pc (step (run x pre) e) (addr 0).1=411 ∧
      GeneratedOwner hp base addr len (step (run x pre) e) .idle post b := by
  induction T with
  | endpoint I =>
    simp only [BStarResetSchedule.run] at last
    omega
  | @next x a e w b dest I E T ih =>
    have h := band [] (e::w) rfl
    change oldH6 B x (addr 0).1=true ∧ 408≤pc x (addr 0).1 ∧ _ at h
    have j := band [e] w rfl
    change oldH6 B (step x e) (addr 0).1=true ∧ 408≤pc (step x e) (addr 0).1 ∧
      pc (step x e) (addr 0).1≤411 at j
    by_cases A : pc (step x e) (addr 0).1=411
    · obtain ⟨op,_,rfl,L,Q⟩ := entry_411 hp h.1 (sep e) I (current_head hp T) E old A
      have PB : PreBand hp x (addr 0).1 [] := by
        intro u v eq
        obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp eq.symm
        change oldH6 B x (addr 0).1=true ∧ 408≤pc x (addr 0).1 ∧ pc x (addr 0).1≤410
        exact ⟨h.1,h.2.1,by omega⟩
      exact ⟨[],e,w,op,rfl,.nil _,PB,L,Q,A,T⟩
    have ab : pc (step x e) (addr 0).1<411 := by have := j.2.2; omega
    have band' : TailBand hp (step x e) (addr 0).1 w := by
      intro u v eq
      exact band (e::u) v (congrArg (List.cons e) eq)
    obtain ⟨pre,m,post,op,W,P,PB,L,Q,U,V⟩ := ih band' ab last
    have endpoints : PreBand hp x (addr 0).1 [e] := by
      intro u v eq
      cases u with
      | nil =>
        change oldH6 B x (addr 0).1=true ∧ 408≤pc x (addr 0).1 ∧ pc x (addr 0).1≤410
        exact ⟨h.1,h.2.1,by omega⟩
      | cons hd tail =>
        obtain ⟨rfl,S⟩ := List.cons.inj eq
        obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp S.symm
        change oldH6 B (step x e) (addr 0).1=true ∧ 408≤pc (step x e) (addr 0).1 ∧
          pc (step x e) (addr 0).1≤410
        exact ⟨j.1,j.2.1,by omega⟩
    have one := scan_before_choice hp K sep (.next I E (.endpoint (current_head hp T))) endpoints
    have together : BeforeChoice hp base addr len x (e::pre) := by
      cases one with
      | flight h sep I E N A NC _ => exact .flight h sep I E N A NC P
      | consume h sep I E A _ => exact .consume h sep I E A P
    have initial : PreBand hp x (addr 0).1 (e::pre) := by
      intro u v E'
      cases u with
      | nil => exact endpoints [] [e] rfl
      | cons f q =>
        obtain ⟨rfl,R⟩ := List.cons.inj E'
        exact PB q v R
    exact ⟨e::pre,m,post,op,congrArg (List.cons e) W,together,initial,L,Q,U,V⟩

/-- Literal backward reflection. A mark entering the 408..411 band
from outside is the successful generated 407 receipt. Other marks
in the suffix have old PC in the band, without assuming reboot did
not occur earlier in the tape. -/
theorem reflect_tail {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {a b : Mode} (K : (addr 0).2=0)
    (h : oldH6 B x (addr 0).1=true) (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x a)
    (J : Current hp base addr len (step x e) b)
    (E : Event hp addr len x e a b)
    (new : 408≤pc (step x e) (addr 0).1 ∧ pc (step x e) (addr 0).1≤411) :
    (408≤pc x (addr 0).1 ∧ pc x (addr 0).1≤411) ∨
      (pc x (addr 0).1=407 ∧ pc (step x e) (addr 0).1=408 ∧
        Current hp base addr len x (.busy 407 (.back 0)) ∧
        Event hp addr len x e (.busy 407 (.back 0)) .idle) := by
  by_cases old : 408≤pc x (addr 0).1 ∧ pc x (addr 0).1≤411
  · exact .inl old
  have ch : pc (step x e) (addr 0).1≠pc x (addr 0).1 := by omega
  obtain ⟨op,_,_,IC,EC⟩ := changed_nonzero hp h sep I J E ch (by omega)
  by_cases P : pc (step x e) (addr 0).1=408
  · obtain ⟨O,_,_⟩ := consume_to_stage hp K h sep IC EC P
    have N : pc x (addr 0).1=op := IC.1.2.2.2
    exact .inr ⟨N.trans O,P,O ▸ IC,O ▸ EC⟩
  · have NN : pc (step x e) (addr 0).1=409 ∨ pc (step x e) (addr 0).1=410 ∨
        pc (step x e) (addr 0).1=411 := by omega
    have A := consume_tail hp K h sep IC EC NN
    obtain ⟨_,_,_,_,_,_,M,N,R⟩ := A
    have U : pc x (addr 0).1=op := IC.1.2.2.2
    rcases NN with a|b|c
    · have L := M a
      omega
    · have L := N b
      omega
    · rcases R c with l|l <;> omega

/-- Backward scan from the observed ready COMMIT. The 408 cut is
derived from the actual tape; an earlier reset is not ruled out. -/
theorem last_stage_entry {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (hdr : ∀ u v,w=u++v → oldH6 B (run x u) (addr 0).1=true)
    (last : pc (run x w) (addr 0).1=411) :
    TailBand hp x (addr 0).1 w ∨
      ∃ pre e post, w=pre++e::post ∧
        Current hp base addr len (run x pre) (.busy 407 (.back 0)) ∧
        Event hp addr len (run x pre) e (.busy 407 (.back 0)) .idle ∧
        pc (step (run x pre) e) (addr 0).1=408 ∧
        GeneratedOwner hp base addr len (step (run x pre) e) .idle post b ∧
        TailBand hp (step (run x pre) e) (addr 0).1 post := by
  induction T with
  | endpoint I =>
    left
    intro u v eq
    obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp eq.symm
    exact ⟨hdr [] [] rfl,by omega,by omega⟩
  | @next x a e w b dest I E T ih =>
    have subHdr : ∀ u v,w=u++v → oldH6 B (run (step x e) u) (addr 0).1=true := by
      intro u v Q
      exact hdr (e::u) v (congrArg (List.cons e) Q)
    rcases ih subHdr last with rest|⟨pre,m,post,W,L,Q,U,V,G⟩
    · have hh : oldH6 B x (addr 0).1=true := hdr [] (e::w) rfl
      have J : 408≤pc (step x e) (addr 0).1 ∧ pc (step x e) (addr 0).1≤411 := (rest [] w rfl).2
      rcases reflect_tail hp K hh (sep e) I (current_head hp T) E J with P|⟨old,C,L,Q⟩
      · left
        intro u v W
        cases u with
        | nil => exact ⟨hh,P⟩
        | cons f tail =>
          obtain ⟨rfl,U⟩ := List.cons.inj W
          exact rest tail v U
      · have A : b=.idle := by
          obtain ⟨_,_,eq,_,_⟩ := changed_nonzero hp hh (sep e) I (current_head hp T) E
            (show pc (step x e) (addr 0).1≠pc x (addr 0).1 by omega) (by omega)
          exact eq
        subst b
        exact .inr ⟨[],e,w,rfl,L,Q,C,T,rest⟩
    · exact .inr ⟨e::pre,m,post,congrArg (List.cons e) W,L,Q,U,V,G⟩

private theorem no_consume_411 {base x : X} {addr : Nat → Pos n} {len : Nat}
    {e : Fin n} (K : (addr 0).2=0) (h : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x (.busy 411 (.back 0)))
    (E : Event hp addr len x e (.busy 411 (.back 0)) .idle)
    (next : 408≤pc (step x e) (addr 0).1 ∧ pc (step x e) (addr 0).1≤411) : False := by
  have O : pc x (addr 0).1=411 := I.1.2.2.2
  have N := consume_not_408 hp K h sep (show 408≤pc x (addr 0).1 by omega) I E
  have A : pc (step x e) (addr 0).1=409 ∨ pc (step x e) (addr 0).1=410 ∨
      pc (step x e) (addr 0).1=411 := by omega
  obtain ⟨_,_,_,_,_,_,J,K',L⟩ := consume_tail hp K h sep I E A
  rcases A with a|b|c
  · have := J a; omega
  · have := K' b; omega
  · rcases L c with a|b <;> omega

private theorem busy_411_cannot_idle {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (band : TailBand hp x (addr 0).1 w)
    (busy : ∃ z,a=.busy 411 z) (last : b=.idle) : False := by
  induction T with
  | endpoint I =>
    obtain ⟨z,E⟩ := busy
    cases last.symm.trans E
  | @next x a e w b dest I E T ih =>
    obtain ⟨z,rfl⟩ := busy
    have sub : TailBand hp (step x e) (addr 0).1 w := by
      intro u v Q
      exact band (e::u) v (congrArg (List.cons e) Q)
    cases E with
    | transit _ z d live S => exact ih sub ⟨d,rfl⟩ last
    | arrived_hold _ away => exact ih sub ⟨.back 0,rfl⟩ last
    | consume _ own clear =>
      exact no_consume_411 hp K (band [] (e::w) rfl).1 (sep e) I
        (.consume 411 own clear) (sub [] w rfl).2

/-- Between the first schedule of 411 and the nominated idle COMMIT
issue, every earlier mark is foreign. An intervening actual own launch
would leave a busy 411 that cannot return to idle in this live band. -/
theorem ready_411_foreign {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (band : TailBand hp x (addr 0).1 w)
    (start : a=.idle) (last : b=.idle) (P : pc x (addr 0).1=411) :
    ∀ e∈w, rightNeighbor e≠(addr 0).1 := by
  induction T with
  | endpoint I => simp
  | @next x a e w b dest I E T ih =>
    subst a
    have hh : oldH6 B x (addr 0).1=true := (band [] (e::w) rfl).1
    have sub : TailBand hp (step x e) (addr 0).1 w := by
      intro u v Q
      exact band (e::u) v (congrArg (List.cons e) Q)
    cases E with
    | idle_hold away =>
      have N : rightNeighbor e≠(addr 0).1 := by
        intro R
        exact away ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor R))
      have pc' := (foreign_pc hp x (addr 0).1 e hh N).trans P
      intro f mf
      rcases List.mem_cons.mp mf with rfl|mf
      · exact N
      · exact ih sub rfl last pc' f mf
    | bad_issue own err =>
      have Z := bad_issue_pc hp hh (sep e) I.1 own err
      have L : 408≤pc (step x e) (addr 0).1 := (sub [] w rfl).2.1
      omega
    | launch own L =>
      exact (busy_411_cannot_idle hp K sep T sub
        ⟨.out 0,congrArg (fun o => Mode.busy o (.out 0)) P⟩ last).elim

#print axioms ready_411_foreign
#print axioms last_stage_entry
#print axioms reflect_tail
#print axioms first_411
#print axioms scan_before_choice
end L4.BStarCommitTailScan
