import Leader.Wu.Authorization.ProvenanceMarks

/-!
# No CLEAN command on an occupied CLEAN output

This is a stage-local property of the original AuthF definitions. A same-mark
`-1` command deletes the main path; a different-mark command is cleared. Thus
an occupied output of `cleanApplyAuth` has no command in either CLEAN slot.
No domain condition on the raw Int/Nat payloads is required. In particular,
this result does not assert that remaining records have bounded normal values.

The pair corollary concerns `cleanSourceAuth`, not the full pipeline. A
population interaction cannot be stopped at this internal cut; later path
movement and the final frame need separate arguments before using this fact
in a full-row or SerialPlus conclusion.

Source-level nonvacuity: at psi = 2 choose main paths `some 0 0` and
`some 1 0`, common path mark, empty CLEAN records, and otherwise neutral raw
fields. The generated adjacent connection records agree, both main paths
survive CLEAN, and the two no-command conclusions apply.
-/

namespace PPLLAuthCheckCleanNoCmd

open PPLL PPLLAuthF

set_option autoImplicit false

variable {ψ : Nat}

/-- Neither CLEAN slot contains the distinguished `-1` command. Other raw
integer labels are allowed; this predicate does not assert domain validity. -/
def NoCmd (u : AuthState ψ) : Prop :=
  isCmd u.core.path4 = false ∧ isCmd u.core.path5 = false

/-- First slot of the existing command application, factored before the
second slot so each proof splits only one record's guards. -/
private def apply4 (pl : Nat) (u : AuthState ψ) : AuthState ψ :=
  match u.core.path4 with
  | some (lbl,_) =>
    if lbl = (-1 : Int) then
      if u.path4_mark == u.path_mark then
        let c := if pl = 0 then {u.core with path4 := none} else u.core
        {u with core := {c with path := .bot}}
      else {u with core := {u.core with path4 := none}}
    else u
  | none => u

/-- Second slot of the same command application. -/
private def apply5 (pl : Nat) (u : AuthState ψ) : AuthState ψ :=
  match u.core.path5 with
  | some (lbl,_) =>
    if lbl = (-1 : Int) then
      if u.path5_mark == u.path_mark then
        let c := if pl = ψ - 1 then {u.core with path5 := none} else u.core
        {u with core := {c with path := .bot}}
      else {u with core := {u.core with path5 := none}}
    else u
  | none => u

/-- Factor before inspecting the main path. The two branches are
 definitionally the original nested command application. -/
private theorem cleanApply_eq (u : AuthState ψ) :
    cleanApplyAuth u =
      match u.core.path with
      | .bot => u
      | .some pl _ => apply5 pl (apply4 pl u) := by
  rfl

/-- An occupied output of the first slot has no command in that slot. -/
private theorem apply4_retained (pl : Nat) (u : AuthState ψ) :
    (apply4 pl u).core.path ≠ .bot → isCmd (apply4 pl u).core.path4 = false := by
  cases ht : u.core.path4 with
  | none => simp [apply4,ht,isCmd]
  | some t =>
    rcases t with ⟨lbl,bit⟩
    by_cases hc : lbl = (-1 : Int)
    · by_cases hm : (u.path4_mark == u.path_mark) = true
      · by_cases hz : pl = 0 <;> simp [apply4,ht,hc,hm,hz]
      · simp [apply4,ht,hc,hm,isCmd]
    · simp [apply4,ht,hc,isCmd]

/-- The second slot preserves path4. If its output is occupied, its input
was occupied and its own command is absent. -/
private theorem apply5_retained (pl : Nat) (u : AuthState ψ) :
    (apply5 pl u).core.path4 = u.core.path4 ∧
      ((apply5 pl u).core.path ≠ .bot →
        u.core.path ≠ .bot ∧ isCmd (apply5 pl u).core.path5 = false) := by
  cases ht : u.core.path5 with
  | none => simp [apply5,ht,isCmd]
  | some t =>
    rcases t with ⟨lbl,bit⟩
    by_cases hc : lbl = (-1 : Int)
    · by_cases hm : (u.path5_mark == u.path_mark) = true
      · by_cases hz : pl = ψ - 1 <;> simp [apply5,ht,hc,hm,hz]
      · simp [apply5,ht,hc,hm,isCmd]
    · simp [apply5,ht,hc,isCmd]

/-- Any occupied output of command application has no remaining command.
This permits arbitrary input paths, records, record marks and ancillary fields. -/
theorem cleanApply_retained_noCmd (u : AuthState ψ)
    (h : (cleanApplyAuth u).core.path ≠ .bot) :
    NoCmd (cleanApplyAuth u) := by
  cases hp : u.core.path with
  | bot => simp [cleanApplyAuth,hp] at h
  | some pl bit =>
    have he : cleanApplyAuth u = apply5 pl (apply4 pl u) := by
      rw [cleanApply_eq,hp]
    rw [he] at h ⊢
    have h4 := apply4_retained pl u
    generalize apply4 pl u = a at h4 h ⊢
    have h5 := apply5_retained pl a
    generalize apply5 pl a = b at h5 h ⊢
    obtain ⟨hpath4,hrest⟩ := h5
    obtain ⟨hprior,hcmd5⟩ := hrest h
    refine ⟨?_,hcmd5⟩
    rw [hpath4]
    exact h4 hprior

/-- The existing CLEAN stages before the final command application, named
only to keep the pair proof from expanding nested transition expressions. -/
private def cleanPrelude (hp : ψ > 0) (c : Cfg) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let l := genConnectAuth l
  let r := genConnectAuth r
  let (l,r) := step3Auth c.cleanNbr c.markClean l r
  let (l,r) := step4Auth c.cleanNbr c.markClean l r
  let (l,r) := if isCmd l.core.path4 then
      (l, {r with core := {r.core with path4 := none}})
    else step5Auth hp l r
  if isCmd r.core.path5 then
    ({l with core := {l.core with path5 := none}}, r)
  else step6Auth hp l r

/-- Definitional factoring of the original CLEAN, with no transition change. -/
private theorem cleanSource_eq (hp : ψ > 0) (c : Cfg) (l r : AuthState ψ) :
    cleanSourceAuth hp c l r =
      (cleanApplyAuth (cleanPrelude hp c l r).1,
       cleanApplyAuth (cleanPrelude hp c l r).2) := by rfl

/-- On each endpoint independently, retaining a main path after the full
CLEAN stage excludes commands. No assumptions on the other endpoint are needed. -/
theorem cleanSource_retained_noCmd (hp : ψ > 0) (c : Cfg) (l r : AuthState ψ) :
    let q := cleanSourceAuth hp c l r
    (q.1.core.path ≠ .bot → NoCmd q.1) ∧
      (q.2.core.path ≠ .bot → NoCmd q.2) := by
  rw [cleanSource_eq]
  generalize cleanPrelude hp c l r = q
  rcases q with ⟨a,b⟩
  exact ⟨cleanApply_retained_noCmd a,cleanApply_retained_noCmd b⟩

/-- Pair form for a continuing CLEAN cut with both main paths present. This
is still an internal-stage theorem, not a complete population interaction. -/
theorem cleanSource_both_retained_noCmd (hp : ψ > 0) (c : Cfg) (l r : AuthState ψ)
    (hl : (cleanSourceAuth hp c l r).1.core.path ≠ .bot)
    (hr : (cleanSourceAuth hp c l r).2.core.path ≠ .bot) :
    NoCmd (cleanSourceAuth hp c l r).1 ∧ NoCmd (cleanSourceAuth hp c l r).2 := by
  have h := cleanSource_retained_noCmd hp c l r
  exact ⟨h.1 hl,h.2 hr⟩

#print axioms cleanApply_retained_noCmd
#print axioms cleanSource_retained_noCmd
#print axioms cleanSource_both_retained_noCmd

end PPLLAuthCheckCleanNoCmd
