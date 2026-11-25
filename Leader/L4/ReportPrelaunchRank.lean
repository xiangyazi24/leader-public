import Leader.L4.ReportChartPartition

namespace L4.ReportPrelaunchRank

/-- Weights depend only on old decoded tags and genuine ADMIT gate race,
not on unused packet or source padding. -/
inductive Label where
  | e | trail | reply | front (race : Nat) (fault : Bool)

def raceDebt (race : Nat) : Nat := if race=1 then 2 else if race=2 ∨ race=3 then 1 else 0

def extra (g j race : Nat) (fault : Bool) : Nat :=
  if j<g then 2 else if j=g ∧ !fault then raceDebt race else 0

def rank (L g j : Nat) : Label → Nat
  | .e => 0
  | .trail => 1
  | .reply => j+1
  | .front race fault => 3*L-2*j+extra g j race fault

theorem debt_cap (r : Nat) : raceDebt r≤2 := by
  unfold raceDebt
  split
  · omega
  · split <;> omega

theorem extra_cap (g j r : Nat) (f : Bool) : extra g j r f≤2 := by
  unfold extra
  split
  · omega
  · split
    · exact debt_cap _
    · omega

theorem slot_cap {L g j : Nat} (J : j<L) (t : Label) :
    rank L g j t≤3*L+2 := by
  cases t with
  | e => simp [rank]
  | trail => simp [rank]
  | reply => simp [rank]; omega
  | front r f => have := extra_cap g j r f; simp [rank]; omega

/-- Travel steps cannot increase the gate debt. This includes an
arbitrary valid or fault-normalized arriving F at the unique gate. -/
theorem extra_forward (g j r s : Nat) (f b : Bool) :
    extra g (j+1) s b≤extra g j r f := by
  by_cases H : j<g
  · simpa only [extra,if_pos H] using extra_cap g (j+1) s b
  · have A : ¬j+1<g := by omega
    have B : j+1≠g := by omega
    simp [extra,A,B]

/-- A nonterminal F hop overwrites any old destination occurrence.
The old source slot becomes T. No vacancy assumption is used. -/
theorem forward_strict {L g j : Nat} (J : j+1<L)
    (old : Label) (r s : Nat) (f b : Bool) :
    rank L g j .trail + rank L g (j+1) (.front s b) <
      rank L g j (.front r f) + rank L g (j+1) old := by
  have := extra_forward g j r s f b
  simp only [rank]
  omega

/-- The final F turns into D on its own physical site. -/
theorem terminal_strict {L g j : Nat} (J : j<L)
    (r : Nat) (f : Bool) :
    rank L g j .reply < rank L g j (.front r f) := by
  simp only [rank]
  omega

/-- The only progressing live gate updates in the literal race. -/
def RaceAdvance (r s : Nat) : Prop :=
  (r=1 ∧ (s=2 ∨ s=3)) ∨ (r=2 ∧ s=4) ∨ (r=3 ∧ s=5)

theorem gate_race_strict (L g r s : Nat) (R : RaceAdvance r s) :
    rank L g g (.front s false) < rank L g g (.front r false) := by
  rcases R with ⟨rfl,rfl|rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    simp [rank,extra,raceDebt]

/-- Backward transfer can overwrite any lower slot and clears the
upper slot; the literal row allows this only for a non-F predecessor. -/
theorem reverse_strict (L g j : Nat) (old : Label) :
    rank L g j .reply + rank L g (j+1) .e <
      rank L g j old + rank L g (j+1) .reply := by
  simp only [rank]
  omega

theorem trail_clear_strict (L g j : Nat) :
    rank L g j .e < rank L g j .trail := by simp [rank]

theorem fault_nonincrease (L g j r s : Nat) (f : Bool) :
    rank L g j (.front s true)≤rank L g j (.front r f) := by
  by_cases A : j<g
  · simp [rank,extra,A]
  · simp [rank,extra,A]

/-- Composing with an unmodified prefix/suffix simply adds the same
nonnegative contribution to both sides. -/
theorem strict_with_frame {a b c d u v : Nat} (H : a+b<c+d) :
    u+a+b+v<u+c+d+v := by omega

/-- A literal non-target source event can rewrite the root rail;
decreasing source debt by one pays every possible rewrite. -/
theorem source_event_strict {L g debt debt' : Nat} (L0 : 0<L)
    (H : debt'<debt) (before after : Label) :
    (3*L+3)*debt' + rank L g 0 after <
      (3*L+3)*debt + rank L g 0 before := by
  have B := slot_cap (g:=g) L0 after
  have C := Nat.mul_le_mul_left (3*L+3) (show debt'+1≤debt by omega)
  rw [Nat.mul_add,Nat.mul_one] at C
  omega

/-- Total initial slot-rank bound, for the actual L chart positions. -/
theorem chart_rank_cap {L g : Nat} (get : Fin L→Label) :
    (List.ofFn (fun i=>rank L g i.val (get i))).sum≤L*(3*L+2) := by
  have bound (m : Nat) (f : Fin m→Nat) (B : ∀ i,f i≤3*L+2) :
      (List.ofFn f).sum≤m*(3*L+2) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.ofFn_succ,List.sum_cons,Nat.succ_mul]
      exact Nat.le_trans (Nat.add_le_add (B 0) (ih (fun i=>f i.succ) (fun i=>B i.succ))) (by omega)
  exact bound L _ (fun i => slot_cap i.isLt (get i))

/-- If the concrete controller supplies a source-action debt ≤2P+2,
then inclusion of every decoded chart slot fits the polynomial clock.
The source itinerary bound and exact row refinement are separate. -/
theorem initial_budget {L P g debt : Nat} (H : debt≤2*P+2)
    (get : Fin L→Label) :
    (List.ofFn (fun i=>rank L g i.val (get i))).sum+(3*L+3)*debt
      ≤10*(L+P+2)^2 := by
  let x := L+P+2
  have A : L*(3*L+2)≤x*(3*x) := Nat.mul_le_mul (by dsimp [x]; omega) (by dsimp [x]; omega)
  have B : (3*L+3)*debt≤(3*x)*(2*x) :=
    Nat.mul_le_mul (by dsimp [x]; omega) (by dsimp [x]; omega)
  have S := Nat.add_le_add (Nat.le_trans (chart_rank_cap (g:=g) get) A) B
  have A' : x*(3*x)=3*x^2 := by rw [Nat.pow_two]; ac_rfl
  have B' : (3*x)*(2*x)=6*x^2 := by
    rw [Nat.pow_two]
    calc
      _ = (3*2)*(x*x) := by ac_rfl
      _ = _ := rfl
  rw [A',B'] at S
  change _ ≤ 10*x^2
  omega

end L4.ReportPrelaunchRank

namespace L4.ReportPrelaunchRank

/-- The controller visits READ and WRITE alternately, although its
encoding places all READ codes before all WRITE codes. -/
def logical (t op : Nat) : Nat :=
  if op<2*t+3 then op
  else if op<3*t+3 then 2*t+3+2*(op-(2*t+3))
  else if op<4*t+3 then 2*t+4+2*(op-(3*t+3))
  else op

def pcDebt (t phase op : Nat) : Nat :=
  let P := 4*t+5
  if phase=1 ∧ op=0 then 0
  else if (phase=1 ∨ phase=2) ∧ op<P then
    2*(P-logical t op) - (if phase=2 then 1 else 0)
  else 2*P+2

theorem logical_le {t a : Nat} (A : a<4*t+5) : logical t a<4*t+5 := by
  unfold logical
  split
  · omega
  · split
    · omega
    · split <;> omega

theorem logical_linear {t a : Nat} (A : a+1<2*t+3) :
    logical t (a+1)=logical t a+1 := by
  simp [logical,A,show a<2*t+3 by omega]

theorem logical_cmp_to_read {t : Nat} (T : 0<t) :
    logical t (2*t+3)=logical t (2*t+2)+1 := by
  simp [logical,show 2*t+3<3*t+3 by omega,show 2*t+2<2*t+3 by omega]

theorem logical_read_write {t j : Nat} (J : j<t) :
    logical t (3*t+3+j)=logical t (2*t+3+j)+1 := by
  simp [logical,show ¬3*t+3+j<2*t+3 by omega,show ¬3*t+3+j<3*t+3 by omega,
    show 3*t+3+j<4*t+3 by omega,show ¬2*t+3+j<2*t+3 by omega,
    show 2*t+3+j<3*t+3 by omega,
    show 3*t+3+j-(3*t+3)=j by omega,show 2*t+3+j-(2*t+3)=j by omega]
  omega

theorem logical_write_read {t j : Nat} (J : j+1<t) :
    logical t (2*t+3+(j+1))=logical t (3*t+3+j)+1 := by
  simp [logical,show ¬3*t+3+j<2*t+3 by omega,show ¬3*t+3+j<3*t+3 by omega,
    show 3*t+3+j<4*t+3 by omega,show ¬2*t+3+(j+1)<2*t+3 by omega,
    show 2*t+3+(j+1)<3*t+3 by omega,
    show 3*t+3+j-(3*t+3)=j by omega,show 2*t+3+(j+1)-(2*t+3)=j+1 by omega]
  omega

theorem logical_write_seal {t j : Nat} (J : j+1=t) :
    logical t (4*t+3)=logical t (3*t+3+j)+1 := by
  simp [logical,show ¬4*t+3<2*t+3 by omega,show ¬4*t+3<3*t+3 by omega,
    show ¬3*t+3+j<2*t+3 by omega,show ¬3*t+3+j<3*t+3 by omega,
    show 3*t+3+j<4*t+3 by omega,show 3*t+3+j-(3*t+3)=j by omega]
  omega

theorem logical_seal_commit (t : Nat) :
    logical t (4*t+4)=logical t (4*t+3)+1 := by
  simp [logical,show ¬4*t+3<2*t+3 by omega,show ¬4*t+3<3*t+3 by omega,
    show ¬4*t+4<2*t+3 by omega,show ¬4*t+4<3*t+3 by omega,show ¬4*t+4<4*t+3 by omega]

theorem pc_debt_cap (t phase op : Nat) : pcDebt t phase op≤2*(4*t+5)+2 := by
  simp only [pcDebt]
  split
  · omega
  · split <;> omega

theorem pc_debt_issue {t op : Nat} (O : 0<op) (V : op<4*t+5) :
    pcDebt t 2 op<pcDebt t 1 op := by
  have A := logical_le V
  simp [pcDebt,show op≠0 by omega,V]
  omega

theorem pc_debt_consume {t op next : Nat} (V : op<4*t+5) (W : next<4*t+5)
    (G : logical t next=logical t op+1) :
    pcDebt t 1 next<pcDebt t 2 op := by
  have A := logical_le V
  simp [pcDebt,V,W]
  split <;> omega

theorem pc_debt_restart {t phase op : Nat} (NotLaunch : ¬(phase=1 ∧ op=0)) :
    pcDebt t 1 0<pcDebt t phase op := by
  have Z : pcDebt t 1 0=0 := by simp [pcDebt]
  rw [Z]
  simp only [pcDebt,if_neg NotLaunch]
  by_cases H : (phase=1 ∨ phase=2) ∧ op<4*t+5
  · rw [if_pos H]
    have A := logical_le H.2
    split <;> omega
  · rw [if_neg H]
    omega

end L4.ReportPrelaunchRank

namespace L4.ReportPrelaunchRank

def total {m : Nat} (f : Fin m→Nat) : Nat := (List.ofFn f).sum

private theorem total_add {m : Nat} (f g : Fin m→Nat) :
    total (fun i=>f i+g i)=total f+total g := by
  induction m with
  | zero => simp [total]
  | succ m ih =>
    unfold total
    simp only [List.ofFn_succ,List.sum_cons]
    have IH := ih (fun i=>f i.succ) (fun i=>g i.succ)
    unfold total at IH
    rw [IH]
    omega

private theorem one_slot {m : Nat} (i : Fin m) (v : Nat) :
    total (fun j=>if j=i then v else 0)=v := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun k=>?_) i
    · have zero (z : Nat) : (List.ofFn (fun _ : Fin z=>0)).sum=0 := by
        induction z with
        | zero => simp
        | succ z ih => rw [List.ofFn_succ,List.sum_cons,Nat.zero_add,ih]
      unfold total
      simp only [List.ofFn_succ,List.sum_cons,Fin.succ_ne_zero,if_false]
      simp [zero]
    · unfold total
      simp only [List.ofFn_succ,List.sum_cons,Ne.symm (Fin.succ_ne_zero k),if_false,Fin.succ_inj,Nat.zero_add]
      exact ih k

/-- Lifts a local two-rail arithmetic proof into the complete index
set under the exact disjoint frame. Either/both edited labels may
overwrite previously nonempty slots. -/
theorem pair_total_strict {m : Nat} (old new : Fin m→Nat) (i j : Fin m)
    (D : i≠j) (F : ∀ k,k≠i → k≠j → new k=old k)
    (H : new i+new j<old i+old j) :
    total new<total old := by
  let rest k := if k=i ∨ k=j then 0 else old k
  have parts (f : Fin m→Nat) (P : ∀ k,k≠i → k≠j → f k=old k) :
      total f=total rest+f i+f j := by
    have E : f=(fun k=>rest k+(if k=i then f i else 0)+(if k=j then f j else 0)) := by
      funext k
      by_cases I : k=i
      · subst k
        simp [rest,D]
      · by_cases J : k=j
        · subst k
          simp [rest,D.symm]
        · simp [rest,I,J,P _ I J]
    calc
      _ = total (fun k=>rest k+(if k=i then f i else 0)+(if k=j then f j else 0)) :=
        congrArg total E
      _ = _ := by rw [total_add,total_add,one_slot,one_slot]
  rw [parts new F,parts old (fun _ _ _=>rfl)]
  omega

theorem single_total_strict {m : Nat} (old new : Fin m→Nat) (i : Fin m)
    (F : ∀ k,k≠i → new k=old k) (H : new i<old i) :
    total new<total old := by
  let rest k := if k=i then 0 else old k
  have parts (f : Fin m→Nat) (P : ∀ k,k≠i → f k=old k) :
      total f=total rest+f i := by
    have E : f=(fun k=>rest k+if k=i then f i else 0) := by
      funext k
      by_cases I : k=i
      · subst k
        simp [rest]
      · simp [rest,I,P _ I]
    calc
      _ = total (fun k=>rest k+if k=i then f i else 0) := congrArg total E
      _ = _ := by rw [total_add,one_slot]
  rw [parts new F,parts old (fun _ _=>rfl)]
  omega

end L4.ReportPrelaunchRank
