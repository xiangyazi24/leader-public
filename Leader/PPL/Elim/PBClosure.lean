import Leader.PPL.Elim.SectorMonitor
import Lean

/-
Proof plan for YSM21 repair Lemma 1, on the literal row E.

Fix the selected directed edge e = (u,v), where v is the right neighbor of u.

1. Existing live bullet not at u.
   Peaceful has two clauses along the leftward scan:
   (a) every visited cell has signalB = false;
   (b) the first visited leader is shielded.
   Only u and v can change.  At v, clause (a) prevents the responder
   dummy-fire; clause (b), when v is the first leader, prevents deletion.
   At u, the scan can reach u only after passing v as a follower with
   signalB = false.  Hence line 62 cannot create a signal behind the bullet.
   All other cells are unchanged.

2. Existing live bullet at u.
   Its Peaceful head gives u.signalB = false, so u does not refire.
   If v is a follower, line 60 clears v.signalB before line 62.  Thus the
   old zero-signal trail remains zero after the bullet moves/merges, and the
   protected first leader clause is preserved.

3. A new live bullet at v.
   If v did not already contain a live bullet, finite row-E case analysis
   says the live bullet came either from an old live bullet at u or from the
   line-51 live firing of u.  In the former case use (2).  In the latter,
   line 51 gives u shield = true and signalB = false, while line 60 gives
   v.signalB = false, so the new bullet is immediately Peaceful.

4. Last leader.
   Row E never creates leaders and can delete only the responder v.  If v is
   the unique leader and an old live bullet from u could delete it, Peaceful
   at u scans the whole ring: all cells before v are followers, so its final
   visited cell is v and the two Peaceful clauses force
   v.signalB = false and v.shield = true.  Hence v cannot dummy-fire and
   cannot be deleted.  If the incoming live bullet was freshly fired, u is
   itself a second leader, contradicting uniqueness.

The Lean proof below mirrors exactly these four case families.  The recursive
peaceScan is a definitionally identical local proof view of RowE.lean's
private peacefulScanP; this avoids changing any existing public interface.
-/

set_option autoImplicit false

namespace PPL.Convergence.LDLocal

private theorem fin3_cases_local (b : Fin 3) :
    b = 0 ∨ b = 1 ∨ b = 2 := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega


/-! ## Literal row-E pair facts -/

private def ScanHeadSafe (u : PPL.Elim.Cell4) : Prop :=
  u.signalB = false ∧ (u.leader = true → u.shield = true)


private structure ScanFrame
    (before after : PPL.Elim.Cell4) : Prop where
  signalB : after.signalB = false
  leader : after.leader = before.leader
  shield : before.leader = true → after.shield = true


private theorem rowE_left_bullet_zero
    (l r : PPL.Elim.Cell4) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with rfl | rfl | rfl <;>
  rcases fin3_cases_local rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp [PPL.Elim.rowE]


private theorem rowE_left_scanFrame
    (l r : PPL.Elim.Cell4)
    (hl : ScanHeadSafe l)
    (hrLeader : r.leader = false)
    (hrSignal : r.signalB = false) :
    ScanFrame l (PPL.Elim.rowE l r).1 := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with rfl | rfl | rfl <;>
  rcases fin3_cases_local rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  constructor <;> simp_all [ScanHeadSafe, PPL.Elim.rowE]


private theorem rowE_left_live_scanFrame
    (l r : PPL.Elim.Cell4)
    (hlive : l.bullet = (2 : Fin 3))
    (hl : ScanHeadSafe l)
    (hrLeader : r.leader = false) :
    ScanFrame l (PPL.Elim.rowE l r).1 := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with rfl | rfl | rfl <;>
  rcases fin3_cases_local rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  constructor <;> simp_all [ScanHeadSafe, PPL.Elim.rowE]


private theorem rowE_right_scanFrame
    (l r : PPL.Elim.Cell4)
    (hr : ScanHeadSafe r) :
    ScanFrame r (PPL.Elim.rowE l r).2 := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with rfl | rfl | rfl <;>
  rcases fin3_cases_local rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  constructor <;> simp_all [ScanHeadSafe, PPL.Elim.rowE]


private theorem rowE_right_new_live_cases
    (l r : PPL.Elim.Cell4)
    (hold : r.bullet ≠ (2 : Fin 3))
    (hout : (PPL.Elim.rowE l r).2.bullet = (2 : Fin 3)) :
    r.leader = false ∧
      (PPL.Elim.rowE l r).2.signalB = false ∧
      (l.bullet = (2 : Fin 3) ∨
        (l.leader = true ∧ l.signalB = true)) := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with rfl | rfl | rfl <;>
  rcases fin3_cases_local rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_fired_source_is_safe_leader
    (l r : PPL.Elim.Cell4)
    (hlLeader : l.leader = true)
    (hlSignal : l.signalB = true)
    (hrLeader : r.leader = false) :
    (PPL.Elim.rowE l r).1.signalB = false ∧
      (PPL.Elim.rowE l r).1.leader = true ∧
      (PPL.Elim.rowE l r).1.shield = true := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with rfl | rfl | rfl <;>
  rcases fin3_cases_local rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_right_deleted_origin
    (l r : PPL.Elim.Cell4)
    (hrLeader : r.leader = true)
    (hout : (PPL.Elim.rowE l r).2.leader = false) :
    l.bullet = (2 : Fin 3) ∨
      (l.leader = true ∧ l.signalB = true) := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with rfl | rfl | rfl <;>
  rcases fin3_cases_local rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_right_survives_live_safe
    (l r : PPL.Elim.Cell4)
    (hlive : l.bullet = (2 : Fin 3))
    (hrLeader : r.leader = true)
    (hrSignal : r.signalB = false)
    (hrShield : r.shield = true) :
    (PPL.Elim.rowE l r).2.leader = true := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with rfl | rfl | rfl <;>
  rcases fin3_cases_local rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


/-! ## Ring and concrete step equations -/

private theorem rightNeighbor_ne_self_local
    {n : Nat} (R : DirectedRing n) (hn2 : 2 ≤ n) (i : Fin n) :
    R.rightNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : i.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega


private theorem leftNeighbor_rightNeighbor_local
    {n : Nat} (R : DirectedRing n) (i : Fin n) :
    R.leftNeighbor (R.rightNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq : i.val + 1 + n - 1 = n + i.val := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega


private theorem rightNeighbor_leftNeighbor_local
    {n : Nat} (R : DirectedRing n) (i : Fin n) :
    R.rightNeighbor (R.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]


private theorem stepE_source
    {n : Nat} (R : DirectedRing n) (C : Config n) (e : Fin n) :
    stepE R C e e =
      (PPL.Elim.rowE (C e) (C (R.rightNeighbor e))).1 := by
  change
    (show Config n from
      fun k =>
        if k = e then
          (PPL.Elim.rowE (C e) (C (R.rightNeighbor e))).1
        else if k = R.rightNeighbor e then
          (PPL.Elim.rowE (C e) (C (R.rightNeighbor e))).2
        else
          C k) e =
      (PPL.Elim.rowE (C e) (C (R.rightNeighbor e))).1
  simp


private theorem stepE_responder
    {n : Nat} (R : DirectedRing n) (C : Config n) (e : Fin n)
    (hne : e ≠ R.rightNeighbor e) :
    stepE R C e (R.rightNeighbor e) =
      (PPL.Elim.rowE (C e) (C (R.rightNeighbor e))).2 := by
  have hne' : R.rightNeighbor e ≠ e := Ne.symm hne
  change
    (show Config n from
      fun k =>
        if k = e then
          (PPL.Elim.rowE (C e) (C (R.rightNeighbor e))).1
        else if k = R.rightNeighbor e then
          (PPL.Elim.rowE (C e) (C (R.rightNeighbor e))).2
        else
          C k) (R.rightNeighbor e) =
      (PPL.Elim.rowE (C e) (C (R.rightNeighbor e))).2
  simp [hne, hne']


private theorem stepE_other
    {n : Nat} (R : DirectedRing n) (C : Config n) (e k : Fin n)
    (hke : k ≠ e) (hkr : k ≠ R.rightNeighbor e) :
    stepE R C e k = C k := by
  change
    (show Config n from
      fun x =>
        if x = e then
          (PPL.Elim.rowE (C e) (C (R.rightNeighbor e))).1
        else if x = R.rightNeighbor e then
          (PPL.Elim.rowE (C e) (C (R.rightNeighbor e))).2
        else
          C x) k = C k
  simp [hke, hkr]


private theorem stepE_leader_eq_of_ne_responder
    {n : Nat} (R : DirectedRing n) (C : Config n) (e k : Fin n)
    (hk : k ≠ R.rightNeighbor e) :
    (stepE R C e k).leader = (C k).leader := by
  by_cases hke : k = e
  · subst k
    rw [stepE_source, PPL.Elim.rowE_left_leader]
  · rw [stepE_other R C e k hke hk]


/-! ## Local proof view of Peaceful -/

/-- The arbitrary-fuel scan already used by `Elim.Peaceful`.
The upstream scan is private, so its constant is recovered from the public
definition instead of maintaining a second recursive function. -/
private def peaceScan {n : Nat} (R : DirectedRing n)
    (C : Config n) : Nat → Fin n → Prop := by
  run_tac
    let body := (← Lean.getConstInfoDefn `PPL.Elim.Peaceful).value
    let .const nm _ := body.bindingBody!.bindingBody!.bindingBody!.bindingBody!.getAppFn
      | throwError "Peaceful no longer uses a recursive scan constant"
    let size := (← Lean.Meta.getLocalDeclFromUserName `n).toExpr
    let ring := (← Lean.Meta.getLocalDeclFromUserName `R).toExpr
    let config := (← Lean.Meta.getLocalDeclFromUserName `C).toExpr
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign (Lean.mkApp3 (Lean.mkConst nm) size ring config)


private theorem peaceful_iff_peaceScan
    {n : Nat} (R : DirectedRing n) (C : Config n) (i : Fin n) :
    PPL.Elim.Peaceful R C i ↔ peaceScan R C n i := by
  unfold PPL.Elim.Peaceful peaceScan
  rfl


private theorem peaceScan_head
    {n : Nat} (R : DirectedRing n) (C : Config n)
    (fuel : Nat) (i : Fin n)
    (h : peaceScan R C (fuel + 1) i) :
    ScanHeadSafe (C i) := by
  change
    (C i).signalB = false ∧
      (if (C i).leader = true then
        (C i).shield = true
      else
        peaceScan R C fuel (R.leftNeighbor i)) at h
  refine ⟨h.1, ?_⟩
  intro hl
  simpa [hl] using h.2


private theorem peaceScan_tail
    {n : Nat} (R : DirectedRing n) (C : Config n)
    (fuel : Nat) (i : Fin n)
    (h : peaceScan R C (fuel + 1) i)
    (hl : (C i).leader = false) :
    peaceScan R C fuel (R.leftNeighbor i) := by
  change
    (C i).signalB = false ∧
      (if (C i).leader = true then
        (C i).shield = true
      else
        peaceScan R C fuel (R.leftNeighbor i)) at h
  simpa [hl] using h.2


private theorem stepE_scanFrame_ne_source
    {n : Nat} (hn2 : 2 ≤ n)
    (R : DirectedRing n) (C : Config n) (e x : Fin n)
    (hx : x ≠ e) (h : ScanHeadSafe (C x)) :
    ScanFrame (C x) (stepE R C e x) := by
  let j := R.rightNeighbor e
  have hne : e ≠ j := (rightNeighbor_ne_self_local R hn2 e).symm
  by_cases hxj : x = j
  · subst x
    rw [stepE_responder R C e hne]
    exact rowE_right_scanFrame (C e) (C j) h
  · rw [stepE_other R C e x hx (by simpa [j] using hxj)]
    exact ⟨h.1, rfl, h.2⟩


private theorem stepE_scanFrame_source
    {n : Nat} (R : DirectedRing n) (C : Config n) (e : Fin n)
    (h : ScanHeadSafe (C e))
    (hrLeader : (C (R.rightNeighbor e)).leader = false)
    (hrSignal : (C (R.rightNeighbor e)).signalB = false) :
    ScanFrame (C e) (stepE R C e e) := by
  rw [stepE_source]
  exact rowE_left_scanFrame
    (C e) (C (R.rightNeighbor e)) h hrLeader hrSignal


private theorem stepE_scanFrame_source_live
    {n : Nat} (R : DirectedRing n) (C : Config n) (e : Fin n)
    (hlive : (C e).bullet = (2 : Fin 3))
    (h : ScanHeadSafe (C e))
    (hrLeader : (C (R.rightNeighbor e)).leader = false) :
    ScanFrame (C e) (stepE R C e e) := by
  rw [stepE_source]
  exact rowE_left_live_scanFrame
    (C e) (C (R.rightNeighbor e)) hlive h hrLeader


private theorem peaceScan_preserve_with_right
    {n : Nat} (hn2 : 2 ≤ n)
    (R : DirectedRing n) (C : Config n) (e : Fin n) :
    ∀ (fuel : Nat) (x : Fin n),
      peaceScan R C fuel x →
      (C (R.rightNeighbor x)).leader = false →
      (C (R.rightNeighbor x)).signalB = false →
      peaceScan R (stepE R C e) fuel x := by
  intro fuel
  induction fuel with
  | zero =>
      intro x h hrL hrS
      trivial
  | succ fuel ih =>
      intro x hscan hrL hrS
      have hhead := peaceScan_head R C fuel x hscan
      have hframe : ScanFrame (C x) (stepE R C e x) := by
        by_cases hxe : x = e
        · subst x
          exact stepE_scanFrame_source R C e hhead hrL hrS
        · exact stepE_scanFrame_ne_source hn2 R C e x hxe hhead
      change
        (stepE R C e x).signalB = false ∧
          (if (stepE R C e x).leader = true then
            (stepE R C e x).shield = true
          else
            peaceScan R (stepE R C e) fuel (R.leftNeighbor x))
      refine ⟨hframe.signalB, ?_⟩
      cases hl : (C x).leader with
      | true =>
          have hnew : (stepE R C e x).leader = true := by
            rw [hframe.leader, hl]
          simpa [hnew] using hframe.shield hl
      | false =>
          have hnew : (stepE R C e x).leader = false := by
            rw [hframe.leader, hl]
          have htail :=
            peaceScan_tail R C fuel x hscan hl
          have hrl :
              R.rightNeighbor (R.leftNeighbor x) = x :=
            rightNeighbor_leftNeighbor_local R x
          have hnextL :
              (C (R.rightNeighbor (R.leftNeighbor x))).leader = false := by
            rw [hrl]
            exact hl
          have hnextS :
              (C (R.rightNeighbor (R.leftNeighbor x))).signalB = false := by
            rw [hrl]
            exact hhead.1
          have htail' :=
            ih (R.leftNeighbor x) htail hnextL hnextS
          simpa [hnew] using htail'


private theorem peaceScan_preserve_ne_source
    {n : Nat} (hn2 : 2 ≤ n)
    (R : DirectedRing n) (C : Config n) (e : Fin n)
    (fuel : Nat) (x : Fin n)
    (hx : x ≠ e)
    (hscan : peaceScan R C fuel x) :
    peaceScan R (stepE R C e) fuel x := by
  cases fuel with
  | zero =>
      trivial
  | succ fuel =>
      have hhead := peaceScan_head R C fuel x hscan
      have hframe :=
        stepE_scanFrame_ne_source hn2 R C e x hx hhead
      change
        (stepE R C e x).signalB = false ∧
          (if (stepE R C e x).leader = true then
            (stepE R C e x).shield = true
          else
            peaceScan R (stepE R C e) fuel (R.leftNeighbor x))
      refine ⟨hframe.signalB, ?_⟩
      cases hl : (C x).leader with
      | true =>
          have hnew : (stepE R C e x).leader = true := by
            rw [hframe.leader, hl]
          simpa [hnew] using hframe.shield hl
      | false =>
          have hnew : (stepE R C e x).leader = false := by
            rw [hframe.leader, hl]
          have htail :=
            peaceScan_tail R C fuel x hscan hl
          have hrl :
              R.rightNeighbor (R.leftNeighbor x) = x :=
            rightNeighbor_leftNeighbor_local R x
          have hnextL :
              (C (R.rightNeighbor (R.leftNeighbor x))).leader = false := by
            rw [hrl]
            exact hl
          have hnextS :
              (C (R.rightNeighbor (R.leftNeighbor x))).signalB = false := by
            rw [hrl]
            exact hhead.1
          have htail' :=
            peaceScan_preserve_with_right hn2 R C e
              fuel (R.leftNeighbor x) htail hnextL hnextS
          simpa [hnew] using htail'


private theorem peaceScan_preserve_source_live
    {n : Nat} (hn2 : 2 ≤ n)
    (R : DirectedRing n) (C : Config n) (e : Fin n)
    (fuel : Nat) (hfuel : 0 < fuel)
    (hscan : peaceScan R C fuel e)
    (hlive : (C e).bullet = (2 : Fin 3))
    (hrLeader : (C (R.rightNeighbor e)).leader = false) :
    peaceScan R (stepE R C e) fuel e := by
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      have hhead := peaceScan_head R C fuel e hscan
      have hframe :=
        stepE_scanFrame_source_live R C e hlive hhead hrLeader
      change
        (stepE R C e e).signalB = false ∧
          (if (stepE R C e e).leader = true then
            (stepE R C e e).shield = true
          else
            peaceScan R (stepE R C e) fuel (R.leftNeighbor e))
      refine ⟨hframe.signalB, ?_⟩
      cases hl : (C e).leader with
      | true =>
          have hnew : (stepE R C e e).leader = true := by
            rw [hframe.leader, hl]
          simpa [hnew] using hframe.shield hl
      | false =>
          have hnew : (stepE R C e e).leader = false := by
            rw [hframe.leader, hl]
          have htail :=
            peaceScan_tail R C fuel e hscan hl
          have hrl :
              R.rightNeighbor (R.leftNeighbor e) = e :=
            rightNeighbor_leftNeighbor_local R e
          have hnextL :
              (C (R.rightNeighbor (R.leftNeighbor e))).leader = false := by
            rw [hrl]
            exact hl
          have hnextS :
              (C (R.rightNeighbor (R.leftNeighbor e))).signalB = false := by
            rw [hrl]
            exact hhead.1
          have htail' :=
            peaceScan_preserve_with_right hn2 R C e
              fuel (R.leftNeighbor e) htail hnextL hnextS
          simpa [hnew] using htail'


private theorem peaceScan_drop_one
    {n : Nat} (R : DirectedRing n) (C : Config n) :
    ∀ (fuel : Nat) (i : Fin n),
      peaceScan R C (fuel + 1) i →
      peaceScan R C fuel i := by
  intro fuel
  induction fuel with
  | zero =>
      intro i h
      trivial
  | succ fuel ih =>
      intro i h
      have hhead := peaceScan_head R C (fuel + 1) i h
      change
        (C i).signalB = false ∧
          (if (C i).leader = true then
            (C i).shield = true
          else
            peaceScan R C fuel (R.leftNeighbor i))
      refine ⟨hhead.1, ?_⟩
      cases hl : (C i).leader with
      | true =>
          simpa [hl] using hhead.2 hl
      | false =>
          have htail :=
            peaceScan_tail R C (fuel + 1) i h hl
          have htail' := ih (R.leftNeighbor i) htail
          simpa [hl] using htail'


private theorem peaceScan_safe_leader
    {n : Nat} (R : DirectedRing n) (C : Config n)
    (fuel : Nat) (i : Fin n)
    (hfuel : 0 < fuel)
    (hs : (C i).signalB = false)
    (hl : (C i).leader = true)
    (hh : (C i).shield = true) :
    peaceScan R C fuel i := by
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      change
        (C i).signalB = false ∧
          (if (C i).leader = true then
            (C i).shield = true
          else
            peaceScan R C fuel (R.leftNeighbor i))
      exact ⟨hs, by simpa [hl] using hh⟩


/-! ## The one-leader geometry used by Lemma 10 -/

private def leftOffset {n : Nat} (R : DirectedRing n)
    (i : Fin n) (d : Nat) : Fin n :=
  ⟨(i.val + n - d % n) % n, Nat.mod_lt _ R.hn⟩


private theorem leftOffset_val_of_le
    {n : Nat} (R : DirectedRing n) (i : Fin n)
    (d : Nat) (hd : d < n) (hle : d ≤ i.val) :
    (leftOffset R i d).val = i.val - d := by
  simp only [leftOffset]
  rw [Nat.mod_eq_of_lt hd]
  have heq : i.val + n - d = n + (i.val - d) := by omega
  rw [heq, add_self_mod, Nat.mod_eq_of_lt (by omega : i.val - d < n)]


private theorem leftOffset_val_of_lt
    {n : Nat} (R : DirectedRing n) (i : Fin n)
    (d : Nat) (hd : d < n) (hlt : i.val < d) :
    (leftOffset R i d).val = n - (d - i.val) := by
  simp only [leftOffset]
  rw [Nat.mod_eq_of_lt hd]
  have heq : i.val + n - d = n - (d - i.val) := by omega
  rw [heq, Nat.mod_eq_of_lt (by omega : n - (d - i.val) < n)]


private theorem leftOffset_zero
    {n : Nat} (R : DirectedRing n) (i : Fin n) :
    leftOffset R i 0 = i := by
  apply Fin.ext
  rw [leftOffset_val_of_le R i 0 R.hn (Nat.zero_le _)]
  simp


private theorem leftNeighbor_val_of_pos
    {n : Nat} (R : DirectedRing n) (i : Fin n)
    (hi : 0 < i.val) :
    (R.leftNeighbor i).val = i.val - 1 := by
  simp only [DirectedRing.leftNeighbor]
  have heq : i.val + n - 1 = n + (i.val - 1) := by omega
  rw [heq, add_self_mod, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]


private theorem leftNeighbor_val_of_zero
    {n : Nat} (R : DirectedRing n) (i : Fin n)
    (hi : i.val = 0) :
    (R.leftNeighbor i).val = n - 1 := by
  simp only [DirectedRing.leftNeighbor, hi, Nat.zero_add]
  rw [Nat.mod_eq_of_lt (by omega : n - 1 < n)]


private theorem leftOffset_succ
    {n : Nat} (R : DirectedRing n) (i : Fin n)
    (d : Nat) (hd : d + 1 < n) :
    R.leftNeighbor (leftOffset R i d) =
      leftOffset R i (d + 1) := by
  apply Fin.ext
  by_cases hlt : d < i.val
  · have hcur :
        (leftOffset R i d).val = i.val - d :=
      leftOffset_val_of_le R i d (by omega) (by omega)
    have hcurPos : 0 < (leftOffset R i d).val := by
      rw [hcur]
      omega
    rw [leftNeighbor_val_of_pos R _ hcurPos,
      leftOffset_val_of_le R i d (by omega) (by omega),
      leftOffset_val_of_le R i (d + 1) hd (by omega)]
    omega
  · by_cases heq : d = i.val
    · have hcur :
          (leftOffset R i d).val = 0 := by
        rw [leftOffset_val_of_le R i d (by omega) (by omega)]
        omega
      rw [leftNeighbor_val_of_zero R _ hcur,
        leftOffset_val_of_lt R i (d + 1) hd (by omega)]
      omega
    · have hgt : i.val < d := by omega
      have hcur :
          (leftOffset R i d).val = n - (d - i.val) :=
        leftOffset_val_of_lt R i d (by omega) hgt
      have hcurPos : 0 < (leftOffset R i d).val := by
        rw [hcur]
        omega
      rw [leftNeighbor_val_of_pos R _ hcurPos,
        leftOffset_val_of_lt R i d (by omega) hgt,
        leftOffset_val_of_lt R i (d + 1) hd (by omega)]
      omega


private theorem leftOffset_last
    {n : Nat} (R : DirectedRing n) (hn2 : 2 ≤ n) (i : Fin n) :
    leftOffset R i (n - 1) = R.rightNeighbor i := by
  apply Fin.ext
  simp only [leftOffset, DirectedRing.rightNeighbor]
  rw [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
  have heq : i.val + n - (n - 1) = i.val + 1 := by omega
  rw [heq]


private theorem leftOffset_ne_rightNeighbor_of_lt
    {n : Nat} (R : DirectedRing n) (hn2 : 2 ≤ n)
    (i : Fin n) (d : Nat) (hd : d < n - 1) :
    leftOffset R i d ≠ R.rightNeighbor i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hwrap : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hwrap] at hv
    by_cases hle : d ≤ i.val
    · rw [leftOffset_val_of_le R i d (by omega) hle] at hv
      omega
    · rw [leftOffset_val_of_lt R i d (by omega) (by omega)] at hv
      omega
  · have hi : i.val + 1 = n := by omega
    rw [hi, Nat.mod_self] at hv
    rw [leftOffset_val_of_le R i d (by omega) (by omega)] at hv
    omega


private theorem peaceScan_shift_followers
    {n : Nat} (hn2 : 2 ≤ n)
    (R : DirectedRing n) (C : Config n) (start : Fin n) :
    ∀ d : Nat, d < n →
      peaceScan R C n start →
      (∀ q : Nat, q < d →
        (C (leftOffset R start q)).leader = false) →
      peaceScan R C (n - d) (leftOffset R start d) := by
  intro d
  induction d with
  | zero =>
      intro hd hscan hfollowers
      rw [leftOffset_zero]
      simpa using hscan
  | succ d ih =>
      intro hd hscan hfollowers
      have hprev :=
        ih (by omega) hscan
          (fun q hq => hfollowers q (by omega))
      have hlead :
          (C (leftOffset R start d)).leader = false :=
        hfollowers d (by omega)
      have hdecomp :
          n - d = (n - (d + 1)) + 1 := by omega
      rw [hdecomp] at hprev
      have htail :=
        peaceScan_tail R C (n - (d + 1))
          (leftOffset R start d) hprev hlead
      rw [leftOffset_succ R start d hd] at htail
      exact htail


private theorem peaceScan_unique_right_safe
    {n : Nat} (hn2 : 2 ≤ n)
    (R : DirectedRing n) (C : Config n) (e : Fin n)
    (hscan : peaceScan R C n e)
    (honly :
      ∀ k : Fin n, (C k).leader = true →
        k = R.rightNeighbor e)
    (hrLeader : (C (R.rightNeighbor e)).leader = true) :
    (C (R.rightNeighbor e)).signalB = false ∧
      (C (R.rightNeighbor e)).shield = true := by
  have hfollowers :
      ∀ q : Nat, q < n - 1 →
        (C (leftOffset R e q)).leader = false := by
    intro q hq
    cases hl : (C (leftOffset R e q)).leader with
    | false =>
        rfl
    | true =>
        have heq := honly (leftOffset R e q) hl
        exact False.elim
          ((leftOffset_ne_rightNeighbor_of_lt R hn2 e q hq) heq)
  have hlast :=
    peaceScan_shift_followers hn2 R C e
      (n - 1) (by omega) hscan hfollowers
  rw [leftOffset_last R hn2 e] at hlast
  have hone : n - (n - 1) = 1 := by omega
  rw [hone] at hlast
  have hhead :=
    peaceScan_head R C 0 (R.rightNeighbor e) hlast
  exact ⟨hhead.1, hhead.2 hrLeader⟩


/-! ## Leader-count helpers -/

private theorem leaderCount_eq_sum
    {n : Nat} (C : Config n) :
    PPL.Elim.leaderCount C =
      (List.ofFn
        (fun i : Fin n => if (C i).leader then 1 else 0)).sum := by
  rfl


private theorem leaderCount_pos_of_true
    {n : Nat} (C : Config n) (i : Fin n)
    (hi : (C i).leader = true) :
    0 < PPL.Elim.leaderCount C := by
  rw [leaderCount_eq_sum]
  have hmem :
      1 ∈
        List.ofFn
          (fun k : Fin n => if (C k).leader then 1 else 0) := by
    rw [List.mem_ofFn]
    exact ⟨i, by simp [hi]⟩
  by_cases hz :
      (List.ofFn
        (fun k : Fin n => if (C k).leader then 1 else 0)).sum = 0
  · have hall := List.sum_eq_zero_iff_forall_eq_nat.mp hz
    have hone := hall 1 hmem
    omega
  · omega


private theorem exists_leader_of_count_pos
    {n : Nat} (C : Config n)
    (hpos : 0 < PPL.Elim.leaderCount C) :
    ∃ i : Fin n, (C i).leader = true := by
  by_cases hex : ∃ i : Fin n, (C i).leader = true
  · exact hex
  ·
    have hall : ∀ i : Fin n, (C i).leader = false := by
      intro i
      cases hi : (C i).leader with
      | false =>
          rfl
      | true =>
          exact False.elim (hex ⟨i, hi⟩)
    rw [leaderCount_eq_sum] at hpos
    have hz :
        (List.ofFn
          (fun k : Fin n => if (C k).leader then 1 else 0)).sum = 0 := by
      apply List.sum_eq_zero_iff_forall_eq_nat.mpr
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      simp [hall i]
    rw [hz] at hpos
    omega


private theorem bool_sum_one_unique :
    ∀ {n : Nat} (f : Fin n → Bool) (i j : Fin n),
      (List.ofFn (fun k : Fin n => if f k then 1 else 0)).sum = 1 →
      f i = true →
      f j = true →
      i = j := by
  intro n
  induction n with
  | zero =>
      intro f i
      exact Fin.elim0 i
  | succ n ih =>
      intro f i j hsum hi hj
      rw [List.ofFn_succ, List.sum_cons] at hsum
      by_cases h0 : f 0 = true
      · have htail :
            (List.ofFn
              (fun k : Fin n => if f k.succ then 1 else 0)).sum = 0 := by
          simp [h0] at hsum
          omega
        have hzero :=
          List.sum_eq_zero_iff_forall_eq_nat.mp htail
        have only0 :
            ∀ k : Fin (n + 1), f k = true → k = 0 := by
          intro k hk
          cases k using Fin.cases with
          | zero =>
              rfl
          | succ k =>
              have hmem :
                  (if f k.succ then 1 else 0) ∈
                    List.ofFn
                      (fun q : Fin n =>
                        if f q.succ then 1 else 0) := by
                rw [List.mem_ofFn]
                exact ⟨k, rfl⟩
              have hz := hzero _ hmem
              simp [hk] at hz
        rw [only0 i hi, only0 j hj]
      · have h0f : f 0 = false := by
          cases hv : f 0 with
          | false =>
              rfl
          | true =>
              exact False.elim (h0 hv)
        have htail :
            (List.ofFn
              (fun k : Fin n => if f k.succ then 1 else 0)).sum = 1 := by
          simpa [h0f] using hsum
        cases i using Fin.cases with
        | zero =>
            simp [h0f] at hi
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                simp [h0f] at hj
            | succ j =>
                have hij :=
                  ih (fun k : Fin n => f k.succ)
                    i j htail hi hj
                simpa using congrArg Fin.succ hij


private theorem leaderCount_one_unique
    {n : Nat} (C : Config n)
    (hcount : PPL.Elim.leaderCount C = 1)
    (root : Fin n) (hroot : (C root).leader = true) :
    ∀ k : Fin n, (C k).leader = true → k = root := by
  intro k hk
  rw [leaderCount_eq_sum] at hcount
  exact bool_sum_one_unique
    (fun i : Fin n => (C i).leader)
    k root hcount hk hroot


/-! ## Last-leader core -/

private theorem lastLeaderSurvivalCore :
    PPL.Convergence.LDLocal.LastLeaderSurvival := by
  intro m R C e hPB hcount
  have hmpos : 0 < m := R.hn
  by_cases hm1 : m = 1
  · subst m
    obtain ⟨root, hroot⟩ := hPB.1
    have hre : root = e := Subsingleton.elim _ _
    subst root
    have hsurvive :
        (stepE R C e e).leader = true := by
      rw [stepE_source, PPL.Elim.rowE_left_leader]
      exact hroot
    have hpos' :=
      leaderCount_pos_of_true (stepE R C e) e hsurvive
    have hle :=
      (PPL.Elim.leaderCount_step_sandwich R C e).1
    have hle' :
        PPL.Elim.leaderCount (stepE R C e) ≤ 1 := by
      simpa [stepE, hcount] using hle
    omega
  · have hm2 : 2 ≤ m := by omega
    let j := R.rightNeighbor e
    have hne : e ≠ j := by
      exact (rightNeighbor_ne_self_local R hm2 e).symm
    obtain ⟨root, hroot⟩ := hPB.1
    by_cases hrj : root = j
    · subst root
      have honly :
          ∀ k : Fin m, (C k).leader = true → k = j :=
        leaderCount_one_unique C hcount j hroot
      have hjSurvives :
          (stepE R C e j).leader = true := by
        cases hout : (stepE R C e j).leader with
        | true =>
            rfl
        | false =>
            have hrowOut :
                (PPL.Elim.rowE (C e) (C j)).2.leader = false := by
              rw [stepE_responder R C e hne] at hout
              exact hout
            have horigin :=
              rowE_right_deleted_origin (C e) (C j)
                hroot hrowOut
            rcases horigin with hlive | hfire
            · have hpeace := hPB.2 e hlive
              have hscan :=
                (peaceful_iff_peaceScan R C e).1 hpeace
              have hsafe :=
                peaceScan_unique_right_safe
                  hm2 R C e hscan honly hroot
              have hrowSurvives :=
                rowE_right_survives_live_safe
                  (C e) (C j) hlive hroot hsafe.1 hsafe.2
              rw [hrowSurvives] at hrowOut
              contradiction
            · have heq := honly e hfire.1
              exact False.elim (hne heq)
      have hpos' :=
        leaderCount_pos_of_true (stepE R C e) j hjSurvives
      have hle :=
        (PPL.Elim.leaderCount_step_sandwich R C e).1
      have hle' :
          PPL.Elim.leaderCount (stepE R C e) ≤ 1 := by
        simpa [stepE, hcount] using hle
      omega
    · have hrootSurvives :
          (stepE R C e root).leader = true := by
        have hframe :=
          stepE_leader_eq_of_ne_responder
            R C e root (by simpa [j] using hrj)
        rw [hframe]
        exact hroot
      have hpos' :=
        leaderCount_pos_of_true
          (stepE R C e) root hrootSurvives
      have hle :=
        (PPL.Elim.leaderCount_step_sandwich R C e).1
      have hle' :
          PPL.Elim.leaderCount (stepE R C e) ≤ 1 := by
        simpa [stepE, hcount] using hle
      omega


/-! ## Peaceful live bullets after one step -/

private theorem liveOutputsPeaceful_of_pb
    {n : Nat} (hn2 : 2 ≤ n)
    (R : DirectedRing n) (C : Config n) (e : Fin n)
    (hPB : PPL.Elim.PB R C) :
    ∀ i : Fin n,
      (stepE R C e i).bullet = (2 : Fin 3) →
      PPL.Elim.Peaceful R (stepE R C e) i := by
  intro i hLive
  let j := R.rightNeighbor e
  have hne : e ≠ j :=
    (rightNeighbor_ne_self_local R hn2 e).symm
  by_cases hie : i = e
  · subst i
    have hz :
        (stepE R C e e).bullet = (0 : Fin 3) := by
      rw [stepE_source]
      exact rowE_left_bullet_zero
        (C e) (C (R.rightNeighbor e))
    rw [hz] at hLive
    have hv := congrArg Fin.val hLive
    simp at hv
  · by_cases hij : i = j
    · subst i
      have hrowLive :
          (PPL.Elim.rowE (C e) (C j)).2.bullet =
            (2 : Fin 3) := by
        rw [stepE_responder R C e hne] at hLive
        exact hLive
      by_cases hold : (C j).bullet = (2 : Fin 3)
      · have hpeace := hPB.2 j hold
        have hscan :=
          (peaceful_iff_peaceScan R C j).1 hpeace
        have hscan' :=
          peaceScan_preserve_ne_source
            hn2 R C e n j (Ne.symm hne) hscan
        exact
          (peaceful_iff_peaceScan
            R (stepE R C e) j).2 hscan'
      · have hinfo :=
          rowE_right_new_live_cases
            (C e) (C j) hold hrowLive
        rcases hinfo with
          ⟨hrFollower, hrSignal, horigin⟩
        have htail :
            peaceScan R (stepE R C e) (n - 1) e := by
          rcases horigin with hsrcLive | hfire
          · have hpeaceSrc := hPB.2 e hsrcLive
            have hscanFull :=
              (peaceful_iff_peaceScan R C e).1 hpeaceSrc
            have heq : (n - 1) + 1 = n := by omega
            have hscanFull' :
                peaceScan R C ((n - 1) + 1) e := by
              simpa [heq] using hscanFull
            have hshort :=
              peaceScan_drop_one R C (n - 1) e hscanFull'
            exact
              peaceScan_preserve_source_live
                hn2 R C e (n - 1) (by omega)
                hshort hsrcLive hrFollower
          · have hfields :=
              rowE_fired_source_is_safe_leader
                (C e) (C j) hfire.1 hfire.2 hrFollower
            have hsource := stepE_source R C e
            have hs :
                (stepE R C e e).signalB = false := by
              rw [hsource]
              exact hfields.1
            have hl :
                (stepE R C e e).leader = true := by
              rw [hsource]
              exact hfields.2.1
            have hh :
                (stepE R C e e).shield = true := by
              rw [hsource]
              exact hfields.2.2
            exact
              peaceScan_safe_leader
                R (stepE R C e) (n - 1) e
                (by omega) hs hl hh
        have hjStep :=
          stepE_responder R C e hne
        have hjSignal :
            (stepE R C e j).signalB = false := by
          rw [hjStep]
          exact hrSignal
        have hjLeader :
            (stepE R C e j).leader = false := by
          rw [hjStep]
          exact
            PPL.Elim.rowE_right_leader_false_of_false
              (C e) (C j) hrFollower
        have hleft :
            R.leftNeighbor j = e := by
          dsimp [j]
          exact leftNeighbor_rightNeighbor_local R e
        apply
          (peaceful_iff_peaceScan
            R (stepE R C e) j).2
        have hscanJ :
            peaceScan R (stepE R C e) ((n - 1) + 1) j := by
          change
          (stepE R C e j).signalB = false ∧
            (if (stepE R C e j).leader = true then
              (stepE R C e j).shield = true
            else
              peaceScan R (stepE R C e) (n - 1)
                (R.leftNeighbor j))
          refine ⟨hjSignal, ?_⟩
          simpa [hjLeader, hleft] using htail
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hscanJ
    · have hsame :
          stepE R C e i = C i := by
        exact stepE_other R C e i hie
          (by simpa [j] using hij)
      have hold : (C i).bullet = (2 : Fin 3) := by
        rw [hsame] at hLive
        exact hLive
      have hpeace := hPB.2 i hold
      have hscan :=
        (peaceful_iff_peaceScan R C i).1 hpeace
      have hscan' :=
        peaceScan_preserve_ne_source
          hn2 R C e n i hie hscan
      exact
        (peaceful_iff_peaceScan
          R (stepE R C e) i).2 hscan'


/-! ## Requested theorems -/

theorem pbStepClosure :
    PPL.Convergence.LDLocal.PBStepClosure := by
  intro m R C e hPB
  have hmpos : 0 < m := R.hn
  by_cases hm1 : m = 1
  · subst m
    obtain ⟨root, hroot⟩ := hPB.1
    have hre : root = e := Subsingleton.elim _ _
    subst root
    refine ⟨?_, ?_⟩
    · refine ⟨e, ?_⟩
      rw [stepE_source, PPL.Elim.rowE_left_leader]
      exact hroot
    · intro i hLive
      have hie : i = e := Subsingleton.elim _ _
      subst i
      have hz :
          (stepE R C e e).bullet = (0 : Fin 3) := by
        rw [stepE_source]
        exact rowE_left_bullet_zero
          (C e) (C (R.rightNeighbor e))
      rw [hz] at hLive
      have hv := congrArg Fin.val hLive
      simp at hv
  · have hm2 : 2 ≤ m := by omega
    refine ⟨?_, liveOutputsPeaceful_of_pb hm2 R C e hPB⟩
    obtain ⟨root, hroot⟩ := hPB.1
    have hpos :=
      leaderCount_pos_of_true C root hroot
    by_cases hcount1 : PPL.Elim.leaderCount C = 1
    · have hsurvive :=
        lastLeaderSurvivalCore R C e hPB hcount1
      have hpos' :
          0 < PPL.Elim.leaderCount (stepE R C e) := by
        omega
      exact
        exists_leader_of_count_pos
          (stepE R C e) hpos'
    · have htwo : 2 ≤ PPL.Elim.leaderCount C := by omega
      have hsand :=
        PPL.Elim.leaderCount_step_sandwich R C e
      have hpos' :
          0 < PPL.Elim.leaderCount (stepE R C e) := by
        have hback :
            PPL.Elim.leaderCount C ≤
              PPL.Elim.leaderCount (stepE R C e) + 1 := by
          simpa [stepE] using hsand.2
        omega
      exact
        exists_leader_of_count_pos
          (stepE R C e) hpos'


theorem lastLeaderSurvival :
    PPL.Convergence.LDLocal.LastLeaderSurvival :=
  lastLeaderSurvivalCore


end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.pbStepClosure
#print axioms PPL.Convergence.LDLocal.lastLeaderSurvival
