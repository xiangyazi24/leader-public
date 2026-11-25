import Leader.L4.WindowOwnership
import Leader.L4.WindowProtectedSlot

namespace L4.WindowOrdinarySlot
open SevenTagCharge WindowOwnership WindowLocal WindowProtectedOuter GGTiming

/-- During one ordinary transaction, retain precisely the old certified segment
and target. On the first non-keep, save the actual post-mark joined cursor. -/
inductive Slot {p c n : Nat} (x : Config p c n) (g cert : List (Fin n)) (a : Fin n)
  | active (F : Front x g) (P : Progress F.ledger g) (mode : F.mode=.owned P)
      (cert_eq : P.cert=cert) (target_eq : P.target=some a)
  | stop (q : WindowLatch.Cursor (Front x g) x g)

def Slot.physical {p c n : Nat} {x : Config p c n} {g cert : List (Fin n)} {a : Fin n}
    (s : Slot x g cert a) : WindowLatch.Cursor (Front x g) x g :=
  match s with
  | .active F .. => .inl F
  | .stop q => q

def Slot.done {p c n : Nat} {x : Config p c n} {g cert : List (Fin n)} {a : Fin n}
    (s : Slot x g cert a) : Prop :=
  match s with
  | .active .. => False
  | .stop _ => True

/-- Only the auxiliary inspection stops; even padding advances the joined ledger. -/
noncomputable def next {p c n : Nat} {x : Config p c n} {g cert : List (Fin n)} {a : Fin n}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (s : Slot x g cert a) (e : Fin n) :
    Slot x g cert a :=
  let actual := joinedNext (WindowLatch.front hn (WindowOwnership.decide hp hc hn))
  match s with
  | .stop q => .stop (actual q e)
  | .active F P _ hC hA =>
    if hr : route g P.cert P.target F.ledger e=.keep then
      .active ⟨advance F.ledger e,valid_step hn F.ledger x e F.valid,
        RootedFresh.quiet_step F.ledger.config e hp hc hn F.quiet,
        .owned (P.onKeep hn F.valid e hr)⟩ (P.onKeep hn F.valid e hr) rfl hC hA
    else .stop (actual (.inl F) e)

/-- The stopped and unstopped branches project to the same original fold. -/
theorem next_physical {p c n : Nat} {x : Config p c n} {g cert : List (Fin n)} {a : Fin n}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (s : Slot x g cert a) (e : Fin n) :
    (next hp hc hn s e).physical =
    joinedNext (WindowLatch.front hn (WindowOwnership.decide hp hc hn)) s.physical e := by
  cases s with
  | stop q => rfl
  | active F P hm hC hA =>
    by_cases H : route g P.cert P.target F.ledger e=.keep
    · simp [next,H,Slot.physical,joinedNext,WindowLatch.front,
        WindowOwnership.decide,hm]
      split <;> (rename_i heq; split at heq <;> simp_all <;> (have A := H.symm.trans (by assumption); contradiction))
    · simp [next,H,Slot.physical]

/-- Match only on the still-running ledger; after stopping the two clocks
agree on cost regardless of their disposable auxiliary state. -/
def Match {p c n : Nat} {x : Config p c n} {g cert : List (Fin n)} {a : Fin n}
    (s : Slot x g cert a) (q : WindowA0Push.State p c n) : Prop :=
  (s.done ↔ q.terminal=true) ∧
    (¬s.done → WindowLatch.project Front.ledger s.physical=q.cursor.ledger)

theorem match_step {p c n : Nat} {x : Config p c n} {g cert : List (Fin n)} {a v : Fin n}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (s : Slot x g cert a)
    (q : WindowA0Push.State p c n) (M : Match s q) (e : Fin n) :
    Match (next hp hc hn s e) (WindowA0Push.next v g cert a q e) := by
  cases s with
  | stop Q =>
    have H : q.terminal=true := M.1.mp trivial
    simp [Match,next,Slot.done,WindowA0Push.next,H]
  | active F P hm hC hA =>
    have hl : F.ledger=q.cursor.ledger := M.2 (by simp [Slot.done])
    have ht : q.terminal=false := by
      cases h : q.terminal
      · rfl
      · exact False.elim (M.1.mpr h)
    by_cases H : route g P.cert P.target F.ledger e=.keep
    · have T := H
      rw [hC,hA,hl] at T
      simp [Match,next,H,Slot.done,WindowA0Push.next,WindowFourHeadCut.tick,
        ht,T,Slot.physical,WindowLatch.project]
      exact congrArg (fun y => SevenTagCharge.advance y e) hl
    · have T := H
      rw [hC,hA,hl] at T
      simp [Match,next,H,Slot.done,WindowA0Push.next,ht,T]

/-- The two stopping rules have identical raw IID truncated costs. -/
theorem cost_eq {p c n : Nat} {x : Config p c n} {g cert : List (Fin n)} {a v : Fin n}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (s : Slot x g cert a)
    (q : WindowA0Push.State p c n) (M : Match s q) (t : Nat) :
    iidHitCost (next hp hc hn) Slot.done t s =
      iidHitCost (WindowA0Push.next v g cert a) (fun r => r.terminal=true) t q := by
  classical
  induction t generalizing s q with
  | zero => rfl
  | succ t ih =>
    by_cases h : s.done
    · rw [iidHitCost_of_target _ Slot.done _ h,
          iidHitCost_of_target _ (fun r : WindowA0Push.State p c n => r.terminal=true) _ (M.1.mp h)]
    · have h' : ¬q.terminal=true := fun T => h (M.1.mpr T)
      rw [iidHitCost,if_neg h,iidHitCost,if_neg h']
      congr 1
      apply congrArg TaggedTail.sumEdge
      funext e
      exact ih _ _ (match_step hp hc hn s q M e)

/-- Projection is exact on all words, including after latching the first exit. -/
theorem run_physical {p c n : Nat} {x : Config p c n} {g cert : List (Fin n)} {a : Fin n}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (s : Slot x g cert a) (w : List (Fin n)) :
    (runMarks (next hp hc hn) s w).physical =
      runMarks (joinedNext (WindowLatch.front hn (WindowOwnership.decide hp hc hn)))
        s.physical w := by
  induction w generalizing s with
  | nil => rfl
  | cons e w ih =>
    rw [runMarks,runMarks,ih,next_physical]

/-- The ordinary clock charges exactly the first non-keep, including the exit mark. -/
theorem active_done_iff {p c n : Nat} {x : Config p c n} {g : List (Fin n)} {a : Fin n}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (F : Front x g) (P : Progress F.ledger g) (hm : F.mode=.owned P)
    (ht : P.target=some a) (e : Fin n) :
    (next hp hc hn (Slot.active F P hm rfl ht) e).done ↔
      route g P.cert P.target F.ledger e ≠ .keep := by
  by_cases H : route g P.cert P.target F.ledger e=.keep <;>
    simp [next,Slot.done,H]

/-- Install either ordinary singleton/pair clock on the owned front.
Only initial cut geometry remains to be supplied by the roster construction. -/
theorem ordinary_mean {p c n : Nat} {x : Config p c n} {g : List (Fin n)}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (F : Front x g) (P : Progress F.ledger g) (hm : F.mode=.owned P)
    (v a b k : Fin n) (ht : P.target=some a)
    (ha : a∈g) (hb : b∈g) (hk : k∈g) (hab : a≠b)
    (q : WindowA0Push.State p c n) (hL : F.ledger=q.cursor.ledger)
    (hT : q.terminal=false) (H : WindowA0Push.ValidCut x v P.cert a b k q)
    (b₀ c₀ : Nat) (hi : q.cursor.index+1=b₀) (hw : q.cursor.width+1=b₀+c₀) :
    let m := min (n-2) (max 2 (q.donor+(2*b₀+c₀+1)))
    IIDExpectedHittingTimeAtMost (next hp hc hn) Slot.done (Slot.active F P hm rfl ht)
      (4*n*(2*(2*b₀+c₀+1)+m+1)) := by
  have M : Match (Slot.active F P hm rfl ht) q :=
    ⟨by simp [Slot.done,hT],fun _ => hL⟩
  have hQ : QuietEntrance q.cursor.ledger.config := hL ▸ F.quiet
  have B := WindowA0Push.push_mean hp hc hn v g P.cert a b k ha hb hk hab
    P.owned.contained q H hQ b₀ c₀ hi hw
  dsimp only
  intro t
  rw [cost_eq hp hc hn _ _ M]
  exact B t

#print axioms next_physical
#print axioms ordinary_mean

end L4.WindowOrdinarySlot
