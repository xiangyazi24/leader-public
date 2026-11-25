import Leader.L4.Height.Window
import Leader.L4.BStarRecoveredHistory
import Leader.L4.BStarClearanceOffsetMask
import Leader.L4.Height.ServiceCustody
import Leader.L4.BStarParkedSteering

/-! Production geometry, the physical next-letter operation under steering,
and the source provenance available at every stopped history. -/
namespace L4.Height.ProductionCustody

open AllSizeProtocol PhysicalCustody BStarTrace BStarH6WordChart BStarAcquireAnchors
open BStarAcquireLiteralChain BStarGrantWriterHistory BStarGeneratedOwner BStarResetChartTouch
open BStarSteeredLikelihood
open Classical

noncomputable section

structure Production {s n : Nat} {x : Raw s n} (g : CustodyWitness x) : Prop where
  advice : s = ell (ell n)
  large : 6 ≤ s
  room : 3 * 1024 * radWidth s < n
  owners : 4 ≤ total (oldH6 (rows s) g.base)

structure ProductionAfterCut {s n : Nat} (x : Raw s n) : Prop where
  witness : ∃ g : CustodyWitness x, Production g

def width {s n : Nat} {x : Raw s n} (g : CustodyWitness x) : Nat :=
  (List.ofFn (fun e : Fin n =>
    if oldH6 (rows s) g.base (rightNeighbor e) then BStarH6Ordinal.oldOrdinal (rows s) g.base g.hh e + 1
    else 0)).foldl max 0

abbrev longBudget : Nat := 2^32

/-- The success predicate counts the event on the outgoing physical bond. -/
def ProductionBlock : Prop :=
  ∀ {s n} {x : Raw s n} (g : CustodyWitness x), Production g →
  ∀ i : Header (oldH6 (rows s) g.base),
    let h := 2 * (2^20 * n * width g)
    n^h ≤ 2^(5*longBudget+1) *
      wordSum (fun w => if RawServiceCore.publishes x i.val w then 1 else 0) h

theorem radius_pos {s n : Nat} {x : Raw s n} {g : CustodyWitness x} (p : Production g) :
    0 < radWidth s := by
  have z : 2^1 ≤ 2^s := Nat.pow_le_pow_right (by decide) (show 1 ≤ s from Nat.le_trans (by decide) p.large)
  unfold radWidth
  omega

theorem separation {s n : Nat} {x : Raw s n} {g : CustodyWitness x} (p : Production g) :
    ∀ e : Fin n, e ≠ rightNeighbor e := by
  have h := p.room
  have r := radius_pos p
  intro e same
  have hv := congrArg Fin.val same
  change e.val = (e.val + 1) % n at hv
  by_cases small : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt small] at hv
    omega
  · have bound := e.isLt
    rw [show e.val + 1 = n by omega, Nat.mod_self] at hv
    omega

def extend {s n : Nat} {x : Raw s n} (g : CustodyWitness x) (w : List (Fin n)) :
    CustodyWitness (rawRun x w) :=
  { g with past := g.past ++ w
           here := by
             rw [← List.append_assoc]
             exact (BStarResetSchedule.run_append (rawNext s) _ _ _).trans
               (congrArg (fun y => rawRun y w) g.here) }

theorem production_extend {s n : Nat} {x : Raw s n} {g : CustodyWitness x} (P : Production g)
    (w : List (Fin n)) : Production (extend g w) :=
  ⟨P.advice,P.large,P.room,P.owners⟩

theorem keep {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (y : Raw s n) (w : List (Fin n)) (qy : g.Q y) : g.Q (rawRun y w) := by
  induction w generalizing y with
  | nil => exact qy
  | cons e w ih => exact ih _ (g.closed y e qy)

def Ready {s n : Nat} {x : Raw s n} (g : CustodyWitness x) (y : Raw s n) : Prop :=
  g.Q y ∧ BStarClearanceOffset.correct (oldH6 (rows s) g.base) g.hh 5 y

theorem ready_next {s n : Nat} {x : Raw s n} {g : CustodyWitness x} (p : Production g)
    {y : Raw s n} (hy : Ready g y) (e : Fin n) : Ready g (rawNext s y e) := by
  refine ⟨g.closed y e hy.1, ?_⟩
  exact BStarClearanceOffset.stable (show 0 < 2 by decide) _ g.hh y e (separation p e)
    (fun j => (congrArg Prod.fst (g.fiber y hy.1 j)).symm)
    (BStarClearanceOffsetMask.leftFrame (show 0 < 2 by decide) y e) hy.2

theorem ready_run {s n : Nat} {x : Raw s n} {g : CustodyWitness x} (p : Production g)
    (w : List (Fin n)) : Ready g (rawRun x w) := by
  have iter (y : Raw s n) (v : List (Fin n)) (q : Ready g y) : Ready g (rawRun y v) := by
    induction v generalizing y with
    | nil => exact q
    | cons e v ih => exact ih _ (ready_next p q e)
  have q := iter g.initial ((g.u++g.v)++g.past) ⟨g.init,g.offset⟩
  rw [g.here] at q
  exact iter x w q

/-- The physical state, both tapes, and the strict publication latch are
updated by one raw candidate. The fixed query policy is a parameter to next. -/
structure History (s n : Nat) where
  physical : Raw s n
  candidates : List (Fin n)
  emitted : List (Fin n)
  published : Prop

def start {s n : Nat} (x : Raw s n) : History s n := ⟨x,[],[],False⟩

def next {s n : Nat} (choose : Word n → Fin n → Fin n) (i : Fin n)
    (y : History s n) (e : Fin n) : History s n :=
  let f := choose y.emitted e
  ⟨rawNext s y.physical f,y.candidates ++ [e],y.emitted ++ [f],
    y.published ∨ (f = i ∧ ¬ NoPublication (show 0 < 2 by decide) y.physical i i)⟩

def Consistent {s n : Nat} (x : Raw s n) (choose : Word n → Fin n → Fin n) (i : Fin n)
    (y : History s n) : Prop :=
  y.emitted = emit choose [] y.candidates ∧ y.physical = rawRun x y.emitted ∧
  (y.published ↔ RawServiceCore.publishes x i y.emitted)

theorem emit_append {n : Nat} (c : Word n → Fin n → Fin n) (a u v : Word n) :
    emit c a (u ++ v) = emit c a u ++ emit c (a ++ emit c a u) v := by
  induction u generalizing a with
  | nil => simp [emit]
  | cons e u ih => simp only [List.cons_append, emit, ih, List.append_assoc, List.nil_append, List.cons_append]

theorem emit_shifted {n : Nat} (c : Word n → Fin n → Fin n) (pre a w : Word n) :
    emit (fun b => c (pre++b)) a w = emit c (pre++a) w := by
  induction w generalizing a with
  | nil => rfl
  | cons e w ih => simp only [emit, ih, List.append_assoc]

theorem consistent_next {s n : Nat} (x : Raw s n) (choose : Word n → Fin n → Fin n) (i : Fin n)
    (y : History s n) (h : Consistent x choose i y) (e : Fin n) :
    Consistent x choose i (next choose i y e) := by
  obtain ⟨tape,here,pub⟩ := h
  refine ⟨?_,?_,?_⟩
  · change y.emitted ++ [choose y.emitted e] = emit choose [] (y.candidates ++ [e])
    rw [emit_append]
    simp only [List.nil_append, emit, ← tape]
  · change rawNext s y.physical _ = rawRun x (y.emitted ++ [_])
    exact here ▸ (BStarResetSchedule.run_append (rawNext s) x y.emitted [choose y.emitted e]).symm
  · change (_ ∨ _) ↔ RawServiceCore.publishes x i (y.emitted++[choose y.emitted e])
    rw [RawServiceCore.publishes_append_one, ← here, ← pub]
    
theorem consistent_start {s n : Nat} (x : Raw s n) (choose : Word n → Fin n → Fin n) (i : Fin n) :
    Consistent x choose i (start x) := by
  refine ⟨rfl,rfl,?_⟩
  change False ↔ _
  constructor
  · exact False.elim
  · exact RawServiceCore.publishes_nil x i

theorem run_consistent {s n : Nat} (x : Raw s n) (c : Word n → Fin n → Fin n) (i : Fin n)
    (y : History s n) (hy : Consistent x c i y) (w : Word n) :
    Consistent x c i (runWord (next c i) y w) := by
  induction w generalizing y with
  | nil => exact hy
  | cons e v ih => exact ih _ (consistent_next x c i y hy e)

private theorem run_candidates {s n : Nat} (c : Word n → Fin n → Fin n) (i : Fin n)
    (y : History s n) (w : Word n) :
    (runWord (next c i) y w).candidates=y.candidates++w := by
  induction w generalizing y with
  | nil => simp [runWord]
  | cons e w ih =>
    change (runWord (next c i) (next c i y e) w).candidates=_
    rw [ih]
    simp [next,List.append_assoc]

theorem run_publication {s n : Nat} (x : Raw s n) (c : Word n → Fin n → Fin n) (i : Fin n)
    (w : Word n) : (runWord (next c i) (start x) w).published ↔
      RawServiceCore.publishes x i (emit c [] w) := by
  obtain ⟨tape,_,hit⟩ := run_consistent x c i _ (consistent_start x c i) w
  have trace : (runWord (next c i) (start x) w).emitted=emit c [] w := by
    rw [run_candidates] at tape
    exact (show (runWord (next c i) (start x) w).emitted=emit c [] ([]++w) from tape)
  rw [trace] at hit
  exact hit

theorem keep_publication {s n : Nat} (c : Word n → Fin n → Fin n) (i : Fin n)
    (y : History s n) (e : Fin n) (h : y.published) : (next c i y e).published := Or.inl h

/-- Every owner has its own authenticated PC3 origin on the common cut tape.
The suffix from that origin includes all the marks emitted after the query. -/
theorem generated_at_every_history {s n : Nat} {x : Raw s n} {g : CustodyWitness x} (p : Production g)
    (o : Owners (oldH6 (rows s) g.base)) (emitted : Word n) :
    ∃ pre segment tail S len fall,
      g.u ++ g.v = pre ++ segment ++ tail ∧
      BStarOwnerRecoveryPass.Recovered (show 0<2 by decide) g.base g.hh o (rawRun g.initial pre) segment ∧
      Chart (show 0 < 2 by decide) g.base g.hh o S len fall ∧
      let root := (S.getD 0 fall).1
      let z := rawRun (rawRun g.initial pre) segment
      (BStarLongDoor.ctrlOp.read (z root).long).toNat = 3 ∧
      ∃ m, GeneratedOwner (show 0 < 2 by decide) g.base (fun j => S.getD j fall) len
        z .idle (tail ++ (g.past ++ emitted)) m ∧
        Current (show 0 < 2 by decide) g.base (fun j => S.getD j fall) len (rawRun x emitted) m := by
  obtain ⟨a,own,_⟩ := BStarAcquireAnchors.unique_command_header _ g.hh o.val o.property.1 o.property.2 0
  obtain ⟨o',_,_,ow',_,_,credit⟩ := g.cuts.recovery g.hh a.val 0
  have eqo : o'=o := Subtype.ext (ow'.symm.trans own)
  subst o'
  obtain ⟨pre,segment,tail,W,_,_,rec⟩ := credit
  obtain ⟨S,len,fall,C,pc,_,m,G,_,cur⟩ := BStarRecoveredHistory.recovered_suffix
    (show 0 < 2 by decide) rec (separation p) g.Q (keep g _ pre g.init) g.fiber g.closed
    (tail ++ (g.past ++ emitted))
  refine ⟨pre,segment,tail,S,len,fall,W,rec,C,pc,m,G,?_⟩
  have here : rawRun (rawRun g.initial pre) (segment ++ (tail ++ (g.past ++ emitted))) = rawRun x emitted := by
    calc
      _ = rawRun g.initial (pre ++ (segment ++ (tail ++ (g.past ++ emitted)))) :=
        (BStarResetSchedule.run_append (rawNext s) _ _ _).symm
      _ = rawRun g.initial (((g.u ++ g.v) ++ g.past) ++ emitted) := by
        simp only [W,List.append_assoc]
      _ = _ := (BStarResetSchedule.run_append (rawNext s) _ _ _).trans
        (congrArg (fun a => rawRun a emitted) g.here)
  exact here ▸ cur

end
end L4.Height.ProductionCustody

