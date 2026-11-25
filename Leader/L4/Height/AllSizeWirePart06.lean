import Leader.L4.Height.AllSizeWirePart05
set_option Elab.async false

namespace L4.Height.AllSizeWire
open AllSizeSpine L4.Compiler.Native Classical

section PackedClock

open Classical
open PhysicalCustody
open AllSizeProtocol BStarH6WordChart BStarAcquireAnchors BStarCycleGeometry
open BStarGrantWriterHistory (NoPublication)

variable {s n : Nat}

/-- Physical positions of the fixed headers of a completed custody epoch. -/
noncomputable abbrev headers {x : Raw s n} (g : CustodyWitness x) : Nat :=
  total (oldH6 (rows s) g.base)

/-- The starting raw state and the certificate of its original custody epoch. -/
abbrev Epoch (s n : Nat) := (x : Raw s n) × CustodyWitness x

/-- The suffix executed after custody, together with the latest publication. -/
abbrev TapeState {x : Raw s n} (g : CustodyWitness x) :=
  List (Fin n) × Option (Fin (headers g))

/-- Appending raw marks changes the current state and preserves the same
permanent layout, custody witnesses and original prefix. -/
noncomputable def extendWitness {x : Raw s n} (g : CustodyWitness x)
    (w : List (Fin n)) : CustodyWitness (rawRun x w) := by
  refine
    { base := g.base
      initial := g.initial
      u := g.u
      v := g.v
      past := g.past ++ w
      Q := g.Q
      init := g.init
      closed := g.closed
      fiber := g.fiber
      here := ?_
      hh := g.hh
      offset := g.offset
      baseOffset := g.baseOffset
      flags := g.flags
      notShort := g.notShort
      heads := g.heads
      cont := g.cont
      packed := g.packed
      upperWidth := g.upperWidth
      widthRatio := g.widthRatio
      charts := g.charts
      cuts := g.cuts
      coherent := g.coherent }
  change rawRun g.initial ((g.u ++ g.v) ++ (g.past ++ w)) = rawRun x w
  rw [← List.append_assoc]
  change BStarResetSchedule.run (rawNext s) g.initial (((g.u ++ g.v) ++ g.past) ++ w) =
    rawRun x w
  rw [BStarResetSchedule.run_append]
  exact congrArg (fun y => rawRun y w) g.here

/-- One more letter of the original epoch executes one literal physical mark. -/
theorem custody_rawRun_snoc (x : Raw s n) (w : List (Fin n)) (e : Fin n) :
    rawRun x (w ++ [e]) = rawNext s (rawRun x w) e := by
  unfold rawRun
  rw [BStarResetSchedule.run_append] <;> rfl

/-- The exact initiator-side publication relation on the packed row. -/
def packedPublication (s : Nat) {n : Nat} (x : Raw s n) (e i : Fin n) : Prop :=
  ¬ NoPublication (show 0 < 2 by decide) x e i

/-- The map from native clock indices to physical initiators. -/
noncomputable def packedHeader (j : Epoch s n) (i : Fin (headers j.2)) : Fin n :=
  (atIndex j.2.hh i).val

theorem exists_chartMark {x : Raw s n} (g : CustodyWitness x)
    (hn : 4 ≤ n) (hs : 6 ≤ s) (w : List (Fin n)) (e : Fin n) :
    ∃ a : Option (Fin (headers g) × Bool),
      (literalClockCfg g.hh (rawRun x (w ++ [e])) =
        match a with
        | none => literalClockCfg g.hh (rawRun x w)
        | some a => Recover.StageThree.activate (heightMod (radWidth s))
            (modulus (radWidth s)) (total_pos (oldH6 (rows s) g.base) g.hh)
            (literalClockCfg g.hh (rawRun x w)) a.1 a.2) ∧
      ∀ i, (∃ b, a = some (i,b)) ↔
        e = (atIndex g.hh i).val ∧ packedPublication s (rawRun x w) e e := by
  let old := rawRun x w
  let prior := rawRun g.initial ((g.u ++ g.v) ++ (g.past ++ w))
  let hp : 0 < 2 := by decide
  have hwhere : prior = old := (extendWitness g w).here
  have one :
      (NoPublication hp prior e e ∧
        literalClockCfg g.hh (rawNext s prior e) = literalClockCfg g.hh prior) ∨
      (¬ NoPublication hp prior e e ∧
        ∃ (i : Fin (headers g)) (bit : Bool), (atIndex g.hh i).val = e ∧
          literalClockCfg g.hh (rawNext s prior e) =
            Recover.StageThree.activate (heightMod (radWidth s)) (modulus (radWidth s))
              (total_pos (oldH6 (rows s) g.base) g.hh) (literalClockCfg g.hh prior) i bit) :=
    indexed_literal_mark_logical hp g.u g.v (g.past ++ w) g.cuts g.hh (pair_distinct hn)
      g.Q g.init g.fiber g.closed e (packed_radius_large hs) g.flags g.notShort
  rw [hwhere] at one
  rw [custody_rawRun_snoc]
  rcases one with ⟨quiet, cfg⟩ | ⟨pub, i, b, loc, cfg⟩
  · refine ⟨none, cfg, fun _ => ?_⟩
    constructor
    · rintro ⟨_, h⟩
      cases h
    · rintro ⟨_, h⟩
      exact (h quiet).elim
  · refine ⟨some (i,b), cfg, fun j => ?_⟩
    constructor
    · rintro ⟨c, hc⟩
      have hij : i = j := congrArg Prod.fst (Option.some.inj hc)
      exact ⟨loc.symm.trans (congrArg (fun k => (atIndex g.hh k).val) hij), pub⟩
    · rintro ⟨hj, _⟩
      have hij : i = j := BStarLogicalConjugacy.physical_injective g.hh (loc.trans hj)
      exact ⟨b, by rw [hij]⟩

/-- Choose the native action witnessed by each mark of the physical tape. -/
noncomputable def chooseMark {x : Raw s n} (g : CustodyWitness x)
    (hn : 4 ≤ n) (hs : 6 ≤ s) (w : List (Fin n)) (e : Fin n) :
    Option (Fin (headers g) × Bool) :=
  Classical.choose (exists_chartMark g hn hs w e)

/-- At a mark, the chosen action exists at exactly the publishing header. -/
theorem chooseMark_matches {x : Raw s n} (g : CustodyWitness x)
    (hn : 4 ≤ n) (hs : 6 ≤ s) (w : List (Fin n)) (e : Fin n) (i : Fin (headers g)) :
    (∃ b, chooseMark g hn hs w e = some (i,b)) ↔
      e = (atIndex g.hh i).val ∧ packedPublication s (rawRun x w) e e :=
  (Classical.choose_spec (exists_chartMark g hn hs w e)).2 i

/-- The clock chart follows every raw mark on the same physical suffix.
Only the latest genuine publication is recorded. -/
noncomputable def chartClock {x : Raw s n} (g : CustodyWitness x)
    (hn : 4 ≤ n) (hs : 6 ≤ s) :
    Recover.Chain.ClockChain (TapeState g) n (headers g) (heightMod (radWidth s))
      (modulus (radWidth s)) (total_pos (oldH6 (rows s) g.base) g.hh) where
  next z e := (z.1 ++ [e], (chooseMark g hn hs z.1 e).map Prod.fst)
  cfg z := literalClockCfg g.hh (rawRun x z.1)
  act z e := chooseMark g hn hs z.1 e
  lastAct := Prod.snd
  cfg_next z e := by
    have h :
        literalClockCfg g.hh (rawRun x (z.1 ++ [e])) =
          match chooseMark g hn hs z.1 e with
          | none => literalClockCfg g.hh (rawRun x z.1)
          | some a => Recover.StageThree.activate (heightMod (radWidth s))
              (modulus (radWidth s)) (total_pos (oldH6 (rows s) g.base) g.hh)
              (literalClockCfg g.hh (rawRun x z.1)) a.1 a.2 :=
      (Classical.choose_spec (exists_chartMark g hn hs z.1 e)).1
    cases hAct : chooseMark g hn hs z.1 e with
    | none => simpa only [hAct] using h
    | some a =>
      rcases a with ⟨i,b⟩
      simpa only [hAct] using h
  last_next _ _ := rfl

/-- The chart run accumulates exactly the raw input word. -/
theorem chart_state_tape {x : Raw s n} (g : CustodyWitness x)
    (hn : 4 ≤ n) (hs : 6 ≤ s) (z : TapeState g) (w : List (Fin n)) :
    (runWord (chartClock g hn hs).next z w).1 = z.1 ++ w := by
  induction w generalizing z with
  | nil => simp [runWord]
  | cons e w ih =>
    change (runWord (chartClock g hn hs).next ((chartClock g hn hs).next z e) w).1 =
      z.1 ++ e :: w
    rw [ih]
    change (z.1 ++ [e]) ++ w = z.1 ++ e :: w
    rw [List.append_assoc] <;> rfl

/-- Install the fixed-layout raw clock on the production packed pair rule.
Display trial levels are provided by the separately selected display trial. -/
noncomputable def packedData (s n : Nat) (hn : 4 ≤ n) (hs : 6 ≤ s) :
    AllSizeData (PackedSite s) n where
  row := largePair (rows s)
  leader := packedOutput s
  reference := packedRead s
  cust := Custody
  marked := PublicSpec.Marked
  Chart := Epoch s n
  State j := TapeState j.2
  m j := headers j.2
  hm j := total_pos (oldH6 (rows s) j.2.base) j.2.hh
  r := radWidth s
  width j := ClockServiceSpec.maxWordWidth j.2
  clock j := chartClock j.2 hn hs
  raw j z := rawRun j.1 z.1
  opening _ _ := 0
  level _ _ _ _ := 0

/-- The padded population-protocol step is the literal physical packed step. -/
theorem packed_next (hn : 4 ≤ n) (hs : 6 ≤ s) :
    (packedData s n hn hs).next (by omega) = rawNext s := by
  rfl

/-- Each chart step projects to the same raw production step. -/
theorem packed_rawStep (hn : 4 ≤ n) (hs : 6 ≤ s) :
    let D := packedData s n hn hs
    ∀ j z e, D.raw j ((D.clock j).next z e) = D.next (by omega) (D.raw j z) e := by
  dsimp only
  intro j z e
  change rawRun j.1 (z.1 ++ [e]) = rawNext s (rawRun j.1 z.1) e
  exact custody_rawRun_snoc (s := s) j.1 z.1 e

/-- A raw custody cut embeds into its history chart before the first
post-cut mark, with well-formed selected records. -/
theorem packed_liftCustody (hn : 4 ≤ n) (hs : 6 ≤ s) :
    let D := packedData s n hn hs
    2^32 < n → ∀ x, D.cust x → ∃ j z, D.raw j z = x ∧
      Recover.StageTwo.WellFormed (modulus D.r) ((D.clock j).cfg z) := by
  dsimp only
  intro _ x hx
  change Custody (s := s) x at hx
  obtain ⟨g⟩ := hx
  have hr : 1 ≤ radWidth s := Nat.le_trans (by decide) (packed_radius_large hs)
  exact ⟨(⟨x,g⟩ : Epoch s n), ([], none), rfl,
    literalClockCfg_wellFormed (r := radWidth s) hr g.hh x⟩

end PackedClock

end L4.Height.AllSizeWire
