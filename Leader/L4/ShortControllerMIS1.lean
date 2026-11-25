import Leader.L4.ShortResetMIS1Ring
import Leader.L4.ShortControllerEntrance

namespace L4.ShortControllerMIS1
open AllSizeProtocol MISByteCodec ShortResetRow PhysicalCustody ShortControllerEntrance
open ShortResetMIS1Ring (header pairHeader pairIn)

private theorem rightWork {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) {k : Nat} (f : Field 96 k) (bound : f.offset+k≤93) :
    f.read (rawNext s x e (rightNeighbor e)).mis1 =
      f.read (((MISByteRows.row (pairHeader x e) (pairIn x e)).2).apply (pairIn x e).2) := by
  rw [show rawNext s x e (rightNeighbor e)=(largePair (rows s) (x e,x (rightNeighbor e))).2 by
    simp [rawNext,AllSizeS1Geometry.step,Ne.symm sep]]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ho : ¬ShortGeo.mis.owned (f.offset+i) := by
    intro E
    have le := E.1
    change 93≤f.offset+i at le
    omega
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  exact (ShortGeo.work_agrees_outside _ 3 (pairHeader x e) (pairIn x e)
    (BStarShort.shortMIS (pairHeader x e) (pairIn x e)) _ ho).2

/-- Fieldwise physical root-door adapter. The common routed base has the
old controller/file; the literal source patch then acts, with the optional
K0 write last. Geometry can change only the excluded upper cache. -/
theorem source_door_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x (rightNeighbor e)=true) :
    let old := (x (rightNeighbor e)).mis1
    let out := source old (oldK true old 0)
    ∃ base : BitVec 96,
      (∀ {k : Nat} (f : Field 96 k), 57≤f.offset → f.offset+k≤83 → f.read base=f.read old) ∧
      (∀ {k : Nat} (f : Field 96 k), f.offset+k≤93 →
        f.read (rawNext s x e (rightNeighbor e)).mis1 =
          f.read (match out.2 with
          | none => out.1.apply base
          | some t => (putK 0 t).apply (out.1.apply base))) := by
  dsimp only
  obtain ⟨base,hbase,h⟩ := source_door_pair (header x e) (x e).mis1 (x (rightNeighbor e)).mis1
  refine ⟨base,hbase,?_⟩
  intro k f B
  have w := rightWork x e sep f B
  simp only [pairHeader,pairIn,eligible] at w
  exact w.trans (congrArg f.read h)

private theorem assigned_k0_pc (t : Token) (b : BitVec 96) :
    pc ((putK 0 t).apply b)=pc b :=
  congrArg BitVec.toNat (Field.read_other_assign (lane 78 5 (by decide)) (kField 0)
    (encode t) b (.inr (by decide)))

/-- Physical WAIT exit from an arbitrary actual old root. Replacement of
K0 by E is literal, and every non-reset exit strictly lowers opcode debt. -/
theorem wait_exit_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x (rightNeighbor e)=true)
    (op : Nat)
    (hp : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (ho : get (x (rightNeighbor e)).mis1 78 3 (by decide)=op)
    (lt : op<7)
    (hf : (oldK true (x (rightNeighbor e)).mis1 0).tag≠1)
    (ht : (oldK true (x (rightNeighbor e)).mis1 0).tag≠2) :
    let y := (rawNext s x e (rightNeighbor e)).mis1
    (kField 0).read y=encode E ∧
      (pc y=8 ∨ op<6 ∧ pc y=8+(op+1) ∧ 6-(pc y-8)<6-op) := by
  dsimp only
  let old := (x (rightNeighbor e)).mis1
  let t := oldK true old 0
  let out := source old t
  obtain ⟨b,_,A⟩ := source_door_raw x e sep eligible
  have T : out.2=some E := by
    rcases wait_exit old t op hp ho lt hf ht with H|⟨_,H⟩
    · exact congrArg Prod.snd H
    · change (source old t).2=some E
      rw [H]
      split <;> rfl
  have K := A (kField 0) (by decide)
  have P := congrArg BitVec.toNat (A (lane 78 5 (by decide)) (by decide))
  change (kField 0).read _=(kField 0).read (match out.2 with
    | none => out.1.apply b
    | some t => (putK 0 t).apply (out.1.apply b)) at K
  change pc _=pc (match out.2 with
    | none => out.1.apply b
    | some t => (putK 0 t).apply (out.1.apply b)) at P
  rw [T] at K P
  simp only at K P
  rw [assigned_k0_pc] at P
  refine ⟨K.trans (ShortResetFlow.read_putK _ _ _),?_⟩
  rcases wait_exit_next_pc old b t op hp ho lt hf ht with H|⟨L,H⟩
  · exact Or.inl (P.trans H)
  · exact Or.inr ⟨L,P.trans H,by rw [P,H]; omega⟩

#print axioms source_door_raw
#print axioms wait_exit_raw

private theorem source_some_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x (rightNeighbor e)=true)
    (p : Patch 96) (t : Token)
    (out : source (x (rightNeighbor e)).mis1 (oldK true (x (rightNeighbor e)).mis1 0)=(p,some t)) :
    let old := (x (rightNeighbor e)).mis1
    let y := (rawNext s x e (rightNeighbor e)).mis1
    (kField 0).read y=encode t ∧
      ∃ b : BitVec 96, ∀ {k : Nat} (f : Field 96 k), 57≤f.offset → f.offset+k≤83 →
        f.read b=f.read old ∧ f.read y=f.read (p.apply b) := by
  dsimp only
  obtain ⟨b,B,F⟩ := source_door_raw x e sep eligible
  rw [out] at F
  refine ⟨(F (kField 0) (by decide)).trans (ShortResetFlow.read_putK _ _ _),b,?_⟩
  intro k f lo hi
  refine ⟨B f lo hi,(F f (by omega)).trans ?_⟩
  exact Field.read_other_assign f (kField 0) (encode t) _ (.inr (by change 57≤f.offset; exact lo))

private theorem reset_source_field {k : Nat} (f : Field 96 k) (lo : 57≤f.offset)
    (hi : f.offset+k≤83) (b : BitVec 96) :
    f.read (resetSource.apply b)= f.read (resetSource.apply 0) := by
  let a : Field 96 26 := lane 57 26 (by decide)
  let v : BitVec 26 := BitVec.ofNat 26 (2^24)
  apply BitVec.eq_of_getLsbD_eq
  intro i h
  have M := (a.inMask v (f.offset+i)).mpr (show 57≤f.offset+i ∧ f.offset+i<83 by omega)
  change (f.read ((a.assign v).apply b)).getLsbD i=(f.read ((a.assign v).apply 0)).getLsbD i
  simp only [Field.read,BitVec.getLsbD_extractLsb',h,decide_true,Bool.true_and]
  rw [Patch.write _ _ _ M,Patch.write _ _ _ M]

theorem invalid_resets_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x (rightNeighbor e)=true)
    (bad : let old := (x (rightNeighbor e)).mis1
      get old 81 2 (by decide)=0 ∨ get old 81 2 (by decide)=3 ∨ get old 78 3 (by decide)=7) :
    let y := (rawNext s x e (rightNeighbor e)).mis1
    pc y=8 ∧ (kField 0).read y=encode E := by
  obtain ⟨K,b,B⟩ := source_some_raw x e sep eligible resetSource E
    (invalid_controller_resets _ _ bad)
  refine ⟨?_,K⟩
  have P := (B (lane 78 5 (by decide)) (by decide) (by decide)).2.trans
      (reset_source_field _ (by decide) (by decide) b)
  exact (congrArg BitVec.toNat P).trans (by decide)

theorem issue_fresh_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x (rightNeighbor e)=true) (op : Nat)
    (hp : get (x (rightNeighbor e)).mis1 81 2 (by decide)=1)
    (ho : get (x (rightNeighbor e)).mis1 78 3 (by decide)=op) (lt : op<7) :
    let old := (x (rightNeighbor e)).mis1
    let y := (rawNext s x e (rightNeighbor e)).mis1
    get y 81 2 (by decide)=2 ∧ get y 78 3 (by decide)=op ∧
      (kField 0).read y = encode ({tag := 2, opcode := op, payload := if op=3 then 64 else if 4≤op then issuedDescriptor old else 0} : Token) := by
  dsimp only
  let f := lane 81 2 (by decide)
  let g := lane 78 3 (by decide)
  let p := if op=0 then resetSource else Patch.empty 96
  obtain ⟨K,b,B⟩ := source_some_raw x e sep eligible _ _
    (issue_fresh (x (rightNeighbor e)).mis1 _ op hp ho lt)
  have F := (B f (by decide) (by decide)).2
  have G := B g (by decide) (by decide)
  refine ⟨?_,?_,K⟩
  · change (f.read (rawNext s x e (rightNeighbor e)).mis1).toNat=2
    rw [F,Patch.compose_apply]
    exact congrArg BitVec.toNat (Field.read_assign f (2 : BitVec 2) (p.apply b))
  · change (g.read (rawNext s x e (rightNeighbor e)).mis1).toNat=op
    rw [G.2,Patch.compose_apply]
    rw [show put 81 2 (by decide) 2=f.assign (2 : BitVec 2) from rfl,
      Field.read_other_assign g f _ _ (.inl (by decide))]
    by_cases z : op=0
    · simp only [z,if_true]
      rw [reset_source_field g (by decide) (by decide)]
      decide
    · simp only [z,if_false]
      have M : (Patch.empty 96).apply b=b := by
        change b &&& BitVec.allOnes 96 ||| 0=b
        rw [BitVec.and_allOnes]
        exact BitVec.or_zero
      rw [M]
      exact (congrArg BitVec.toNat G.1).trans ho

#print axioms invalid_resets_raw
#print axioms issue_fresh_raw
end L4.ShortControllerMIS1
