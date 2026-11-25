import Leader.L4.BStarAcquireLatch
import Leader.L4.Compiler.BitField

/-! Interpret the arithmetic ACQUIRE lane setter as the same packed
field patch used by the accepted compiler, without expanding payloads. -/
namespace L4.BStarAcquireDigits
open BStarLongGrant BStarAcquireLatch Compiler.BitField BStarLongToken

private theorem splitLane (u v lo wi : Nat) :
    replaceLane u v lo wi =
      2^lo*(2^wi*(u/2^(lo+wi)) + v%2^wi) + u%2^lo := by
  unfold replaceLane
  rw [Nat.pow_add,Nat.mul_add]
  ac_rfl

theorem replace_low (u v lo wi : Nat) :
    replaceLane u v lo wi % 2^lo=u%2^lo := by
  rw [splitLane,Nat.mul_add_mod,Nat.mod_mod]

theorem replace_middle (u v lo wi : Nat) :
    extract (replaceLane u v lo wi) lo wi=v%2^wi := by
  unfold extract
  rw [Nat.shiftRight_eq_div_pow,splitLane,Nat.mul_add_div (Nat.two_pow_pos lo),
    Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos lo)),Nat.add_zero,
    Nat.mul_add_mod,Nat.mod_mod]

private theorem bit_from_div (x j i : Nat) :
    (x/2^j).testBit i=x.testBit (j+i) := by
  rw [← Nat.shiftRight_eq_div_pow,Nat.testBit_shiftRight]

theorem replace_patch (u v lo wi : Nat) :
    replaceLane u v lo wi=patch u lo wi v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_patch]
  by_cases L : i<lo
  · rw [if_neg (by omega)]
    have H := congrArg (fun z : Nat => z.testBit i) (replace_low u v lo wi)
    simpa only [Nat.testBit_mod_two_pow,L,decide_true,Bool.true_and] using H
  · by_cases H : i<lo+wi
    · rw [if_pos (by omega)]
      have E := congrArg (fun z : Nat => z.testBit (i-lo)) (replace_middle u v lo wi)
      have I : i-lo<wi := by omega
      have Y : lo+(i-lo)=i := by omega
      simpa only [testBit_extract,Nat.testBit_mod_two_pow,I,decide_true,Bool.true_and,Y] using E
    · rw [if_neg (by omega)]
      have D := congrArg (fun z : Nat => z.testBit (i-(lo+wi)))
        (replace_div_high u v lo wi (lo+wi) (by omega))
      have Y : lo+wi+(i-(lo+wi))=i := by omega
      simpa only [bit_from_div,Y] using D

theorem winning_patch (s : Fin 3) (h : BitVec 9) (j : Fin 3) (p : Payload) :
    (captureFields s h j p true).argument.toNat =
      patch (patch p.argument.toNat (31-2*j.val) 2 s.val) (18-9*j.val) 9 h.toNat := by
  change (BitVec.ofNat 34 (replaceLane (replaceLane p.argument.toNat s.val (31-2*j.val) 2)
    h.toNat (18-9*j.val) 9)).toNat=_
  rw [BitVec.toNat_ofNat,replace_patch,replace_patch]
  exact Nat.mod_eq_of_lt (patch_lt _ _ _ _ _ (patch_lt _ _ _ _ _ p.argument.isLt (by omega)) (by omega))

def selLo (j : Fin 3) : Nat := 31-2*j.val
def headLo (j : Fin 3) : Nat := 18-9*j.val

private theorem selectors_separate (i j : Fin 3) (H : i≠j) :
    selLo i+2≤selLo j ∨ selLo j+2≤selLo i := by
  have hg : i.val≠j.val := fun E => H (Fin.ext E)
  have := i.isLt
  have := j.isLt
  unfold selLo
  omega

private theorem headers_separate (i j : Fin 3) (H : i≠j) :
    headLo i+9≤headLo j ∨ headLo j+9≤headLo i := by
  have hg : i.val≠j.val := fun E => H (Fin.ext E)
  have := i.isLt
  have := j.isLt
  unfold headLo
  omega

private theorem fields_separate (i j : Fin 3) : headLo i+9≤selLo j := by
  have := j.isLt
  unfold selLo headLo
  omega

theorem winning_reads (s : Fin 3) (h : BitVec 9) (j : Fin 3) (p : Payload) :
    let n := (captureFields s h j p true).argument.toNat
    extract n (selLo j) 2=s.val ∧ extract n (headLo j) 9=h.toNat := by
  have S := s.isLt
  simp only [winning_patch]
  have A := fields_separate j j
  change extract (patch (patch p.argument.toNat (selLo j) 2 s.val) (headLo j) 9 h.toNat)
      (selLo j) 2=s.val ∧
    extract (patch (patch p.argument.toNat (selLo j) 2 s.val) (headLo j) 9 h.toNat)
      (headLo j) 9=h.toNat
  constructor
  · rw [extract_patch_disjoint _ _ _ _ _ _ (.inl A),extract_patch_same,
      Nat.mod_eq_of_lt (Nat.lt_trans S (by decide : 3<2^2))]
  · rw [extract_patch_same,Nat.mod_eq_of_lt h.isLt]

theorem winning_frames (s : Fin 3) (h : BitVec 9) (i j : Fin 3) (p : Payload) (H : j≠i) :
    let n := (captureFields s h j p true).argument.toNat
    extract n (selLo i) 2=extract p.argument.toNat (selLo i) 2 ∧
    extract n (headLo i) 9=extract p.argument.toNat (headLo i) 9 := by
  simp only [winning_patch]
  change extract (patch (patch p.argument.toNat (selLo j) 2 s.val) (headLo j) 9 h.toNat)
      (selLo i) 2=extract p.argument.toNat (selLo i) 2 ∧
    extract (patch (patch p.argument.toNat (selLo j) 2 s.val) (headLo j) 9 h.toNat)
      (headLo i) 9=extract p.argument.toNat (headLo i) 9
  constructor
  · rw [extract_patch_disjoint _ _ _ _ _ _ (.inl (fields_separate j i)),
      extract_patch_disjoint _ _ _ _ _ _ (selectors_separate j i H)]
  · rw [extract_patch_disjoint _ _ _ _ _ _ (headers_separate j i H),
      extract_patch_disjoint _ _ _ _ _ _ (.inr (fields_separate i j))]

def fieldsAt (p : Payload) (j : Fin 3) : Nat × Nat :=
  (extract p.argument.toNat (selLo j) 2,extract p.argument.toNat (headLo j) 9)

theorem fold_unvisited (vs : List Visit) (p : Payload) (j : Fin 3)
    (wins : vs.all Visit.wins=true) (none : ∀ v∈vs,v.incidence≠j) :
    fieldsAt (vs.foldl (fun q v => v.apply q) p) j=fieldsAt p j := by
  induction vs generalizing p with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.all_cons,Bool.and_eq_true_iff] at wins
    rw [List.foldl_cons,ih _ wins.2 (fun a ha => none a (List.mem_cons_of_mem _ ha))]
    unfold Visit.apply
    rw [wins.1]
    exact Prod.ext (winning_frames v.selector v.headers j v.incidence p (none v List.mem_cons_self)).1
      (winning_frames v.selector v.headers j v.incidence p (none v List.mem_cons_self)).2

/-- At a successful visit, the sampled fields replace the previous values.
Every subsequent different successful visit leaves both fields unchanged. -/
theorem fold_last_visit (before after : List Visit) (p : Payload) (v : Visit)
    (win : v.wins=true) (wins : after.all Visit.wins=true)
    (last : ∀ w∈after,w.incidence≠v.incidence) :
    fieldsAt ((before++v::after).foldl (fun q w => w.apply q) p) v.incidence =
      (v.selector.val,v.headers.toNat) := by
  rw [List.foldl_append,List.foldl_cons,fold_unvisited after _ _ wins last]
  unfold Visit.apply
  rw [win]
  exact Prod.ext (winning_reads v.selector v.headers v.incidence _).1
    (winning_reads v.selector v.headers v.incidence _).2

private theorem mod_extract (u off w k : Nat) (H : off+w≤k) :
    extract (u%2^k) off w=extract u off w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [testBit_extract,Nat.testBit_mod_two_pow]
  by_cases I : i<w
  · have J : off+i<k := by omega
    simp [I,J]
  · simp [I]

theorem fields_strip_latch (q : Payload) (j : Fin 3) :
    fieldsAt {q with argument:=BitVec.ofNat 34 (q.argument.toNat%2^33)} j=fieldsAt q j := by
  have L : q.argument.toNat%2^33 < 2^33 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have B : q.argument.toNat%2^33 < 2^34 := Nat.lt_trans L (by decide)
  unfold fieldsAt
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt B]
  rw [mod_extract _ _ _ _ (by unfold selLo; omega),
      mod_extract _ _ _ _ (by unfold headLo; omega)]

/-- Payload readout at the literal successful terminal. The hypotheses
are visits of the same tagged command, not bare equality of token bytes. -/
theorem finish_last_visit (before after : List Visit) (p : Payload) (v : Visit)
    (hf : p.fault=0) (ho : p.opcode.toNat=BStarLongCommand.acquire)
    (hl : latch p=true) (winsBefore : before.all Visit.wins=true) (win : v.wins=true)
    (winsAfter : after.all Visit.wins=true)
    (last : ∀ w∈after,w.incidence≠v.incidence) :
    let q := (before++v::after).foldl (fun q w => w.apply q) p
    let out := {q with race:=0,argument:=BitVec.ofNat 34 (q.argument.toNat%2^33)}
    BStarLongCommand.finish q=.reply out ∧
      fieldsAt out v.incidence=(v.selector.val,v.headers.toNat) := by
  dsimp only
  constructor
  · rw [finish_itinerary _ _ hf ho]
    simp [List.all_append,winsBefore,win,winsAfter,hl]
  · change fieldsAt {((before++v::after).foldl (fun q w => w.apply q) p) with
      race:=0,argument:=BitVec.ofNat 34
        (((before++v::after).foldl (fun q w => w.apply q) p).argument.toNat%2^33)} v.incidence=_
    let q := (before++v::after).foldl (fun q w => w.apply q) p
    have E : fieldsAt {q with race:=0,argument:=BitVec.ofNat 34 (q.argument.toNat%2^33)}
        v.incidence=fieldsAt {q with argument:=BitVec.ofNat 34 (q.argument.toNat%2^33)}
        v.incidence := rfl
    exact E.trans ((fields_strip_latch q _).trans (fold_last_visit before after p v win winsAfter last))

end L4.BStarAcquireDigits
