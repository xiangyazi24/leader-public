import Leader.L4.NativeHeightObservation
import Leader.L4.Compiler.GeneratedEdit

namespace L4.NativeHeightRange
open Compiler.Native NativeHeightObservation

/-- The ordinary decoder is idempotent on exactly these decoded records. -/
def RecordInRange (r : Nat) (y : NativeRecord) : Prop :=
  y.tick<modulus r ∧ (y.err=true → y.tick<modulus r/2) ∧
    SnapshotInRange r y.prior ∧ SnapshotInRange r y.curr

private theorem positive (r : Nat) : 0<modulus r := by
  unfold modulus
  exact Nat.pow_pos (by decide)

private theorem half_positive (r : Nat) (hr : 3≤r) : 0<modulus r/2 := by
  have h : 16^1≤modulus r :=
    Nat.pow_le_pow_right (by decide) (show 1≤r by omega)
  omega

private theorem empty_range (r : Nat) : SnapshotInRange r {} :=
  ⟨edit_positive r,edit_positive r,positive r,edit_positive r⟩

/-- Input banks need no raw well-formedness hypotheses: decode clips the
clock and all numeric fields to their designated ranges. -/
theorem decode_range (r : Nat) (hr : 3≤r) (bank : Bank) (j : Fin 3) :
    RecordInRange r (decodeBank r bank j) := by
  have M := positive r
  have H := edit_positive r
  have P := half_positive r hr
  refine ⟨?_,?_,⟨Nat.mod_lt _ H,Nat.mod_lt _ H,Nat.mod_lt _ M,Nat.mod_lt _ H⟩,
    ⟨Nat.mod_lt _ H,Nat.mod_lt _ H,Nat.mod_lt _ M,Nat.mod_lt _ H⟩⟩
  · change (if bank.hdr j 0 && decide (modulus r/2≤bank.digits j 0%modulus r) then 0
          else bank.digits j 0%modulus r)<modulus r
    split
    · exact M
    · exact Nat.mod_lt _ M
  · intro err
    change bank.hdr j 0=true at err
    change (if bank.hdr j 0 && decide (modulus r/2≤bank.digits j 0%modulus r) then 0
          else bank.digits j 0%modulus r)<modulus r/2
    simp only [err,Bool.true_and,decide_eq_true_eq]
    split <;> omega

/-- Phase 1 keeps its counter in the full-width word and its distance
below the height modulus. All other updates preserve the stronger
height bounds on height and proposal. -/
theorem phase_range (r phase : Nat) (hr : 3≤r) (L C R : Snapshot) (δ : Bool)
    (h : SnapshotInRange r C) : SnapshotInRange r (phaseUpdate (heightMod r) phase L C R δ) := by
  obtain ⟨hx,hd,hz,hp⟩ := h
  have factor := edit_modulus_factor r hr
  have H : 1<heightMod r := by
    change 1<16^(r-2)
    have V := Nat.pow_le_pow_right (n:=16) (by decide : 0<16)
      (show 1≤r-2 by omega)
    omega
  have z' : 8*C.d+8<modulus r := by omega
  rcases phase with _|_|_|_|_|_|phase
  · exact ⟨hx,hd,hz,hp⟩
  · refine ⟨hx,?_,?_,hp⟩
    · change (if R.anchor then 1 else min (heightMod r-1) (R.d+1))<heightMod r
      split <;> omega
    · change (if !C.anchor then 0 else if C.z=0 then 8*C.d+8
        else min (8*C.d+8) (C.z-1))<modulus r
      split
      · exact positive r
      · split <;> omega
  · exact ⟨hx,hd,hz,hp⟩
  · exact ⟨hx,hd,hz,Nat.mod_lt _ (edit_positive r)⟩
  · exact ⟨hx,hd,hz,hp⟩
  · refine ⟨?_,hd,hz,hp⟩
    change (if C.approve && R.approve then C.proposal else C.x)<heightMod r
    split <;> assumption
  · exact ⟨hx,hd,hz,hp⟩

private theorem successor_bound {m t : Nat} (M : 0<m) (T : t<m) :
    successor m t<m := by
  unfold successor
  split <;> omega

private theorem proposals_low (m : Nat) (L C R : NativeRecord) :
    let p := m/2
    let proposal := fun y : NativeRecord =>
      if y.err && decide (y.tick+1<p) && decide (y.tick+1<C.tick) then y.tick+1 else C.tick
    let v := min (proposal L) (proposal R)
    v<C.tick → v<p := by
  dsimp only
  intro H
  have one (y : NativeRecord) :
      let n := if y.err && decide (y.tick+1<m/2) && decide (y.tick+1<C.tick)
        then y.tick+1 else C.tick
      n<C.tick → n<m/2 := by
    dsimp only
    split
    · rename_i G
      exact fun _ => of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp G).1).2
    · intro notSelf
      omega
  by_cases O : (if L.err && decide (L.tick+1<m/2) && decide (L.tick+1<C.tick)
        then L.tick+1 else C.tick)≤(if R.err && decide (R.tick+1<m/2) && decide (R.tick+1<C.tick)
        then R.tick+1 else C.tick)
  · rw [Nat.min_eq_left O] at H ⊢
    exact one L H
  · rw [Nat.min_eq_right (Nat.le_of_not_ge O)] at H ⊢
    exact one R H

/-- Every result of the native row, including RESET, PROPAGATE and HOLD,
already lies in the image of the incident decoder. -/
theorem finish_range (r : Nat) (hr : 3≤r) (L C R : NativeRecord) (δ : Bool)
    (h : RecordInRange r C) :
    RecordInRange r (finishNative (heightMod r) L C R (nativeClock (modulus r) L C R) δ) := by
  let m := modulus r
  let t := C.tick
  let p := m/2
  let lowerErr := fun y : NativeRecord => y.err && decide (y.tick<t)
  let gap := fun y : NativeRecord => decide (t+2≤y.tick) &&
    !(decide (t=p) && decide (y.tick=m-1))
  let root := if C.err then !(lowerErr L || lowerErr R) else gap L || gap R
  let proposal := fun y : NativeRecord =>
    if y.err && decide (y.tick+1<p) && decide (y.tick+1<t) then y.tick+1 else t
  let least := min (proposal L) (proposal R)
  let near := fun y : NativeRecord => decide (y.tick≤t+1) && decide (t≤y.tick+1) &&
    (decide (y.tick≤t) || !y.err)
  let succ := successor m t
  let front := fun y : NativeRecord => decide (y.tick=t) || decide (y.tick=succ)
  let reset := root && !(C.err && decide (t=0))
  let clear := C.err && near L && near R
  let inc := !C.err && front L && front R
  change RecordInRange r (finishNative (heightMod r) L C R
    (if reset then .reset else if least<t then .propagate least
     else if clear then .clear else if inc then .inc succ else .hold) δ)
  by_cases z : reset = true
  · rw [if_pos z]
    exact ⟨positive r,fun _ => half_positive r hr,empty_range r,empty_range r⟩
  rw [if_neg z]
  by_cases y : least<t
  · rw [if_pos y]
    have lo := proposals_low m L C R y
    exact ⟨Nat.lt_of_lt_of_le lo (Nat.div_le_self _ _),fun _ => lo,empty_range r,empty_range r⟩
  rw [if_neg y]
  by_cases a : clear=true
  · rw [if_pos a]
    exact ⟨h.1,by simp [finishNative],empty_range r,empty_range r⟩
  rw [if_neg a]
  by_cases b : inc=true
  · rw [if_pos b]
    exact ⟨successor_bound (positive r) h.1,by simp [finishNative],h.2.2.2,
      phase_range r _ hr _ _ _ δ h.2.2.2⟩
  rw [if_neg b]
  exact h

theorem native_range (r : Nat) (hr : 3≤r) (bank : Bank) (δ : Bool) :
    RecordInRange r (observe ((nativeSpec r bank).2 δ)) := by
  simpa only [nativeSpec,observe_encode] using
    finish_range r hr (decodeBank r bank 0) (decodeBank r bank 1) (decodeBank r bank 2) δ
      (decode_range r hr bank 1)

theorem native_exposure_roundtrip (r : Nat) (hr : 3≤r) (input output : Bank)
    (δ : Bool) (j : Fin 3)
    (digits : output.digits j=((nativeSpec r input).2 δ).digits)
    (hdr : output.hdr j=((nativeSpec r input).2 δ).hdr) :
    decodeBank r output j=observe ((nativeSpec r input).2 δ) := by
  have Y : encodeOutput (observe ((nativeSpec r input).2 δ))=(nativeSpec r input).2 δ := by
    simp only [nativeSpec,observe_encode]
  obtain ⟨h1,h2,h3,h4⟩ := native_range r hr input δ
  exact exposure_roundtrip r _ output j (Y.symm ▸ digits) (Y.symm ▸ hdr) h1 h2 h3 h4

#print axioms native_exposure_roundtrip
end L4.NativeHeightRange
