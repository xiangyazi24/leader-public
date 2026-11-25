import Leader.L4.ReportWriterPayload

namespace L4.ReportAcquireCaptureBits
open AllSizeProtocol ReportByteRows

/-- Centre captured selector is payload bit 4: the selector allocation
is 5,4,3; the independent header-A allocation is 2,1,0. -/
def captureCentre (t : Tok) : Nat := (t.payload/16)%2

private def edit (x j : Nat) (b : Bool) : Nat :=
  if (x >>> j)%2==1 then if b then x else x-2^j else if b then x+2^j else x

private theorem edit_centre (x : Nat) (b : Bool) :
    (edit x 4 b/16)%2=b.toNat := by
  cases b <;> simp [edit,Nat.shiftRight_eq_div_pow] <;> split <;> omega

private theorem edit_not_centre (x : Nat) (b : Bool) (j : Fin 7) (J : j≠4) :
    (edit x j.val b/16)%2=(x/16)%2 := by
  have C : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=5 ∨ j=6 := by
    refine ?_
    have := j.isLt
    apply Classical.byContradiction
    intro K
    simp only [not_or] at K
    have t (h : Fin 7) (e : j.val=h.val) : j=h := Fin.ext e
    have a := (fun H => K.1 (t 0 H))
    have c := (fun H => K.2.1 (t 1 H))
    have d := (fun H => K.2.2.1 (t 2 H))
    have e := (fun H => K.2.2.2.1 (t 3 H))
    have f := (fun H => J (t 4 H))
    have g := (fun H => K.2.2.2.2.1 (t 5 H))
    have k := (fun H => K.2.2.2.2.2 (t 6 H))
    simp only [Fin.val_zero,Fin.val_one] at *
    omega
  have A3 : ((3:Fin 7):Nat)=3 := by decide
  have A5 : ((5:Fin 7):Nat)=5 := by decide
  have A6 : ((6:Fin 7):Nat)=6 := by decide
  rcases C with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    simp [edit,A3,A5,A6,Nat.shiftRight_eq_div_pow] <;> split <;> omega

/-- Exact old-pair capture on the central winning ACQ incidence.
The report proof still must establish that this token and this win
belong to the same transaction that consumes its return. -/
theorem centre_acquire_bit (p : Params) (hv : Bool) (u v : BitVec p.w)
    (k : Option (Fin 3)) (t : Tok)
    (op : t.opcode=acqOp p) (live : t.fault=false) :
    captureCentre (effect p u v true hv 1 k true t).2.2 =
      publicationSelector p u := by
  rw [acquire_capture_old p hv u v 1 k true t op live]
  simp only [if_true]
  let a := (publicationSelector p u==1)
  let b := publicationA p u (publicationSelector p u)
  change (edit (edit t.payload 4 a) 1 b/16)%2=publicationSelector p u
  have Z := edit_not_centre (edit t.payload 4 a) b 1 (by decide)
  change edit (edit t.payload 4 a) 1 b/16%2=edit t.payload 4 a/16%2 at Z
  rw [Z,edit_centre]
  have L : publicationSelector p u<2 :=
    (u.extractLsb' (grantBase p+3) 1).isLt
  have Q : publicationSelector p u=0 ∨ publicationSelector p u=1 := by omega
  rcases Q with Q|Q <;> simp [a,Q]

/-- All other actual old-pair ACQ capture sites frame the centre
capture bit. A denied acquisition can only clear the sticky success bit
6; it must not be counted as a successful return. -/
theorem other_acquire_frames_centre (p : Params) (hv win : Bool)
    (u v : BitVec p.w) (j : Fin 3) (k : Option (Fin 3)) (t : Tok)
    (op : t.opcode=acqOp p) (live : t.fault=false)
    (other : j≠1 ∨ win=false) :
    captureCentre (effect p u v true hv j k win t).2.2=captureCentre t := by
  rw [acquire_capture_old p hv u v j k win t op live]
  cases win with
  | false =>
    change (edit t.payload 6 false/16)%2=(t.payload/16)%2
    have Z := edit_not_centre t.payload false ⟨6,by decide⟩ (by decide)
    exact Z
  | true =>
    let a := (publicationSelector p u==1)
    let b := publicationA p u (publicationSelector p u)
    have J : j≠1 := other.resolve_right (by decide)
    have U : j=0 ∨ j=2 := by
      have jlt := j.isLt
      by_cases L : j.val=0
      · exact .inl (Fin.ext L)
      · have F : j.val≠1 := fun E => J (Fin.ext E)
        exact .inr (Fin.ext (by change j.val=2; omega))
    rcases U with rfl|rfl
    · change (edit (edit t.payload 5 a) 2 b/16)%2=(t.payload/16)%2
      exact (edit_not_centre (edit t.payload 5 a) b ⟨2,by decide⟩ (by decide)).trans
        (edit_not_centre t.payload a ⟨5,by decide⟩ (by decide))
    · change (edit (edit t.payload 3 a) 0 b/16)%2=(t.payload/16)%2
      exact (edit_not_centre (edit t.payload 3 a) b ⟨0,by decide⟩ (by decide)).trans
        (edit_not_centre t.payload a ⟨3,by decide⟩ (by decide))

#print axioms other_acquire_frames_centre
#print axioms centre_acquire_bit
end L4.ReportAcquireCaptureBits
