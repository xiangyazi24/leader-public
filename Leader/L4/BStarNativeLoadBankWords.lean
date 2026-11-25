import Leader.L4.BStarAcquireBirthUnique
import Leader.L4.BStarNativeInputAssembly
import Leader.L4.BStarCanonicalAttemptBank
import Leader.L4.BStarCopyRightWrappedBank
import Leader.L4.BStarCopyLeftReleaseCapture

namespace L4.BStarNativeLoadBankWords
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork BStarLongPublication
open BStarOperandBank BStarOperandSites BStarCommitOperands BStarCaptureInterval
open BStarCopyRightStrip (addr addr_next)
open BStarNativeInputAssembly
open BStarGrantWriterHistory BStarGrantBirth
open L4.Compiler.Native L4.Compiler.Digits

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem packed_nibble (b : Fin 3) (x : BitVec LW) (f : Fin 9) :
    (packedNib ((bankPart b 9 36 (by decide)).read x) f).val=
      ((bankDigit b f).read x).toNat := by
  unfold packedNib
  change (BitVec.extractLsb' (4*(8-f.val)) 4 ((bankPart b 9 36 (by decide)).read x)).toNat=_
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have fj := f.isLt
  have h : 4*(8-f.val)+i<36 := by omega
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,h,decide_true,Bool.true_and,bankDigit,bankPart]
  rw [show bankBase b+9+(4*(8-f.val)+i)=bankBase b+(9+4*(8-f.val))+i by omega]

theorem addr_advance (base : Fin n) (seam j : Nat) :
    addr base (seam+j)=advance (addr base seam) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [show seam+(j+1)=seam+j+1 by omega,addr_next,ih]; rfl

theorem addr_site (base : Fin n) (j : Fin r) :
    addr base j.val=sites base j := by
  rw [show j.val=0+j.val by omega,addr_advance]
  have Z : addr base 0=base := Fin.ext (Nat.mod_eq_of_lt base.isLt)
  rw [Z]
  rfl

/-- The three transported LOAD tables, before changing time of the
bank snapshot, are exactly the same acquisition banks on the
canonical physical body map. Sole-header aliases are allowed. -/
theorem words (xL xC xR : X) (header : Fin 3→Fin n) (a : Fin n) (seam : Nat)
    (R : addr a seam=header 2) (f : Fin 9) :
    let left := BStarCopyLeftReleaseCapture.digitTable xL (header 0) (header 0)
    let right := BStarCopyRightReleaseCapture.digitTable xR (header 2) a seam
    let sel := readSel (xC (header 1)).long
    let center : Fin 9→Word r := fun g j=>
      ⟨((bankDigit sel g).read (xC (addr (header 1) j.val)).long).toNat,
        ((bankDigit sel g).read (xC (addr (header 1) j.val)).long).isLt⟩
    (val (inputWords left right center 0 f)=(bankAt (r:=r) xL header).digits 0 f) ∧
    (val (inputWords left right center 1 f)=(bankAt (r:=r) xC header).digits 1 f) ∧
    (val (inputWords left right center 2 f)=(bankAt (r:=r) xR header).digits 2 f) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  all_goals
    unfold bankAt
    apply congrArg val
    funext j
    apply Fin.ext
  · change (packedNib (BStarCopyLeftReleaseCapture.digitTable xL (header 0) (header 0) j.val) f).val=_
    rw [BStarCopyLeftReleaseCapture.digitTable,addr_site]
    exact packed_nibble _ _ _
  · change ((bankDigit (readSel (xC (header 1)).long) f).read (xC (addr (header 1) j.val)).long).toNat=_
    rw [addr_site]
    rfl
  · change (packedNib (BStarCopyRightReleaseCapture.digitTable xR (header 2) a seam j.val) f).val=_
    rw [BStarCopyRightReleaseCapture.digitTable,addr_advance,R]
    exact packed_nibble _ _ _

theorem replay_of_same_birth {x : X} (hp : 0<p)
    {cut w more : List (Fin n)} {i : Fin n} {j : Fin 3}
    (A : Acquisition hp
      (BStarResetSchedule.run (AllSizeS1Geometry.step (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x cut) [] w i j)
    {rA : List (Fin n)} {f : Fin n} {rs : List (Fin n)}
    (E : (cut++w)++more=rA++f::rs) (born : rA.length<(cut++w).length)
    (H : BStarGrantBirth.WonAt hp
      (BStarResetSchedule.run (AllSizeS1Geometry.step (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x rA) f i j)
    (C : Continuous hp
      (AllSizeS1Geometry.step (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)
        (BStarResetSchedule.run (AllSizeS1Geometry.step (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x rA) f) i j rs) :
    let play := BStarResetSchedule.run (AllSizeS1Geometry.step (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp))
    play (play x cut) A.lead=play x rA := by
  dsimp only
  let step := AllSizeS1Geometry.step (n:=n) (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)
  let play := BStarResetSchedule.run step
  have P : play x (cut++A.lead)=play (play x cut) A.lead :=
    BStarResetSchedule.run_append step x cut A.lead
  let lifted : Acquisition hp x [] (cut++w) i j :=
    ⟨cut++A.lead,A.mark,A.post,(congrArg (cut++·) A.exactTape).trans (List.append_assoc cut A.lead _).symm,Nat.zero_le _,
      by change WonAt hp (play x (cut++A.lead)) _ _ _; rw [P]; exact A.won,
      by change Continuous hp (step (play x (cut++A.lead)) _) _ _ _; rw [P]; exact A.live,
      fun L=>by change BeforePublication hp (step (play x (cut++A.lead)) _) _ _; rw [P]; exact A.writerBefore L⟩
  have eq := (BStarAcquireBirthUnique.same_birth_extended hp lifted E born H C).1
  change cut++A.lead=rA at eq
  exact P.symm.trans (congrArg (play x) eq)

theorem value_bound {i : Nat} (w : Word i) : val w<16^i := by
  have B (j : Nat) (h : j≤i) : valJ w j h<16^j := by
    induction j with
    | zero => simp [valJ]
    | succ j ih =>
      rw [valJ.eq_2]
      have b := (w ⟨j,by omega⟩).isLt
      have x := ih (by omega)
      have y := Nat.mul_le_mul_left (16^j) (show (w ⟨j,by omega⟩).val≤15 by omega)
      rw [Nat.pow_succ]
      rw [Nat.mul_comm (16^j) 16] at *
      omega
  exact B i (Nat.le_refl i)

end L4.BStarNativeLoadBankWords
