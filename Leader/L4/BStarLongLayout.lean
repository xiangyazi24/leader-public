import Leader.L4.BStarTrace

/-! Long-sheet static layout. Addresses are in the numerical
(low-bit-first) convention. Reads accept every byte. Assignments lower
to a field patch and never canonicalize an adjacent held leaf. -/
namespace L4.BStarLongLayout
open AllSizeProtocol BStarTrace

def kBase (j : Fin 11) : Nat := 1192+52*(10-j.val)
def kField (j : Fin 11) : Field LW 52 := ⟨kBase j,by simp [kBase,production_long_width]; omega⟩
def kPart (j : Fin 11) (lo width : Nat) (h : lo+width≤52) : Field LW width :=
  ⟨kBase j+lo,by simp [kBase,production_long_width] at *; omega⟩
def kTag (j : Fin 11) := kPart j 50 2 (by decide)
def kFault (j : Fin 11) := kPart j 49 1 (by decide)
def kOp (j : Fin 11) := kPart j 40 9 (by decide)
def kRace (j : Fin 11) := kPart j 37 3 (by decide)
def kOutcome (j : Fin 11) := kPart j 35 2 (by decide)
def kApplied (j : Fin 11) := kPart j 34 1 (by decide)
def kPayload (j : Fin 11) := kPart j 0 34 (by decide)

def laneBase (l : Fin 4) : Nat := 728+116*(3-l.val)
def lanePart (l : Fin 4) (lo width : Nat) (h : lo+width≤116) : Field LW width :=
  ⟨laneBase l+lo,by simp [laneBase,production_long_width] at *; omega⟩
def laneGate (l : Fin 4) := lanePart l 115 1 (by decide)
def laneError (l : Fin 4) := lanePart l 114 1 (by decide)
def laneMobile (l : Fin 4) := lanePart l 76 38 (by decide)
def laneFrozen (l : Fin 4) := lanePart l 38 38 (by decide)
def laneRetained (l : Fin 4) := lanePart l 0 38 (by decide)

def bankBase (b : Fin 3) : Nat := 2222+45*(2-b.val)
def bankPart (b : Fin 3) (lo width : Nat) (h : lo+width≤45) : Field LW width :=
  ⟨bankBase b+lo,by simp [bankBase,production_long_width] at *; omega⟩
def bankDigit (b : Fin 3) (i : Fin 9) : Field LW 4 :=
  bankPart b (9+4*(8-i.val)) 4 (by omega)
def bankHeader (b : Fin 3) (i : Fin 9) : Field LW 1 :=
  bankPart b (8-i.val) 1 (by omega)

def choice : Field LW 2 := ⟨2133,by decide⟩
def delta : Field LW 1 := ⟨2135,by decide⟩
def need : Field LW 1 := ⟨2136,by decide⟩
def candidateHeader (δ : Fin 2) (i : Fin 9) : Field LW 1 :=
  ⟨2137+9*(1-δ.val)+(8-i.val),by rw [production_long_width]; omega⟩
def sourceDescriptor : Field LW 7 := ⟨2155,by decide⟩
def capturedHeader (which : Fin 3) (i : Fin 9) : Field LW 1 :=
  ⟨2162+9*(2-which.val)+(8-i.val),by rw [production_long_width]; omega⟩
def capturedSelector (which : Fin 3) : Field LW 2 :=
  ⟨2189+2*(2-which.val),by rw [production_long_width]; omega⟩
def sealField : Field LW 8 := ⟨2206,by decide⟩
def stage : Field LW 8 := ⟨2214,by decide⟩
def selector : Field LW 2 := ⟨2360,by decide⟩
def grant (i : Fin 3) : Field LW 1 := ⟨2359-i.val,by rw [production_long_width]; omega⟩

/-- Indices are ranks within the fixed list of WORD-producing nodes,
not opcode numbers or scratch register contents. -/
def wordDigit (i : Fin 182) : Field LW 4 := ⟨4*(181-i.val),by rw [production_long_width]; omega⟩

def Disjoint {a b : Nat} (f : Field LW a) (g : Field LW b) : Prop :=
  f.offset+a≤g.offset ∨ g.offset+b≤f.offset

theorem kPart_spacing (i j : Fin 11) (h : i≠j) (a wa b wb : Nat)
    (A : a+wa≤52) (B : b+wb≤52) :
    Disjoint (kPart i a wa A) (kPart j b wb B) := by
  have H : i.val≠j.val := fun e => h (Fin.ext e)
  simp only [Disjoint,kPart,kBase]
  omega

theorem lanePart_spacing (i j : Fin 4) (h : i≠j) (a wa b wb : Nat)
    (A : a+wa≤116) (B : b+wb≤116) :
    Disjoint (lanePart i a wa A) (lanePart j b wb B) := by
  have H : i.val≠j.val := fun e => h (Fin.ext e)
  simp only [Disjoint,lanePart,laneBase]
  omega

theorem bankPart_spacing (i j : Fin 3) (h : i≠j) (a wa b wb : Nat)
    (A : a+wa≤45) (B : b+wb≤45) :
    Disjoint (bankPart i a wa A) (bankPart j b wb B) := by
  have H : i.val≠j.val := fun e => h (Fin.ext e)
  simp only [Disjoint,bankPart,bankBase]
  omega

theorem bank_digit_header (i j : Fin 3) (a b : Fin 9) :
    Disjoint (bankDigit i a) (bankHeader j b) := by
  by_cases h : i=j
  · subst j
    simp only [Disjoint,bankDigit,bankHeader,bankPart]
    omega
  · exact bankPart_spacing i j h _ _ _ _ _ _

theorem digit_before_lane (i : Fin 182) (j : Fin 4) (a w : Nat) (h : a+w≤116) :
    (wordDigit i).offset+4 ≤ (lanePart j a w h).offset := by
  simp only [wordDigit,lanePart,laneBase]
  omega

theorem lane_before_k (i : Fin 4) (j : Fin 11) (a w : Nat) (h : a+w≤116) :
    (lanePart i a w h).offset+w ≤ (kField j).offset := by
  simp only [lanePart,laneBase,kField,kBase]
  omega

theorem k_before_file (j : Fin 11) :
    (kField j).offset+52 ≤ (LongDoorGuard.fileField manifest).offset := by
  change 1192+52*(10-j.val)+52≤1764
  omega

theorem k0_layout : kField 0 = LongDoorGuard.k0Field manifest := rfl
theorem source_boundaries :
    (LongDoorGuard.fileField manifest).offset=1764 ∧
    (LongDoorGuard.opcodeField manifest).offset=2195 ∧
    (LongDoorGuard.phaseField manifest).offset=2204 := by decide

/-- The register field chosen by a trace can be overwritten idempotently;
the other bank's decoded leaf still sees its original raw bits. -/
theorem digit_write_holds_header (x : BitVec LW) (i j : Fin 3) (a b : Fin 9)
    (v : BitVec 4) :
    (bankHeader j b).read (((bankDigit i a).assign v).apply x) =
      (bankHeader j b).read x :=
  Field.read_other_assign _ _ _ _ ((bank_digit_header i j a b).elim Or.inr Or.inl)

#print axioms kPart_spacing
#print axioms lanePart_spacing
#print axioms bankPart_spacing
#print axioms bank_digit_header
#print axioms digit_before_lane
#print axioms lane_before_k
#print axioms k_before_file
#print axioms k0_layout
#print axioms source_boundaries
#print axioms digit_write_holds_header
end L4.BStarLongLayout
