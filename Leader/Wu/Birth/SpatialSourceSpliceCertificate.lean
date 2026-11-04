import Leader.Wu.Birth.SpatialSourceSpliceMergedCompare
set_option autoImplicit false
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample


def rows : List (Row 32 S) := [row00, row01, row02, row03, row04, row05, row06, row07, row08, row09, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23, row24, row25, row26, row27, row28, row29, row30, row31, row32, row33, row34, row35, row36, row37, row38, row39, row40, row41, row42, row43, row44, row45, row46, row47, row48, row49, row50, row51, row52, row53, row54, row55, row56, row57, row58, row59]


theorem rows_valid : RowsValid ring T rows C00 := by
  exact ⟨row00_ok, ⟨row01_ok, ⟨row02_ok, ⟨row03_ok, ⟨row04_ok, ⟨row05_ok, ⟨row06_ok, ⟨row07_ok, ⟨row08_ok, ⟨row09_ok, ⟨row10_ok, ⟨row11_ok, ⟨row12_ok, ⟨row13_ok, ⟨row14_ok, ⟨row15_ok, ⟨row16_ok, ⟨row17_ok, ⟨row18_ok, ⟨row19_ok, ⟨row20_ok, ⟨row21_ok, ⟨row22_ok, ⟨row23_ok, ⟨row24_ok, ⟨row25_ok, ⟨row26_ok, ⟨row27_ok, ⟨row28_ok, ⟨row29_ok, ⟨row30_ok, ⟨row31_ok, ⟨row32_ok, ⟨row33_ok, ⟨row34_ok, ⟨row35_ok, ⟨row36_ok, ⟨row37_ok, ⟨row38_ok, ⟨row39_ok, ⟨row40_ok, ⟨row41_ok, ⟨row42_ok, ⟨row43_ok, ⟨row44_ok, ⟨row45_ok, ⟨row46_ok, ⟨row47_ok, ⟨row48_ok, ⟨row49_ok, ⟨row50_ok, ⟨row51_ok, ⟨row52_ok, ⟨row53_ok, ⟨row54_ok, ⟨row55_ok, ⟨row56_ok, ⟨row57_ok, ⟨row58_ok, ⟨row59_ok, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩


theorem rows_edges : rows.map Prod.fst = schedule := by decide


def certPrefix (t : Nat) : Vector S 32 := rowPrefix ring t rows C00


private theorem C00_get : C00.get = initial := by
  unfold C00
  funext i
  simp [Vector.get]
  apply congrArg initial
  apply Fin.ext
  rfl


theorem certPrefix_correct (t : Nat) :
    (certPrefix t).get = runPrefix t := by
  have h := rowPrefix_correct_valid ring T rows C00 rows_valid t
  rw [rows_edges] at h
  unfold BirthSpatialSourceSpliceCounterexample.runPrefix
  simpa [certPrefix, T, ring, C00_get] using h


#print axioms rows_valid
#print axioms certPrefix_correct
end BirthSpatialSourceSpliceCertificate
