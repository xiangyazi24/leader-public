import Leader.L4.ReportDigitArithmetic
import Leader.L4.ReportStaticSpacing

namespace L4.ReportDigitWord
open ReportDigitArithmetic ReportStaticSpacing
open ShortResetChart

def selectedFile {n : Nat} (p : ReportByteRows.Params)
    (a : Fin n → BitVec p.w) (i : Fin n) (minus : Bool) (j : Nat) : Nat :=
  selectedDigit p (ReportByteRows.publicationSelector p (a i)) minus (a (nextAt i j))

theorem selectedFile_lt {n : Nat} (p : ReportByteRows.Params)
    (a : Fin n → BitVec p.w) (i : Fin n) (minus : Bool) (j : Nat)
    (B : 2≤p.beta) : selectedFile p a i minus j < p.beta := by
  unfold selectedFile selectedDigit
  dsimp only
  exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (by omega)

theorem reportValue_lt {n : Nat} (p : ReportByteRows.Params)
    (a : Fin n → BitVec p.w) (i : Fin n) (minus : Bool)
    (B : 2≤p.beta) : reportValue p a i minus < p.beta^p.digits :=
  word_lt p.beta (selectedFile p a i minus) p.digits
    (fun j _ => selectedFile_lt p a i minus j B)

theorem radixDigit_reportValue {n : Nat} (p : ReportByteRows.Params)
    (a : Fin n → BitVec p.w) (i : Fin n) (minus : Bool) (j : Nat)
    (B : 2≤p.beta) (J : j<p.digits) :
    digit p.beta j (reportValue p a i minus) = selectedFile p a i minus j :=
  word_digit p.beta (selectedFile p a i minus) p.digits j J B
    (fun k _ => selectedFile_lt p a i minus k B)

end L4.ReportDigitWord
