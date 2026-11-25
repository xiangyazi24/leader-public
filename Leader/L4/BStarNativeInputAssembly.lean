import Leader.L4.BStarNativeLoadTours
import Leader.L4.BStarLongPackets

namespace L4.BStarNativeInputAssembly
open L4.Compiler.Digits

def packedNib (z : BitVec 36) (f : Fin 9) : Fin 16 :=
  ⟨(z.extractLsb' (4*(8-f.val)) 4).toNat,(z.extractLsb' (4*(8-f.val)) 4).isLt⟩

def inputWords {r : Nat} (left right : Nat→BitVec 36) (center : Fin 9→Word r)
    (q : Fin 3) (f : Fin 9) : Word r :=
  fun j => if q=0 then packedNib (left j.val) f else
    if q=1 then center f j else packedNib (right j.val) f

end L4.BStarNativeInputAssembly
