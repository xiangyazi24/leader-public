/-!
# A small record of characteristic-two field laws (R-TAPS)

The proof that primitive binary polynomials exist at every degree (main.tex rem:primitive-taps) runs in two finite fields: the quotient of `F_2[X]` by an irreducible mask, and the same
field seen through a generator.  This record is the interface between the abstract lemmas (root bound,
Fermat, generator) and the bit-mask quotient, which instantiates it in `PrimitiveMaskQuotient`.
It carries data and laws only.  There is no hidden field: every instance is constructed.
-/

namespace L3.TapField

set_option autoImplicit false

/-- Characteristic-two field laws on a carrier `F`.
Consumers: `PrimitiveAbstractField`, `PrimitiveFieldGenerator`, `PrimitiveMaskQuotient`. -/
structure BinaryField (F : Type) where
  zero : F
  one : F
  add : F → F → F
  mul : F → F → F
  inv : F → F
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  add_self : ∀ a, add a a = zero
  mul_comm : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  one_ne_zero : one ≠ zero
  mul_inv : ∀ a, a ≠ zero → mul a (inv a) = one

/-- A duplicate-free list of all elements of `F`.  Consumer: `binaryFiniteFieldFermat`. -/
structure Enumeration (F : Type) where
  elems : List F
  nodup : elems.Nodup
  complete : ∀ a, a ∈ elems

end L3.TapField
