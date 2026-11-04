import Leader.L3.Base

/-!
# Token fields of the base step

The request and grant fields written by `baseStep` are exactly the two
token outputs of `tokenStep`, evaluated at the OLD records, the post-E
native values (replaced by `firedNative` at a FIRE site), the FIRE
selection, the DCC request bit and the BANK/SMALL success bit.  This is
the fieldwise bridge from the local token row to the real step.
-/

namespace L3

set_option autoImplicit false

/-- The BANK/SMALL success bit that `baseStep` passes to `tokenStep`. -/
def baseBankSuccessBit (c : Compiled) (x y : Agent c) : Bool :=
  if c.useSmall then (smallPair x y c.K).2.2
  else bankSuccess (bankCell x x.pack.val) (bankCell y y.pack.val)
    (packNext x.pack.val y.pack.val c.b) c.b

/-- The token outputs that `baseStep` copies into its two records. -/
def baseTokenOutputs (c : Compiled) (ev : CertEvent) (x y : Agent c) :
    TokPair × TokPair × TokMeta :=
  tokenStep x y
    (if fireAtSite (fireSelect x y (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) .siteX then firedNative
      else (certLiteralEPair x.certNative y.certNative).1)
    (if fireAtSite (fireSelect x y (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) .siteY then firedNative
      else (certLiteralEPair x.certNative y.certNative).2)
    (fireSelect x y (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2)
    (dccStep x y ev).request
    (baseBankSuccessBit c x y)

/-- Fieldwise token frame of the real base step. -/
theorem baseStep_token_fields (c : Compiled) (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).1.req = (baseTokenOutputs c ev x y).1.req ∧
    (baseStep c ev x y).1.grant = (baseTokenOutputs c ev x y).1.grant ∧
    (baseStep c ev x y).2.req = (baseTokenOutputs c ev x y).2.1.req ∧
    (baseStep c ev x y).2.grant = (baseTokenOutputs c ev x y).2.1.grant := by
  unfold baseStep baseTokenOutputs baseBankSuccessBit
  cases c.useSmall <;> exact ⟨rfl, rfl, rfl, rfl⟩

end L3
