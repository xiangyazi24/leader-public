import Leader.L4.ReportReaderSelectorLease
import Leader.L4.ReportJoinedBankFrame

namespace L4.ReportReaderWordLease
open AllSizeProtocol PhysicalCustody ReportResetRawHooks
open ReportByteRows ReportLeaseGrants ReportGenerationAncestry
open ReportReaderSelectorLease ReportJoinedBankFrame

variable {s n : Nat}

/-- The selected digits at the indicated nonheader use the logical
selector of its owning header, not the nonheader's raw selector field. -/
def selectedDigits (sheet : Sheet) (x : Raw s n) (hdr site : Fin n) :=
  reportDigitPair (params sheet s) (selectBytes sheet (x site)) (rawSelector sheet x hdr)

/-- The only extra obligation at each original old state, over and
above fixed layout and a compatible reader's no-release condition.
The case with a local enabled WRITE must be supplied by that WRITE's
own generated ancestry. It is not a premise about the new bytes. -/
def NonheaderWriterSafe (sheet : Sheet) (x : Raw s n) (hdr site e : Fin n) : Prop :=
  e=site → let p := params sheet s
  let u := selectBytes sheet (x site)
  let t := publicationToken p false u 1
  rankReady p false u 1=true → t.fault=false → writeOp p≤t.opcode →
    t.opcode<sealOp p → reportOldOffset p false u=t.opcode-writeOp p →
    ancestryWriteTarget p t≠rawSelector sheet x hdr

theorem reader_word_step (sheet : Sheet) (x : Raw s n)
    (hdr site e : Fin n) (N : 1<n) (j : Fin 3) (Side : j=0 ∨ j=2)
    (H : lower sheet (oldHeaders (rows s) (x hdr))=true)
    (S : lower sheet (oldHeaders (rows s) (x site))=false)
    (C : Compatible (rawGrant sheet x hdr))
    (Held : rawGrant sheet x hdr j=true)
    (R : e=hdr → (oldIncidence sheet x hdr).release j=false)
    (W : NonheaderWriterSafe sheet x hdr site e) :
    let y := rawNext s x e
    Compatible (rawGrant sheet y hdr) ∧ rawGrant sheet y hdr j=true ∧
      rawSelector sheet y hdr=rawSelector sheet x hdr ∧
      selectedDigits sheet y hdr site=selectedDigits sheet x hdr site := by
  dsimp only
  obtain ⟨C',Held',Sel⟩ := reader_grant_step sheet x e hdr N j Side H C Held R
  refine ⟨C',Held',Sel,?_⟩
  unfold selectedDigits
  rw [Sel]
  exact raw_all_mark_nonheader_bank_frame sheet x site e N (fun _=>rfl) S
    (rawSelector sheet x hdr) (ancestry_selector_lt _ _) W

/-- On this segment, the chosen side reader is not released and the
local writer, if enabled, writes the opposite bank. Each condition
is evaluated on the actual prefix state. -/
def SafeReadTape (sheet : Sheet) (hdr site : Fin n) (j : Fin 3) :
    Raw s n → List (Fin n) → Prop
  | _,[] => True
  | x,e::es => lower sheet (oldHeaders (rows s) (x hdr))=true ∧
      lower sheet (oldHeaders (rows s) (x site))=false ∧
      (e=hdr → (oldIncidence sheet x hdr).release j=false) ∧
      NonheaderWriterSafe sheet x hdr site e ∧
      SafeReadTape sheet hdr site j (rawNext s x e) es

theorem reader_word_run (sheet : Sheet) (x : Raw s n)
    (hdr site : Fin n) (N : 1<n) (j : Fin 3) (Side : j=0 ∨ j=2)
    (C : Compatible (rawGrant sheet x hdr))
    (Held : rawGrant sheet x hdr j=true) (w : List (Fin n))
    (OK : SafeReadTape sheet hdr site j x w) :
    let y := rawRun x w
    Compatible (rawGrant sheet y hdr) ∧ rawGrant sheet y hdr j=true ∧
      rawSelector sheet y hdr=rawSelector sheet x hdr ∧
      selectedDigits sheet y hdr site=selectedDigits sheet x hdr site := by
  induction w generalizing x with
  | nil => exact ⟨C,Held,rfl,rfl⟩
  | cons e w ih =>
    change lower sheet (oldHeaders (rows s) (x hdr))=true ∧
      lower sheet (oldHeaders (rows s) (x site))=false ∧
      (e=hdr → (oldIncidence sheet x hdr).release j=false) ∧
      NonheaderWriterSafe sheet x hdr site e ∧
      SafeReadTape sheet hdr site j (rawNext s x e) w at OK
    obtain ⟨C',H',S',D'⟩ :=
      reader_word_step sheet x hdr site e N j Side OK.1 OK.2.1 C Held OK.2.2.1 OK.2.2.2.1
    obtain ⟨C'',H'',S'',D''⟩ := ih _ C' H' OK.2.2.2.2
    exact ⟨C'',H'',S''.trans S',D''.trans D'⟩

end L4.ReportReaderWordLease
