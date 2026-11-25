import Leader.L4.BStarNativeNeedLift

namespace L4.BStarBiasedLift
open L4.Compiler.Native BStarNativeNeedLift

/-- The lower half is crossed once; after it the representation wraps
only in the upper half. The coordinate itself is still increasing. -/
def encode (P time : Nat) : Nat :=
  if time<P then time else liftResidue P time

theorem encode_initial (P time : Nat) (_pos : 0<P) (inRange : time<2*P) :
    encode P time=time := by
  by_cases H : time<P
  · exact if_pos H
  · rw [encode,if_neg H]
    unfold liftResidue
    have R := Nat.mod_eq_sub_mod (show P≤time by omega)
    rw [R,Nat.mod_eq_of_lt (show time-P<P by omega)]
    omega

theorem encode_succ (P time : Nat) (pos : 0<P) :
    successor (2*P) (encode P time)=encode P (time+1) := by
  by_cases H : time<P
  · rw [encode,if_pos H]
    have nowrap : time≠2*P-1 := by omega
    simp only [successor,if_neg nowrap]
    exact (encode_initial P _ pos (by omega)).symm
  · have H' : ¬time+1<P := by omega
    rw [encode,if_neg H,encode,if_neg H']
    exact successor_lift _ P time rfl pos

/-- When the half-modulus is a multiple of the phase period, the
literal phase agrees with the nonwrapping index at every natural time. -/
theorem encode_phase (P time q : Nat) (div : q∣P) :
    encode P time%q=time%q := by
  unfold encode
  split
  · rfl
  · unfold liftResidue
    rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd div,Nat.zero_add,Nat.mod_mod_of_dvd _ div,Nat.mod_mod]

/-- For the concrete packed width, the half-period is divisible by
32. The phase agreement is not just an abstract divisibility premise. -/
theorem concrete_half (r : Nat) (hr : 3≤r) :
    ∃ P, modulus r=2*P ∧ 0<P ∧ 32∣P := by
  let K := 16^(r-3)
  have pow : 0<K := Nat.pow_pos (by decide)
  have count : modulus r=4096*K := by
    change 16^r=4096*K
    calc
      16^r = 16^(3+(r-3)) := congrArg (fun a : Nat=>16^a) (by omega)
      _ = 4096*K := by rw [Nat.pow_add]
  refine ⟨2048*K,?_,by omega,⟨64*K,?_⟩⟩
  · rw [count]; omega
  · omega

/-- On a coherent lift band of width one across an edge, the
literal front tests uniquely distinguish level t and t+1,
including the upper half wrap. -/
theorem front_unwrapped (P t neighbor : Nat) (pos : 0<P) (phase : 32∣P)
    (lo : t≤neighbor+1) (hi : neighbor≤t+1)
    (seen : encode P neighbor=encode P t ∨
      encode P neighbor=successor (2*P) (encode P t)) :
    neighbor=t ∨ neighbor=t+1 := by
  have N := encode_phase P neighbor 32 phase
  have T := encode_phase P t 32 phase
  have S := encode_phase P (t+1) 32 phase
  rcases seen with same|next
  · have E := congrArg (fun j : Nat=>j%32) same
    rw [N,T] at E
    exact .inl (by omega)
  · rw [encode_succ P t pos] at next
    have E := congrArg (fun j : Nat=>j%32) next
    rw [N,S] at E
    exact .inr (by omega)

/-- Once an adjacent native port is at level t or t+1, its
current/prior choice is exactly the logical level-t observation. -/
theorem neighborView_lift (P t neighbor : Nat) (period : 32∣P)
    (y : NativeRecord) (tick : y.tick=encode P neighbor)
    (known : neighbor=t ∨ neighbor=t+1) :
    neighborView (encode P t) y=(if neighbor=t then y.curr else y.prior) := by
  unfold neighborView
  rcases known with E|E
  · simp [E,tick]
  · have different : y.tick≠encode P t := by
      intro same
      rw [tick,E] at same
      have modEq := congrArg (fun j : Nat=>j%32) same
      rw [encode_phase P (t+1) 32 period,encode_phase P t 32 period] at modEq
      omega
    rw [if_neg different,if_neg (by omega : neighbor≠t)]

theorem successor_mod (P tick : Nat) (pos : 0<P) :
    successor (2*P) tick%P=(tick+1)%P := by
  unfold successor
  by_cases top : tick=2*P-1
  · rw [if_pos top,show 2*P/2=P by omega,top,show 2*P-1+1=2*P by omega]
    simp
  · rw [if_neg top]

/-- At mixed-sign cuts use a residue-mod-P representation. This
local observation admits two different raw representatives at
nonadjacent sites on the same logical level. -/
theorem front_coset_view (P t u : Nat) (pos : 0<P) (phase : 32∣P)
    (old y : NativeRecord) (A : old.tick%P=t%P) (Y : y.tick%P=u%P)
    (lo : t≤u+1) (hi : u≤t+1)
    (front : y.tick=old.tick ∨ y.tick=successor (2*P) old.tick) :
    (u=t ∨ u=t+1) ∧ neighborView old.tick y=(if u=t then y.curr else y.prior) := by
  have ap : old.tick%32=t%32 := by
    have eq := congrArg (fun z : Nat=>z%32) A
    simpa only [Nat.mod_mod_of_dvd _ phase] using eq
  have yp : y.tick%32=u%32 := by
    have eq := congrArg (fun z : Nat=>z%32) Y
    simpa only [Nat.mod_mod_of_dvd _ phase] using eq
  rcases front with same|next
  · have eq := congrArg (fun z : Nat=>z%32) same
    rw [ap,yp] at eq
    have contemporaneous : u=t := by omega
    exact ⟨.inl contemporaneous,by simp [neighborView,same,contemporaneous]⟩
  · have nextMod := congrArg (fun z : Nat=>z%P) next
    rw [successor_mod P _ pos] at nextMod
    have m := congrArg (fun z : Nat=>z%32) nextMod
    simp only [Nat.mod_mod_of_dvd _ phase] at m
    have plus : (old.tick+1)%32=(t+1)%32 := by
      rw [Nat.add_mod old.tick,Nat.add_mod t,ap]
    rw [yp,plus] at m
    have U : u=t+1 := by omega
    have notSame : y.tick≠old.tick := by
      intro eq
      have E := congrArg (fun z : Nat=>z%32) eq
      rw [ap,yp] at E
      omega
    exact ⟨.inr U,by rw [neighborView,if_neg notSame,if_neg (by omega : u≠t)]⟩

end L4.BStarBiasedLift
