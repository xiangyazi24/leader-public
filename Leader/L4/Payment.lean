import Leader.L4.Protocol

namespace L4

/-- If the unmarked initiator meets a follower, only the stock fields may change. -/
theorem payment_stock_only {p c1 : Nat} (u v : Site p c1)
    (hu : u.mark = false) (hv : v.leader = false) :
    { (payment u v).1 with stock := u.stock } = u ∧
      { (payment u v).2 with stock := v.stock } = v := by
  cases u
  cases v
  simp_all [payment]
  split <;> simp_all

end L4
