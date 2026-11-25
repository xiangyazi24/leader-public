import Leader.L4.G6Complete
import Leader.L4.WindowFiveStages

namespace L4.WindowHeadlineWiring

theorem restartTrial_nondivisible : RankPhysical.ConcreteRestartTrial := by
  intro c hc
  obtain ⟨A,hA,H⟩ := G6Complete.restartTrial c hc
  exact ⟨A,hA,fun x hp hn _ hq hr => H x hp hn hq hr⟩

theorem ordinary_short_window_of_rooted (h : RootedWindows.RootedShortWindowReward) :
    WindowLocalAssembly.ConcreteShortWindowReward := by
  intro c hc
  obtain ⟨B,hB,H⟩ := h c hc
  exact ⟨B,hB,fun x hp hn _ hq hr i hs => H x hp hn hq hr i hs⟩

/-- Invoke the original L4.mainTheorem with literal G6 and G8 and
the G7-produced marginals. Remove this one remaining input only once
the concrete five-stage observer has been proved. -/
theorem main_instantiated_except_g7 (g7 : RootedWindows.RootedShortWindowReward) :
    uniformEdgeStatement :=
  L4.mainTheorem restartTrial_nondivisible
    (LastTwoAssembly.concreteSevenGroups_of_marginals
      (WindowLocalAssembly.marginals_of_short_window (ordinary_short_window_of_rooted g7)))
    AliasLiteralClock.pureAliasClock

/-- Invoke the original L4.uniformEdge_rooted; its two premise
positions are explicit here, and only the latter uses G7. -/
theorem rooted_instantiated_except_g7 (g7 : RootedWindows.RootedShortWindowReward) :
    RootedAssembly.RootedStatement :=
  L4.uniformEdge_rooted (RootedRetirement.boundedRank_of_restartTrial G6Complete.restartTrial)
    (RootedWindows.marginals_of_short_window g7)

end L4.WindowHeadlineWiring
