import Leader.L4.WindowMiddle
import Leader.L4.WindowHeadlineWiring

/-! The L4 ordinary and rooted headlines with every proof input
instantiated. Their statements are the original project's Props. -/
namespace L4

theorem uniformEdge_main_complete : uniformEdgeStatement :=
  L4.mainTheorem WindowHeadlineWiring.restartTrial_nondivisible
    (LastTwoAssembly.concreteSevenGroups_of_marginals
      (WindowLocalAssembly.marginals_of_short_window
        (WindowHeadlineWiring.ordinary_short_window_of_rooted WindowMiddle.rooted_short_window)))
    AliasLiteralClock.pureAliasClock

theorem uniformEdge_rooted_complete : RootedAssembly.RootedStatement :=
  L4.uniformEdge_rooted (RootedRetirement.boundedRank_of_restartTrial G6Complete.restartTrial)
    (RootedWindows.marginals_of_short_window WindowMiddle.rooted_short_window)

end L4

