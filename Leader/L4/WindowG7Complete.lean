import Leader.L4.WindowMiddle
import Leader.L4.WindowHeadlineWiring

/-! The L4 ordinary and rooted headlines with every proof input
instantiated. Their statements are the original project's Props. -/
namespace L4

theorem row175_main_complete : row175Statement :=
  L4.mainTheorem WindowHeadlineWiring.restartTrial_nondivisible
    (LastTwoAssembly.concreteSevenGroups_of_marginals
      (WindowLocalAssembly.marginals_of_short_window
        (WindowHeadlineWiring.ordinary_short_window_of_rooted WindowMiddle.rooted_short_window)))
    AliasLiteralClock.pureAliasClock

theorem row175_rooted_complete : RootedAssembly.RootedStatement :=
  L4.row175_rooted (RootedRetirement.boundedRank_of_restartTrial G6Complete.restartTrial)
    (RootedWindows.marginals_of_short_window WindowMiddle.rooted_short_window)

end L4

#print axioms L4.WindowMiddle.rooted_short_window
#print axioms L4.row175_main_complete
#print axioms L4.row175_rooted_complete
