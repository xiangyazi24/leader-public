import Leader.L4.TripleLongRestart
import Leader.L4.TripleOneEdge
import Leader.L4.RootedWindows

namespace L4.G6Complete

/-- Both literal physical boundary cases, for all moduli. -/
theorem boundary : TripleBoundary.MissingBoundary where
  oneEdge := TripleOneEdge.oneEdge
  long hn v z _ hSep hCert _ := TripleLongRestart.concrete_attempt hn v _ _ z hCert hSep

theorem restartTrial : RestartSerial.RootIndependentRestartTrial :=
  TripleBoundary.restartTrial_of_boundary boundary

theorem uniformEdge_rooted_of_short_window (h : RootedWindows.RootedShortWindowReward) :
    RootedAssembly.RootedStatement :=
  RootedWindows.uniformEdge_rooted_of_minimal_inputs boundary h

theorem uniformEdge_of_short_window (h : RootedWindows.RootedShortWindowReward) :
    uniformEdgeStatement :=
  RootedWindows.uniformEdgeStatement_of_minimal_rooted_inputs boundary h

end L4.G6Complete
