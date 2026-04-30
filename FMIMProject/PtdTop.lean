module

public import Mathlib.Topology.Defs

class PointedTopologicalSpace (X : Type u) (x : X) where
  protected isTop : TopologicalSpace X
