module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Category.TopCat.Basic

open CategoryTheory Topology

class PointedTopologicalSpace (X : Type u) (x : X) where
  protected isTop : TopologicalSpace X

public structure PtdTopCat where
  off ::
  top : TopCat.{u}
  point : top

public instance : CoeSort (PtdTopCat) (Type u) :=
  ⟨fun x ↦ PtdTopCat.top x⟩


public structure Hom (X Y : PtdTopCat) where
  hom' : C(X, Y)
  presPoint : hom' (X.point) = Y.point

public instance : Category PtdTopCat where
  Hom X Y := Hom X Y
  id X := ⟨ContinuousMap.id X,rfl⟩
  comp f g := by
    refine ⟨g.hom'.comp f.hom', ?_⟩
    simp
    rw [f.presPoint,g.presPoint]
