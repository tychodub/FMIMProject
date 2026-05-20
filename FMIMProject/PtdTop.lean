module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Category.TopCat.Basic

@[expose] public section

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
  hom' : X.top⟶ Y.top
  presPoint : hom' (X.point) = Y.point

@[simps?]
public instance : Category PtdTopCat where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 X.top,rfl⟩
  comp f g := by
    refine ⟨f.hom' ≫ g.hom', ?_⟩
    simp
    rw [f.presPoint,g.presPoint]
