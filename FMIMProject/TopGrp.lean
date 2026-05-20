module
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp_
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

public import FMIMProject.PtdTop

open CategoryTheory

@[simp]
lemma FundamentalGroup.mapOfEq_id (X: Type*) (x : X) [TopologicalSpace X] :
  (FundamentalGroup.mapOfEq (ContinuousMap.id X) rfl) =  MonoidHom.id (FundamentalGroup X x) := by
  ext y
  simp
  induction y using Quotient.ind with | _ =>
  sorry




noncomputable def fundamentalGroupFunctor : PtdTopCat ⥤ GrpCat where
  obj X := GrpCat.of (FundamentalGroup X X.point)
  -- obj X := GrpCat.of (Path.Homotopic.Quotient X.point X.point)
  map {X Y} f := by
    apply GrpCat.ofHom
    apply FundamentalGroup.mapOfEq
    exact f.presPoint


  map_comp _ _ := sorry
