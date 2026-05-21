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
lemma FundamentalGroup.map_id (X: Type*) (x : X) [TopologicalSpace X] :
  (FundamentalGroup.map (ContinuousMap.id X) x ) =  MonoidHom.id (FundamentalGroup X x) := by
  ext y
  induction y using Quotient.inductionOn with | h a =>
  rfl

@[simp]
lemma FundamentalGroup.map_comp (X Y Z : Type*) (x : X) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : C(X,Y) ) (f : C(Y,Z)) :
  FundamentalGroup.map (f.comp g ) x = (FundamentalGroup.map f (g x)).comp (FundamentalGroup.map g x) := by
  ext y
  induction y using Quotient.inductionOn with | h a =>
  rfl

@[simp]
lemma FundamentalGroup.mapofEq_rfl (X Y: Type*) (x : X) [TopologicalSpace X] [TopologicalSpace Y] (f : C(X,Y)):
  FundamentalGroup.mapOfEq f rfl = FundamentalGroup.map f x := by
  unfold FundamentalGroup.mapOfEq
  ext y
  simp


@[simp]
lemma FundamentalGroup.mapOfEq_id (X: Type*) (x : X) [TopologicalSpace X] :
  (FundamentalGroup.mapOfEq (ContinuousMap.id X) rfl) =  MonoidHom.id (FundamentalGroup X x) := by
  simp

@[simp]
lemma FundamentalGroup.mapOfEq_comp (X Y Z : Type*) (x : X) (y : Y) (z : Z) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : C(X,Y) ) (f : C(Y,Z)) (hg : g x = y) (hf : f y = z):
  FundamentalGroup.mapOfEq (f.comp g) (by simp [hf,hg]) = (FundamentalGroup.mapOfEq f hf).comp (FundamentalGroup.mapOfEq g hg) := by
  subst hf
  subst hg
  simp
  -- ext w

  -- unfold FundamentalGroup.mapOfEq

  -- simp

  -- rw! [←hg]

  -- apply Iso.conj_comp

noncomputable def fundamentalGroupFunctor : PtdTopCat ⥤ GrpCat where
  obj X := GrpCat.of (FundamentalGroup X X.point)
  -- obj X := GrpCat.of (Path.Homotopic.Quotient X.point X.point)
  map {X Y} f := by
    apply GrpCat.ofHom
    apply FundamentalGroup.mapOfEq
    exact f.presPoint

  map_comp f g := by
    rw[←GrpCat.ofHom_comp]
    rw[←FundamentalGroup.mapOfEq_comp]
    rfl

lemma preservesProduct (X : I → PtdTopCat ): Limits.PreservesLimit (Discrete.functor X) fundamentalGroupFunctor := by
  sorry
