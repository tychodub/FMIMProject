module
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp_
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products

public import FMIMProject.PtdTop

open CategoryTheory

universe u v

variable {I : Type u} (X : I → PtdTopCat.{u})

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

noncomputable def proj (i : I) : fundamentalGroupFunctor.obj (PtdTopCat.of (TopCat.of (∀ i, X i)) (fun i:I ↦ (X i).point  )) ⟶ fundamentalGroupFunctor.obj (X i) :=
  fundamentalGroupFunctor.map (Hom.of ⟨_, continuous_apply i⟩ rfl)

noncomputable def coneDiscreteComp :
    Limits.Cone (Discrete.functor X ⋙ fundamentalGroupFunctor) ≌ Limits.Cone (Discrete.functor fun i => fundamentalGroupFunctor.obj (X i)) :=
  Limits.Cone.postcomposeEquivalence (Discrete.compNatIsoDiscrete X fundamentalGroupFunctor)

theorem coneDiscreteComp_obj_mapCone :
    (coneDiscreteComp X).functor.obj (Functor.mapCone fundamentalGroupFunctor (piFan X)) =
      Limits.Fan.mk (fundamentalGroupFunctor.obj (PtdTopCat.of (TopCat.of (∀ i, X i)) (fun i:I ↦ (X i).point  ))) (proj X) :=
  rfl

def piProj
    {I : Type}
    (X : I → GrpCat)
    (b : I) :
    GrpCat.of ((i : I) → X i) →* X b :=⟨
    { toFun := fun f => f b,
      map_one' := rfl},(by intro x y; rfl)
  ⟩
-- (piProj (fun (b:I) => fundamentalGroupFunctor.obj (X b)))

-- def piTopToPiCone :
--     Limits.Fan.mk (fundamentalGroupFunctor.obj (PtdTopCat.of (TopCat.of (∀ i, X i)) (fun i:I ↦ (X i).point  ))) (proj X) ⟶
--       CategoryTheory.Limits.Fan.mk (GrpCat.of (∀i, fundamentalGroupFunctor.obj (X i))) (by ) where
--   hom := CategoryTheory.Functor.pi' (proj X)

lemma preservesProduct : Limits.PreservesLimit (Discrete.functor X) fundamentalGroupFunctor := by
  apply Limits.preservesLimit_of_preserves_limit_cone (piFanIsLimit X)
  apply (Limits.IsLimit.ofConeEquiv (coneDiscreteComp X)).toFun
  simp only [coneDiscreteComp_obj_mapCone]
  sorry

  --apply Limits.IsLimit.ofIsoLimit _ (asIso (piTopToPiCone X)).symm
