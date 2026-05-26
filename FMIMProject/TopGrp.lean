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
public import Mathlib.CategoryTheory.Types.Basic

public import FMIMProject.PtdTop

open CategoryTheory

universe u v

variable {I : Type u} (X : I → PtdTopCat.{u}) (C : I → GrpCat)

@[simp]
lemma FundamentalGroup.map_id (X : Type*) (x : X) [TopologicalSpace X] :
  (FundamentalGroup.map (ContinuousMap.id X) x ) =  MonoidHom.id (FundamentalGroup X x) := by
  ext y
  induction y using Quotient.inductionOn with | h a =>
  rfl

@[simp]
lemma FundamentalGroup.map_comp (X Y Z : Type*) (x : X) [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (g : C(X, Y)) (f : C(Y, Z)) :
  FundamentalGroup.map (f.comp g ) x =
    (FundamentalGroup.map f (g x)).comp (FundamentalGroup.map g x) := by
  ext y
  induction y using Quotient.inductionOn with | h a =>
  rfl

@[simp]
lemma FundamentalGroup.mapofEq_rfl (X Y : Type*) (x : X) [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
  FundamentalGroup.mapOfEq f rfl = FundamentalGroup.map f x := by
  unfold FundamentalGroup.mapOfEq
  ext y
  simp


@[simp]
lemma FundamentalGroup.mapOfEq_id (X : Type*) (x : X) [TopologicalSpace X] :
  (FundamentalGroup.mapOfEq (ContinuousMap.id X) rfl) =  MonoidHom.id (FundamentalGroup X x) := by
  simp

@[simp]
lemma FundamentalGroup.mapOfEq_comp (X Y Z : Type*) (x : X) (y : Y) (z : Z) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (g : C(X, Y)) (f : C(Y, Z)) (hg : g x = y)
    (hf : f y = z) :
  FundamentalGroup.mapOfEq (f.comp g) (by simp [hf,hg]) =
    (FundamentalGroup.mapOfEq f hf).comp (FundamentalGroup.mapOfEq g hg) := by
  subst hf
  subst hg
  simp

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

noncomputable def X' (i : I) : GrpCat := fundamentalGroupFunctor.obj (X i)

noncomputable def proj (i : I) : fundamentalGroupFunctor.obj (PtdTopCat.of (TopCat.of (∀ i, X i))
    (fun i:I ↦ (X i).point  )) ⟶ fundamentalGroupFunctor.obj (X i) :=
  fundamentalGroupFunctor.map (Hom.of ⟨_, continuous_apply i⟩ rfl)

noncomputable def coneDiscreteComp :
    Limits.Cone (Discrete.functor X ⋙ fundamentalGroupFunctor) ≌
    Limits.Cone (Discrete.functor fun i => fundamentalGroupFunctor.obj (X i)) :=
  Limits.Cone.postcomposeEquivalence (Discrete.compNatIsoDiscrete X fundamentalGroupFunctor)

theorem coneDiscreteComp_obj_mapCone :
    (coneDiscreteComp X).functor.obj (Functor.mapCone fundamentalGroupFunctor (piFan X)) =
      Limits.Fan.mk (fundamentalGroupFunctor.obj (PtdTopCat.of (TopCat.of (∀ i, X i))
        (fun i:I ↦ (X i).point  ))) (proj X) :=
  rfl

def piProj
    (X : I → GrpCat)
    (b : I) :
    GrpCat.of ((i : I) → X i) →* X b :=⟨
    { toFun := fun f => f b,
      map_one' := rfl},(by intro x y; rfl)
  ⟩
-- (piProj (fun (b:I) => fundamentalGroupFunctor.obj (X b)))

def piLimitFanIsLimit
    (X : I → GrpCat) :
    Limits.IsLimit (Limits.Fan.mk (GrpCat.of (∀ (i: I), (X i)))
        (fun b => GrpCat.ofHom (piProj X b) )) where
      lift S := GrpCat.ofHom
                  {
                    toFun := fun s i => S.π.app ⟨i⟩ s
                    map_one':= by funext i; exact  (S.π.app ⟨i⟩).hom.map_one'
                    map_mul':= by intro a b; funext i; exact  (S.π.app ⟨i⟩).hom.map_mul' a b
                  }
      uniq := by
        intro S m hm
        cases m with
        | _ mh =>
        ext s
        funext i
        simp only [Discrete.functor_obj_eq_as, Functor.const_obj_obj, ConcreteCategory.hom_ofHom]
        change (mh s i = (fun s i ↦ (ConcreteCategory.hom (S.π.app { as := i })) s) s i)
        simp
        have := hm ⟨i⟩
        simp [← this]
        rfl

noncomputable def fundamentalProj
    (b : I) :
    GrpCat.of (∀i, fundamentalGroupFunctor.obj (X i)) ⟶ fundamentalGroupFunctor.obj (X b) := by
      apply GrpCat.ofHom
      exact ⟨{toFun:= fun f => f b,map_one':= rfl},by intro x y ; rfl⟩

noncomputable def piTopToPiCone :
    Limits.Fan.mk (fundamentalGroupFunctor.obj
        (PtdTopCat.of (TopCat.of (∀ i, X i)) (fun i:I ↦ (X i).point  ))) (proj X) ⟶
      Limits.Fan.mk (GrpCat.of (∀i, fundamentalGroupFunctor.obj (X i))) (by apply fundamentalProj)
        where
    hom := GrpCat.ofHom
            {
              toFun x i := by
                have : (fundamentalGroupFunctor.obj (PtdTopCat.of (TopCat.of (∀ i, X i))
                    (fun i:I ↦ (X i).point  ))) ⟶ fundamentalGroupFunctor.obj (X i) := by
                  apply fundamentalGroupFunctor.map
                  apply piπ
                apply this.hom.toFun
                exact x

              map_one' := by
                simp
                rfl
              map_mul' x y:= by
                simp
                rfl
            }

instance : IsIso (piTopToPiCone X) :=
  haveI : IsIso (piTopToPiCone X).hom := by
    let f := (piTopToPiCone X).hom
    have hf : Function.Bijective f := by
      constructor
      . sorry
      . sorry
    -- For some reason this gives an error:
    -- rw [CategoryTheory.isIso_iff_bijective f]

    sorry
  Limits.Cone.cone_iso_of_hom_iso (piTopToPiCone X)

lemma preservesProduct : Limits.PreservesLimit (Discrete.functor X) fundamentalGroupFunctor := by
  apply Limits.preservesLimit_of_preserves_limit_cone (piFanIsLimit X)
  apply (Limits.IsLimit.ofConeEquiv (coneDiscreteComp X)).toFun
  simp only [coneDiscreteComp_obj_mapCone]
  apply Limits.IsLimit.ofIsoLimit _ (asIso (piTopToPiCone X)).symm
  apply piLimitFanIsLimit fun (i:I) => fundamentalGroupFunctor.obj (X i)
