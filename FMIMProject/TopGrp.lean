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
public import Mathlib.Topology.Homotopy.Product
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import FMIMProject.PtdTop
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import FMIMProject.Grp
public import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
public import Mathlib.CategoryTheory.Monoidal.Functor
open CategoryTheory

universe u v

variable {I : Type v} (X : I → PtdTopCat.{max u v})

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
lemma FundamentalGroup.mapOfEq_rfl (X Y : Type*) (x : X) [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
  FundamentalGroup.mapOfEq f rfl = FundamentalGroup.map f x := by
  unfold FundamentalGroup.mapOfEq
  ext y
  simp


@[simp]
lemma FundamentalGroup.mapOfEq_id (X : Type*) (x : X) [TopologicalSpace X] :
  FundamentalGroup.mapOfEq (ContinuousMap.id X)
      (show (ContinuousMap.id X) x = x from rfl) =
    MonoidHom.id (FundamentalGroup X x) := by
  change FundamentalGroup.mapOfEq (ContinuousMap.id X)
      (show (ContinuousMap.id X) x = (ContinuousMap.id X) x from rfl) =
    MonoidHom.id (FundamentalGroup X x)
  rw [FundamentalGroup.mapOfEq_rfl]
  exact FundamentalGroup.map_id X x

@[simp]
lemma FundamentalGroup.mapOfEq_comp (X Y Z : Type*) (x : X) (y : Y) (z : Z)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (g : C(X, Y)) (f : C(Y, Z)) (hg : g x = y) (hf : f y = z) :
  FundamentalGroup.mapOfEq (f.comp g) (by simp [hf, hg]) =
    (FundamentalGroup.mapOfEq f hf).comp
      (FundamentalGroup.mapOfEq g hg) := by
  cases hg
  cases hf
  change FundamentalGroup.mapOfEq (f.comp g) rfl =
    (FundamentalGroup.mapOfEq f rfl).comp
      (FundamentalGroup.mapOfEq g rfl)
  rw [FundamentalGroup.mapOfEq_rfl]
  rw [FundamentalGroup.mapOfEq_rfl]
  rw [FundamentalGroup.mapOfEq_rfl]
  exact FundamentalGroup.map_comp X Y Z x g f

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
        simp only [Discrete.functor_obj_eq_as, Functor.const_obj_obj]
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
                funext i
                exact (fundamentalGroupFunctor.map (piπ X i)).hom.map_one'

              map_mul' x y := by
                funext i
                exact (fundamentalGroupFunctor.map (piπ X i)).hom.map_mul' x y
            }

@[simp]
lemma piTopToPiCone_hom_apply
    (p : FundamentalGroup
      ((i : I) → ↑(X i).top)
      (fun i : I => (X i).point))
    (i : I) :
    (ConcreteCategory.hom (piTopToPiCone X).hom) p i =
      Path.Homotopic.proj i p := by
  dsimp [piTopToPiCone]
  change
    (FundamentalGroup.mapOfEq
      (⟨fun y => y i, continuous_apply i⟩ :
        C(((i : I) → ↑(X i).top), ↑(X i).top))
      (show (fun y => y i) (fun i : I => (X i).point) = (X i).point from rfl) p)
      =
    Path.Homotopic.proj i p
  rw [FundamentalGroup.mapOfEq_rfl]
  induction p using Quotient.inductionOn with
  | h γ =>
      rfl

instance : IsIso (piTopToPiCone X) :=
  haveI : IsIso (piTopToPiCone X).hom := by
    let f := (piTopToPiCone X).hom
    have hf : Function.Bijective (ConcreteCategory.hom f) := by
      constructor
      · intro a b h
        have hproj :
            (fun i => Path.Homotopic.proj i a) =
              (fun i => Path.Homotopic.proj i b) := by
          funext i
          have hi :
              (ConcreteCategory.hom (piTopToPiCone X).hom) a i =
                (ConcreteCategory.hom (piTopToPiCone X).hom) b i := by
            simpa [f] using congrFun h i
          exact
            (piTopToPiCone_hom_apply X a i).symm.trans
              (hi.trans (piTopToPiCone_hom_apply X b i))
        exact
          (Path.Homotopic.pi_proj a).symm.trans
            ((congrArg (fun q => Path.Homotopic.pi q) hproj).trans
              (Path.Homotopic.pi_proj b))
      · intro y
        refine ⟨Path.Homotopic.pi y, ?_⟩
        funext i
        have h₁ := piTopToPiCone_hom_apply X (Path.Homotopic.pi y) i
        have h₂ := Path.Homotopic.proj_pi i y
        simpa [f] using h₁.trans h₂
    rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
    exact hf
  Limits.Cone.cone_iso_of_hom_iso (piTopToPiCone X)

lemma preservesProduct : Limits.PreservesLimit (Discrete.functor X) fundamentalGroupFunctor := by
  apply Limits.preservesLimit_of_preserves_limit_cone (piFanIsLimit X)
  apply (Limits.IsLimit.ofConeEquiv (coneDiscreteComp X)).toFun
  simp only [coneDiscreteComp_obj_mapCone]
  apply Limits.IsLimit.ofIsoLimit _ (asIso (piTopToPiCone X)).symm
  apply piLimitFanIsLimit fun (i:I) => fundamentalGroupFunctor.obj (X i)



noncomputable instance fundamentalGroupFunctor_preserves_finite_products :
    Limits.PreservesFiniteProducts
      (fundamentalGroupFunctor : PtdTopCat.{u} ⥤ GrpCat.{u}) where
  preserves n := by
    refine ⟨?_⟩
    intro K
    let Y : Fin n → PtdTopCat.{u} :=
      fun i => K.obj ⟨i⟩
    have h : Limits.PreservesLimit
        (Discrete.functor Y)
        (fundamentalGroupFunctor : PtdTopCat.{u} ⥤ GrpCat.{u}) :=
      preservesProduct (X := Y)
    have hK : Discrete.functor Y = K := by
      apply Discrete.functor_ext
      intro i
      simp [Y]
    simpa [hK] using h




open CategoryTheory.Limits
open CartesianMonoidalCategory
open scoped MonObj

noncomputable instance ptdTopCat_cartesianMonoidal :
    CartesianMonoidalCategory PtdTopCat.{u} := by
  apply CartesianMonoidalCategory.ofChosenFiniteProducts
  · let Y : PEmpty → PtdTopCat.{u} :=
      fun i => PEmpty.elim i
    change Limits.LimitCone (Discrete.functor Y)
    exact ⟨piFan Y, piFanIsLimit Y⟩
  · intro A B
    let Y : Limits.WalkingPair → PtdTopCat.{u} :=
      fun j =>
        Limits.WalkingPair.rec A B j
    exact
      (⟨piFan Y, by
          simpa [Limits.pair, Y] using piFanIsLimit Y⟩ :
        Limits.LimitCone (Limits.pair A B))


noncomputable instance fundamentalGroupFunctor_monoidal :
    (fundamentalGroupFunctor : PtdTopCat.{u} ⥤ GrpCat.{u}).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts
    (fundamentalGroupFunctor : PtdTopCat.{u} ⥤ GrpCat.{u})

noncomputable def topGrpToPtdTop
    (A : Type u) [TopologicalSpace A] [One A] : PtdTopCat.{u} :=
  PtdTopCat.of (TopCat.of A) (1 : A)


theorem fundamentalGroup_topologicalGroup_commutative
    (A : Type u) [TopologicalSpace A] [Group A] [IsTopologicalGroup A]
    [GrpObj (topGrpToPtdTop A)] :
    @Std.Commutative (FundamentalGroup A (1 : A)) (fun a b => a * b) := by
  haveI : GrpObj
      ((fundamentalGroupFunctor : PtdTopCat.{u} ⥤ GrpCat.{u}).obj
        (topGrpToPtdTop A)) :=
    Functor.grpObjObj
      (F := (fundamentalGroupFunctor : PtdTopCat.{u} ⥤ GrpCat.{u}))
      (G := topGrpToPtdTop A)
  simpa [fundamentalGroupFunctor, topGrpToPtdTop] using
    (grpIsCommGrpCat
      ((fundamentalGroupFunctor : PtdTopCat.{u} ⥤ GrpCat.{u}).obj
        (topGrpToPtdTop A)))

theorem fundamentalGroup_topologicalGroup_mul_comm
    (A : Type u) [TopologicalSpace A] [Group A] [IsTopologicalGroup A]
    [GrpObj (topGrpToPtdTop A)]
    (a b : FundamentalGroup A (1 : A)) :
    a * b = b * a := by
  exact (fundamentalGroup_topologicalGroup_commutative A).comm a b
