module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.TopCat.Limits.Products

@[expose] public section

open CategoryTheory Topology

universe v u w

class PointedTopologicalSpace (X : Type u) (x : X) where
  protected isTop : TopologicalSpace X

public structure PtdTopCat where
  of ::
  top : TopCat.{u}
  point : top

public instance : CoeSort (PtdTopCat) (Type u) :=
  ⟨fun x ↦ PtdTopCat.top x⟩

@[ext]
public structure Hom (X Y : PtdTopCat) where
  of ::
  hom' : X.top⟶ Y.top
  presPoint : hom' (X.point) = Y.point

@[simps?]
public instance : Category PtdTopCat where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 X.top,rfl⟩
  comp f g := by
    refine ⟨f.hom' ≫ g.hom', ?_⟩
    simp only [TopCat.hom_comp, ContinuousMap.comp_apply]
    rw [f.presPoint,g.presPoint]

abbrev piπ {ι : Type v} (α : ι → PtdTopCat.{max v u}) (i : ι) : PtdTopCat.of (TopCat.of (∀ i, α i))
(fun i:ι ↦ (α i).point  ) ⟶ α i where
  hom' := by
    apply TopCat.piπ
  presPoint := by
    simp

-- piFan is the same as TopCat.piFan, but then for PtdTopCat
def piFan {ι : Type v} (α : ι → PtdTopCat.{max v u}) : CategoryTheory.Limits.Fan α :=
  CategoryTheory.Limits.Fan.mk
    (PtdTopCat.of (TopCat.of (∀ i, α i)) (fun i:ι ↦ (α i).point  )) (piπ.{v, u} α)
-- piFanIsLimit is the same as TopCat.piFanIsLimt, but then for PtdTopCat.
def piFanIsLimit {ι : Type v} (α : ι → PtdTopCat.{max v u}) :
  CategoryTheory.Limits.IsLimit (piFan α) where
  lift S := Hom.of (TopCat.ofHom
    {toFun:= fun s i => (S.π.app ⟨i⟩).hom' s
     continuous_toFun := continuous_pi (fun i => (S.π.app ⟨i⟩).hom'.hom.2)})
     (by
        simp only [Functor.const_obj_obj, Discrete.functor_obj_eq_as, ConcreteCategory.hom_ofHom]
        change ((fun s i ↦ (ConcreteCategory.hom (S.π.app { as := i }).hom') s) S.pt.point
          =(piFan α).pt.point )
        simp only [Discrete.functor_obj_eq_as, Functor.const_obj_obj]
        ext i
        have := (S.π.app { as := i }).presPoint;
        simp only [Discrete.functor_obj_eq_as, Functor.const_obj_obj] at this;
        exact this
      )
  uniq := by
    intro S m h
    cases m with
    | of mh mp =>
    have : mh = TopCat.ofHom
      { toFun := fun s i ↦ (ConcreteCategory.hom (S.π.app { as := i }).hom') s,
        continuous_toFun := continuous_pi fun i ↦
          (TopCat.Hom.hom (S.π.app { as := i }).hom').continuous_toFun } := by
      ext x
      funext i
      have h' : ∀ (j : Discrete ι), mh ≫ ((piFan α).π.app j).hom' = (S.π.app j).hom' := by
        intro j
        calc
          mh ≫ ((piFan α).π.app j).hom' =
            ({ hom' := mh, presPoint := mp }: S.pt ⟶ (piFan α).pt).hom' ≫ ((piFan α).π.app j).hom'
            := by rfl
          _ = (({ hom' := mh, presPoint := mp }: S.pt ⟶ (piFan α).pt) ≫ ((piFan α).π.app j)).hom'
            := by rfl
          _ = (S.π.app j).hom' := by rw [h j]
      simp only [Discrete.functor_obj_eq_as, Functor.const_obj_obj, ConcreteCategory.hom_ofHom]
      change (((ConcreteCategory.hom mh) x i) =
        (fun s i ↦ (ConcreteCategory.hom (S.π.app { as := i }).hom') s) x i)
      simp [← h' ⟨i⟩]
      rfl
    subst this
    simp
