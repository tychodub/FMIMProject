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

@[simps]
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
    lift S := by
      refine
        { hom' := TopCat.ofHom
            { toFun := fun s i => (S.π.app ⟨i⟩).hom' s
              continuous_toFun := continuous_pi fun i =>
                (TopCat.Hom.hom (S.π.app ⟨i⟩).hom').continuous_toFun }
          presPoint := ?_ }
      change
        (fun i => (S.π.app ⟨i⟩).hom' S.pt.point)
          =
        (fun i => (α i).point)
      funext i
      simpa using (S.π.app ⟨i⟩).presPoint

    fac S j := by
      apply Hom.ext
      ext x
      cases j
      rfl

    uniq := by
      intro S m h
      apply Hom.ext
      ext x
      funext i
      have h' :
          m.hom' ≫ ((piFan α).π.app ⟨i⟩).hom' = (S.π.app ⟨i⟩).hom' := by
        simpa using congrArg Hom.hom' (h ⟨i⟩)
      simpa [piFan, piπ, TopCat.hom_comp, ContinuousMap.comp_apply] using
        ConcreteCategory.congr_hom h' x
