module
public import Mathlib.Tactic
public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.Algebra.Group.Prod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon_
open CategoryTheory
open Limits

@[expose] public section

def binaryProductCone (M N : MonCat) : BinaryFan M N := by
  apply BinaryFan.mk
  · exact (MonCat.ofHom (MonoidHom.fst M N))
  · exact (MonCat.ofHom (MonoidHom.snd M N))


def terminalLimitCone : IsTerminal (MonCat.of PUnit) := by
  fapply IsTerminal.ofUniqueHom
  · intro M
    apply MonCat.ofHom
    exact default
  · intros M f
    ext

instance : CartesianMonoidalCategory MonCat := by
  apply CartesianMonoidalCategory.ofChosenFiniteProducts
  · exact ⟨_, terminalLimitCone⟩
  intros M N
  fapply LimitCone.mk
  · apply binaryProductCone
  apply BinaryFan.IsLimit.mk _ (fun l r ↦ MonCat.ofHom (MonoidHom.prod l.hom r.hom))
  · intros; rfl
  · intros; rfl
  cat_disch


instance : BraidedCategory MonCat := BraidedCategory.ofCartesianMonoidalCategory
instance : SymmetricCategory MonCat := SymmetricCategory.mk


theorem commutative_monoid_of_monoid_object (M : Mon MonCat) : IsCommMonObj M.X := by
  apply IsCommMonObj.mk
  ext XY
  sorry
