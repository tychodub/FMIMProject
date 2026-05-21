module
public import Mathlib.Tactic
public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.Algebra.Group.Prod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_
import Mathlib.GroupTheory.EckmannHilton
open CategoryTheory
open Limits
open MonObj

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

-- instance (M : Mon MonCat) : MulOneClass M.X where
--   one := M.mon.one 1
--   mul X Y := M.mon.mul ⟨ X , Y ⟩
--   one_mul a := sorry
--   mul_one := sorry

-- lemma swap_muls (M : Mon MonCat) (a b c d : M.X) : M.mon.mul (a * b , c * d) = (M.mon.mul (a,c)) * (M.mon.mul (b,d)) := by
--   apply M.mon.one.hom'.map_mul

-- instance (M : Mon MonCat) : MulOneClass M.X := b

-- lemma ones_coincide (M : Mon MonCat) : M.mon.one 1 = 1 := by
--   apply M.mon.one.hom'.map_one

-- instance monobjinstance (M : Mon MonCat) (Y : MonCat) : Mul (Y ⟶ M.X) where
--   mul := by
--     intros f g
--     apply MonCat.instCategory.comp
--     · exact CartesianMonoidalCategory.lift f g
--     · exact M.mon.mul

-- instance (M : Mon MonCat) (Y : MonCat) : MulOneClass (Y ⟶ M.X) where
--   one := _
--   mul := _
--   one_mul := _
--   mul_one := _

theorem commutative_monoid_of_monoid_object (M : Mon MonCat) : IsCommMonObj M.X := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro Y
  let : CommMonoid (Y ⟶ M.X) := by
    apply EckmannHilton.commMonoid
    sorry
    sorry
    sorry
    sorry
  exact this.to_isCommutative
