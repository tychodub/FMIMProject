module
public import Mathlib.Tactic
public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.Algebra.Group.Prod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_
public import Mathlib.GroupTheory.EckmannHilton
open CategoryTheory
open Limits
open MonObj
open CartesianMonoidalCategory
open EckmannHilton

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


lemma ones_coincide (M : Mon MonCat) (Y : MonCat) : (1 : Y ⟶ M.X) = toUnit Y ≫ M.mon.one := by
  ext x
  -- rw [show (MonCat.Hom.hom (1 : Y ⟶ M.X)) x = 1 from rfl]
  rw [show (MonCat.Hom.hom (toUnit Y ≫ η)) x = M.mon.one.hom' ((toUnit Y).hom' x) from rfl]
  rw [show (toUnit Y).hom' x = 1 from rfl]
  rw [MonoidHom.map_one M.mon.one.hom']
  rfl


instance test (M : Mon MonCat) (Y : MonCat) : @EckmannHilton.IsUnital (Y ⟶ M.X) (fun f g ↦
(CartesianMonoidalCategory.lift f g) ≫ M.mon.mul) 1 where
  left_id := by
    intro f
    rw [ones_coincide, lift_comp_one_left]
  right_id := by
    intro f
    rw [ones_coincide, lift_comp_one_right]

theorem commutative_monoid_of_monoid_object (M : Mon MonCat) : IsCommMonObj M.X := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro Y
  let : CommMonoid (Y ⟶ M.X) := by
    apply EckmannHilton.commMonoid
    · exact test M Y
    intros a b c d
    rw [show lift a c ≫ μ * lift b d ≫ μ = lift (lift a c ≫ μ) (lift b d ≫ μ) ≫ μ from rfl]
    rw [← lift_map (lift a c) (lift b d) μ μ]
    rw [← lift_lift_associator_inv a c (lift b d)]
    rw??

    -- rw [← Hom.mul_def (a * b) (c * d)]

    sorry
  exact this.to_isCommutative
