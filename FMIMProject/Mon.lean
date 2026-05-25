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
open MonoidalCategory
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

def mon_mul {M : Mon MonCat} : M.X → M.X → M.X := by
  intros x y
  exact M.mon.mul.hom (x, y)

lemma ones_coincide {M : Mon MonCat} : 1 = M.mon.one 1 := by
  rw [MonoidHom.map_one]

instance mul_instance {M : MonCat} : @IsUnital M (fun a b ↦ a * b) 1 where
  left_id := one_mul
  right_id := mul_one

instance mon_instance {M : Mon MonCat} : @IsUnital M.X mon_mul 1 where
  left_id := by
    intro x
    unfold mon_mul
    rw [ones_coincide]
    calc
      M.mon.mul.hom' ((M.mon.one.hom') 1, x) = ((M.mon.one ⊗ₘ 𝟙 M.X) ≫ M.mon.mul).hom' (1, x) := by
        exact MonoidHom.mem_eqLocusM.mp rfl
      _ = (𝟙 M.X : M.X ⟶ M.X).hom' x := by
        rw [one_mul_hom]
        rfl
      _ = x := by
        apply MonCat.id_apply
  right_id := by
    intro x
    unfold mon_mul
    rw [ones_coincide]
    calc
      M.mon.mul.hom' (x, (M.mon.one.hom') 1) = ((𝟙 M.X ⊗ₘ M.mon.one) ≫ M.mon.mul).hom' (x, 1) := by
        exact MonoidHom.mem_eqLocusM.mp rfl
      _ = (𝟙 M.X : M.X ⟶ M.X).hom' x := by
        rw [mul_one_hom]
        rfl
      _ = x := by
        apply MonCat.id_apply

lemma muls_coincide {M : Mon MonCat} (a b c d : M.X) :  (mon_mul a b) * (mon_mul c d) =
mon_mul (a * c) (b * d) := by
  unfold mon_mul
  rw [← MonoidHom.map_mul (MonCat.Hom.hom M.mon.mul) (a, b) (c, d)]
  rfl


theorem commutative_monoid_of_monoid_object (M : Mon MonCat) : IsCommMonObj M.X := by
  have := @EckmannHilton.mul_comm M.X _ mon_mul 1 1 mul_instance mon_instance muls_coincide
  apply IsCommMonObj.mk
  ext xy
  apply this.comm
