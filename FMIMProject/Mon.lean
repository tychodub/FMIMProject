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

-- we need to define a second monoid structure on M.X given by the monoid multiplication in MonCat
def mon_mul {M : Mon MonCat} : M.X → M.X → M.X := by
  intros x y
  exact μ[M.X].hom (x, y)

-- This repackages the fact that M has a unit in a way we need
instance mul_is_unital {M : MonCat} : @IsUnital M (fun a b ↦ a * b) 1 where
  left_id := one_mul
  right_id := mul_one

-- This shows that our second multiplication has a unit
instance mon_is_unital {M : Mon MonCat} : @IsUnital M.X mon_mul (η[M.X] 1) where
  left_id := by
    intro x
    unfold mon_mul
    calc
      μ[M.X].hom ((η[M.X].hom) 1, x) = ((η[M.X] ⊗ₘ 𝟙 M.X) ≫ μ).hom (1, x) := by
        exact MonoidHom.mem_eqLocusM.mp rfl
      _ = (𝟙 M.X : M.X ⟶ M.X).hom' x := by
        rw [one_mul_hom]
        rfl
      _ = x := by
        apply MonCat.id_apply
  right_id := by
    intro x
    unfold mon_mul
    calc
      μ[M.X].hom (x, (η[M.X].hom) 1) = ((𝟙 M.X ⊗ₘ η) ≫ μ).hom (x, 1) := by
        exact MonoidHom.mem_eqLocusM.mp rfl
      _ = (𝟙 M.X : M.X ⟶ M.X).hom' x := by
        rw [mul_one_hom]
        rfl
      _ = x := by
        apply MonCat.id_apply

lemma muls_coincide {M : Mon MonCat} (a b c d : M.X) :  (mon_mul a b) * (mon_mul c d) =
mon_mul (a * c) (b * d) := by
  unfold mon_mul
  rw [← MonoidHom.map_mul (MonCat.Hom.hom μ[M.X]) (a, b) (c, d)]
  rfl



theorem IsCommMonObj_of_monoid_object (M : Mon MonCat) :
    @Std.Commutative M.X (fun a b => a * b) :=
  @EckmannHilton.mul_comm M.X
    (fun a b : M.X => mon_mul (M := M) a b)
    (fun a b : M.X => a * b)
    (η[M.X] 1)
    1
    (mon_is_unital (M := M))
    (mul_is_unital (M := M.X))
    (fun a b c d => (muls_coincide (M := M) a c b d).symm)
