module
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Monoidal.ofHasFiniteProducts
import Mathlib.Algebra.Category.Grp.CartesianMonoidal
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Limits
import FMIMProject.Mon

open CategoryTheory

instance : Functor.LaxMonoidal (forget₂ GrpCat MonCat) where
    ε := by
        exact 𝟙 (MonoidalCategoryStruct.tensorUnit MonCat)
    μ := by
        exact fun X Y ↦
          𝟙
            (MonoidalCategoryStruct.tensorObj ((forget₂ GrpCat MonCat).obj X)
              ((forget₂ GrpCat MonCat).obj Y))


lemma forget_reflects_commutativity
      (M : GrpCat)
      [MonObj M] :
      (@IsCommMonObj _ _ _ _ ((forget₂ GrpCat MonCat).obj M)
       (Functor.monObjObj M))
      → IsCommMonObj M := by
        intro forgetComm
        refine { mul_comm := ?_ }
        have isComm2 : (forget₂ GrpCat MonCat).map (β_ M M).hom ≫
               (forget₂ GrpCat MonCat).map MonObj.mul =
               (forget₂ GrpCat MonCat).map MonObj.mul := by
               apply forgetComm.mul_comm
        have : (forget₂ GrpCat MonCat).map (β_ M M).hom ≫
               (forget₂ GrpCat MonCat).map MonObj.mul =
               (forget₂ GrpCat MonCat).map ((β_ M M).hom ≫ MonObj.mul) := by
                   simp
        rw [this] at isComm2
        apply forget₂_faithful.map_injective at isComm2
        assumption

lemma monIsCommGrpCat (M : GrpCat) [MonObj M] : IsCommMonObj M := by

/--
every internal group in the category of groups is also commutative.
-/
structure SimpleInternalGroupInGrp where
  Carrier : Type
  instGroup : Group Carrier

  star : Carrier → Carrier → Carrier
  e : Carrier

  star_left_id : ∀ x : Carrier, star e x = x
  star_right_id : ∀ x : Carrier, star x e = x

  interchange :
    ∀ a b c d : Carrier,
      star (a * c) (b * d) = star a b * star c d

attribute [instance] SimpleInternalGroupInGrp.instGroup

theorem simpleInternalGroupInGrp_ambient_mul_comm
    (G : SimpleInternalGroupInGrp) :
    ∀ x y : G.Carrier, x * y = y * x := by
  letI : Group G.Carrier := G.instGroup
  have e_eq_one : G.e = (1 : G.Carrier) := by
    calc
      G.e = G.star G.e G.e := by
        rw [G.star_left_id G.e]
      _ = G.star (G.e * 1) (1 * G.e) := by
        simp
      _ = G.star G.e 1 * G.star 1 G.e := by
        exact G.interchange G.e 1 1 G.e
      _ = 1 * 1 := by
        rw [G.star_left_id 1, G.star_right_id 1]
      _ = 1 := by
        simp
  intro x y
  calc
    x * y = G.star x G.e * G.star G.e y := by
      rw [G.star_right_id x, G.star_left_id y]
    _ = G.star (x * G.e) (G.e * y) := by
      rw [← G.interchange x G.e G.e y]
    _ = G.star x y := by
      rw [e_eq_one]
      simp
    _ = G.star (G.e * x) (y * G.e) := by
      rw [e_eq_one]
      simp
    _ = G.star G.e y * G.star x G.e := by
      rw [G.interchange G.e y x G.e]
    _ = y * x := by
      rw [G.star_left_id y, G.star_right_id x]
