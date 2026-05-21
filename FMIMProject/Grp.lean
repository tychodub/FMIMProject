module
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.Internal.Module
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
      refine forget_reflects_commutativity M ?_
      let mMon := @Mon.mk MonCat _ _ ((forget₂ GrpCat MonCat).obj M)
                                 (Functor.monObjObj M)
      exact commutative_monoid_of_monoid_object mMon

lemma grpIsCommGrpCat (G : GrpCat) [GrpObj G] : IsCommMonObj G := by
  let mMon : Mon MonCat :=
    @Mon.mk MonCat _ _
      ((forget₂ GrpCat MonCat).obj G)
      (Functor.monObjObj G)
  have hForget :
      @IsCommMonObj _ _ _ _
        ((forget₂ GrpCat MonCat).obj G)
        (Functor.monObjObj G) :=
    commutative_monoid_of_monoid_object mMon
  exact forget_reflects_commutativity G hForget


/--
A monoid object in `Ab`, written elementwise, gives a ring.
-/
@[irreducible] noncomputable def monoidObjectInAb_isRing
    (A : ModuleCat ℤ)
    [MonObj A] :
    Ring A := by
  exact ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toRing A
