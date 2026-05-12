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
