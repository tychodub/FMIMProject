module
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Monoidal.ofHasFiniteProducts
import Mathlib.Algebra.Category.Grp.CartesianMonoidal
import Mathlib.Algebra.Category.Grp.Adjunctions

open CategoryTheory

-- I could not find the instance of CartesianMonoidalCategory for MonCat, if it exists
noncomputable instance MonCatCart : CartesianMonoidalCategory MonCat := CartesianMonoidalCategory.ofHasFiniteProducts
noncomputable instance : BraidedCategory MonCat := BraidedCategory.ofCartesianMonoidalCategory

instance : Functor.LaxMonoidal (forget₂ GrpCat MonCat) where
    ε := sorry
    μ := sorry

lemma forget_reflects_commutativity
      (M : GrpCat)
      [MonObj M] :
      (@IsCommMonObj _ _ _ _ ((forget₂ GrpCat MonCat).obj M)
       (Functor.monObjObj M))
      → IsCommMonObj M := sorry
