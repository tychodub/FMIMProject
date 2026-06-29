module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Grp_
public import Mathlib.CategoryTheory.Monoidal.Mon_
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.Internal.Module
public import FMIMProject.Mon

@[expose] public section

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

lemma monIsCommGrpCat (M : GrpCat) [MonObj M] :
    @Std.Commutative ((forget₂ GrpCat MonCat).obj M)
      (fun a b => a * b) := by
  let mMon : Mon MonCat :=
    @Mon.mk MonCat _ _
      ((forget₂ GrpCat MonCat).obj M)
      (Functor.monObjObj M)
  simpa [mMon] using IsCommMonObj_of_monoid_object mMon


lemma grpIsCommGrpCat (G : GrpCat) [GrpObj G] :
    @Std.Commutative ((forget₂ GrpCat MonCat).obj G)
      (fun a b => a * b) := by
  let mMon : Mon MonCat :=
    @Mon.mk MonCat _ _
      ((forget₂ GrpCat MonCat).obj G)
      (Functor.monObjObj G)
  simpa [mMon] using IsCommMonObj_of_monoid_object mMon



/--
A monoid object in `Ab`, written elementwise, gives a ring.
-/
@[irreducible] noncomputable def monoidObjectInAb_isRing
    (A : ModuleCat ℤ)
    [MonObj A] :
    Ring A := by
  exact ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toRing A
