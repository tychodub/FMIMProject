module
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Topology.Homotopy.Path
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

import FMIMProject.PtdTop

open CategoryTheory


noncomputable def myMul (X : PtdTopCat) : (Path.Homotopic.Quotient X.point X.point) → (Path.Homotopic.Quotient X.point X.point) → (Path.Homotopic.Quotient X.point X.point) := Path.Homotopic.Quotient.trans

noncomputable instance (X : PtdTopCat) : Group (Path.Homotopic.Quotient X.point X.point) where
  mul := myMul X
  mul_assoc := by
    rintro a b c
    change (a.trans b).trans c = a.trans (b.trans c)
    induction a using Quotient.ind with | _ =>
    induction b using Quotient.ind with | _ =>
    induction c using Quotient.ind with | _ =>
    apply Quotient.sound
    constructor
    apply Path.Homotopy.transAssoc

  one := ⟦Path.refl X.point⟧
  one_mul := by
    rintro a
    change Path.Homotopic.Quotient.trans ⟦Path.refl X.point⟧ a = a
    induction a using Quotient.ind with | _ =>
    apply Quotient.sound
    constructor
    apply Path.Homotopy.reflTrans
  mul_one := by
    rintro a
    change Path.Homotopic.Quotient.trans a ⟦Path.refl X.point⟧ = a
    induction a using Quotient.ind with | _ =>
    apply Quotient.sound
    constructor
    apply Path.Homotopy.transRefl
  inv := Quotient.lift (fun f ↦ ⟦f.symm⟧) (by rintro a b ⟨h⟩; exact Quotient.sound ⟨h.symm₂⟩)
  inv_mul_cancel := by
    intro a
    sorry




noncomputable def fundamentalGroupFunctor : PtdTopCat ⥤ GrpCat where
  obj X := GrpCat.of (FundamentalGroup X X.point)
  -- obj X := GrpCat.of (Path.Homotopic.Quotient X.point X.point)
  map {X Y} f := by
    rw [←f.presPoint]
    exact GrpCat.ofHom (FundamentalGroup.map f.hom' X.point)
  map_id _ := sorry
  map_comp _ _ := sorry
