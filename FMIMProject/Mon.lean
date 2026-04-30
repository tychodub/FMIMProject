module
import Mathlib

instance : CategoryTheory.CartesianMonoidalCategory MonCat := by
  apply CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts
  sorry
  sorry

instance : CategoryTheory.BraidedCategory MonCat := sorry


theorem commutative_monoid_of_monoid_object (M : CategoryTheory.Mon MonCat) : CategoryTheory.IsCommMonObj M.X := sorry
