import data.real.basic
import combinatorics.simplicial_complex.basic
import combinatorics.simplicial_complex.finite
import combinatorics.simplicial_complex.sperner


variables {m n : ℕ}
local notation `E` := fin m → ℝ

open affine
open set

-- The proposition that a given sperner colouring is sperner.
#check is_sperner_colouring

variables {S: simplicial_complex E} [hS: simplicial_complex.finite S]
          [h₂S : simplicial_complex.full_dimensional S]

#check hS

-- TODO: This definition is not right. We need the diameter of the convexhull of A.
-- TODO: We need to take the maximum of this finite set.
def diameter_face (A : finset E): set ℝ :=
  {d | (∃ x y ∈ A, d = dist x y)}

-- simplicial_complex.mesh_size
def diameter (S: simplicial_complex E) [simplicial_complex.finite S]: ℝ :=
 sorry
 -- maxim diametre entre totes les cares.


