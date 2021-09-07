import data.real.basic
import data.list
import barycentric_subdivision
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



