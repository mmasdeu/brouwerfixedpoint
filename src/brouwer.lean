import data.real.basic
import combinatorics.simplicial_complex.basic
import combinatorics.simplicial_complex.sperner


variables {m n : ℕ}
local notation `E` := fin m → ℝ


open affine

-- The proposition that a given sperner colouring is sperner.
#check is_sperner_colouring

def diameter (S: simplicial_complex E): ℝ :=
 sorry
 -- maxima distancia entre dos punts qualsevols
 -- si no hi hagues maxim (un complexe simplicial infinit), que fem?


