import algebraic_topology.simplicial_object
import data.real.basic
import .dependencies.simplicial_complex
import .dependencies.sperner


variables {m n : ℕ}
local notation `E` := fin m → ℝ

-- The proposition that a given sperner colouring is sperner.
#check is_sperner_colouring


