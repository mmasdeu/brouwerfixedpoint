import .simplicial_complex

open affine

variables {m n : ℕ}
local notation `E` := fin m → ℝ

def is_sperner_colouring (S : simplicial_complex E)
  (f : E → fin m) : Prop :=
∀ (x : E) i, x ∈ S.points → x i = 0 → f x ≠ i