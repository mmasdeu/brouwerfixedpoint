import tactic
import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.combination
import linear_algebra.finite_dimensional
import analysis.convex.topology

open_locale classical affine big_operators
open set

namespace affine

/--
A simplicial complex in `R^m`.
TODO: generalise to normed affine spaces `E`, so this is `simplicial_complex E`.
-/
 
@[ext] structure simplicial_complex (E : Type*) [normed_group E] [normed_space ℝ E] :=
(faces : set (finset E))
(indep : ∀ {X}, X ∈ faces → affine_independent ℝ (λ p, p : (X : set E) → E))
(down_closed : ∀ {X Y}, X ∈ faces → Y ⊆ X → Y ∈ faces)
(disjoint : ∀ {X Y}, X ∈ faces → Y ∈ faces →
  convex_hull ↑X ∩ convex_hull ↑Y ⊆ convex_hull (X ∩ Y : set E))

variables {m n : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E] {S : simplicial_complex E}
  {x y : E} {X Y : finset E} {A : set (finset E)}
--local notation `E` := E

/--
The underlying space of a simplicial complex.
-/
def simplicial_complex.space (S : simplicial_complex E) :
  set E :=
⋃ X ∈ S.faces, convex_hull (X : set E)



def simplicial_complex.points (S : simplicial_complex E) :
  set E :=
⋃ k ∈ S.faces, (k : set E)

end affine