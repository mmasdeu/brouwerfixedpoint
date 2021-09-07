import data.real.basic
import combinatorics.simplicial_complex.basic
import combinatorics.simplicial_complex.finite
import combinatorics.simplicial_complex.sperner

variables {m n : ℕ}
local notation `E` := fin m → ℝ

noncomputable def barycenter(L: list E): E :=
  (list.foldl (λ x:E , λ y:E, x + y) (0 : E) L) / L.length
  
variables (L : list E) [pseudo_metric_space E]

namespace list

-- Given an order of the vertices of each face, we have a simplex of the barycentric subdivision.
  -- Recursive definition
  -- If L.length > 1,
  -- add the point `barycenter L` and all the points of `face_barycentric_subdivision L.tail`
  -- If L.length = 1, add the point.

noncomputable def face_baricentric_subdivision(L : list E) : finset E :=
  begin
    induction L with head tail smaller_dim_baricentric_subdivision,
    { exact (∅ : finset E) },
    { exact { barycenter (list.cons head tail) } ∪ smaller_dim_baricentric_subdivision },
  end
   
open affine

-- The goal is to complete this definition.
noncomputable def simplicial_complex.barycentric_subdivision (S : simplicial_complex E) : simplicial_complex E :=
  { faces := {X | ∃ {L : list E}, list.nodup L ∧ list.to_finset L ∈ S.faces ∧ X = face_baricentric_subdivision L},
  indep := 
    begin
      rintros face ⟨vertex_list, ⟨vertex_nodup, ⟨h_face3, face_from_vertex_list⟩⟩⟩,
      cases S,
      simp at h_face3,
      -- help?
      sorry,
    end,
  down_closed := sorry,
  disjoint := sorry }

-- The maximum distance bewteen any pair of vertices in a simplicial complex.
noncomputable def distance_vertices  (A : set E) : ℝ :=
  metric.diam A
  --Sup {d | ∃ x y ∈ A, d = edist x y}

lemma distance_vertices_eq_diam_convexhull(A : set E):
  metric.diam (convex_hull A) = metric.diam A :=
  begin
    -- apply convex_hull_diam,
    sorry,
  end
   


open affine
open set

-- simplicial_complex.mesh_size
def diameter (S: simplicial_complex E) [simplicial_complex.finite S]: ℝ :=
 sorry
 -- maxim diametre entre totes les cares.

end list