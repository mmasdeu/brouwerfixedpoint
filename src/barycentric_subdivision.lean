import data.real.basic
import combinatorics.simplicial_complex.basic
import combinatorics.simplicial_complex.finite
import combinatorics.simplicial_complex.sperner

variables {m n : ℕ}
local notation `E` := fin m → ℝ

noncomputable def barycenter(L: list E): E :=
  (list.foldl (λ x:E , λ y:E, x + y) (0 : E) L) / L.length
  
variables (L : list E) [pseudo_metric_space E]

-- Why can't I turn this into an instance?
lemma tail_nodup {T: Type}(L : list T) [list.nodup L] : list.nodup (L.tail) :=
begin
  induction L with x L IH,
  {
    simp,
  },
  {
    simp,
    finish,
  },
end

lemma tail_nodup2 {T: Type}(head: T)(tail : list T) [list.nodup (head :: tail)] : list.nodup tail :=
begin
  induction tail with x tail IH,
  {
    simp,
  },
  {
    simp,
    finish,
  },
end

namespace list

-- Given an order of the vertices of each face, we have a simplex of the barycentric subdivision.
-- To do, add `[list.nodup L]`. Done, but I'm not sure if it's useful.
def face_baricentric_subdivision{L : list E}[nodup: list.nodup L] : set E :=
  begin
    induction L with head tail smaller_dim_baricentric_subdivision nodup,
    { exact (∅ : finset E) },
    { 
      have : tail.nodup :=  @tail_nodup2 _ _ _ nodup,
      exact {barycenter (list.cons head tail)} ∪ (@smaller_dim_baricentric_subdivision this)},
    
    -- Recursive definition
    -- If L.length > 1,
    -- add the point `barycenter L` and all the points of `face_barycentric_subdivision L.tail`
    -- If L.length = 1, add the point.

  end

def face_baricentric_subdivision2{L : list E} : set E :=
  begin
    induction L with head tail smaller_dim_baricentric_subdivision,
    { exact (∅ : finset E) },
    { 
      exact { barycenter (list.cons head tail) } ∪ smaller_dim_baricentric_subdivision },
    
    -- Recursive definition
    -- If L.length > 1,
    -- add the point `barycenter L` and all the points of `face_barycentric_subdivision L.tail`
    -- If L.length = 1, add the point.
  end

-- The goal is to complete this definition.
/-def simplicial_complex.barycentric_subdivision (S : simplicial_complex E) : simplicial_complex E :=
{ faces := {X | ∃ {L : list (fin m → ℝ)}, list.to_finset L ∈ S.faces ∧ X = },
  indep := _,
  down_closed := _,
  disjoint := _ }-/

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