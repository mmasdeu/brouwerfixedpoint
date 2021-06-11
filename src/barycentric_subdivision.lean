import data.real.basic
import combinatorics.simplicial_complex.basic
import combinatorics.simplicial_complex.finite
import combinatorics.simplicial_complex.sperner

variables {m n : ℕ}
local notation `E` := fin m → ℝ

noncomputable def barycenter(L: list E): E :=
  (list.foldl (λ x:E , λ y:E, x + y) 0 L) / L.length
  
variables L: list E

#check L.tail
#check barycenter ↑L

-- Donada una ordenació dels vertexs de cada cara, tenim un simplex de la subdivisió baricentrica.
-- To do, afegir `[list.nodup L]`
def face_baricentric_subdivision(L : list E): set E :=
  begin
    induction L with L' hL' smaller_dim_baricentric_subdivision,
    {
      exact (∅ : finset E),
    },
    {
      let B := barycenter ↑L',
      
      exact {B} ∪ smaller_dim_baricentric_subdivision,
      
      { -- no se perque haig de demostrar això.
        fconstructor,
        intro x,
        exact [x],
      },
      
    },
    -- Definició recursiva
    -- Si L.length > 1,
    -- afegitm el punt `barycenter L` i tots els punts de `face_barycentric_subdivision L.tail`
    -- Si L.length = 1, afegim el punt.
  end
-- Cada cara del complx simplicial s'ha de subdividir amb aquesta funció. 
-- Per cada permutació dels vertexs de la cara tenim un simplex de la subdivisió.
-- Falaria la condició que L conté tots els vertexs de la cara, que jo ho faria així:
--  [ hL : (∀ x : S.vertices, x ∈ L)  ]



-- L'objectiu de tot això seria aconseguir completar aquesta definició.
/-def simplicial_complex.barycentric_subdivision (S : simplicial_complex E) : simplicial_complex E :=
{ faces := {X | ∃ {L : list (fin m → ℝ)}, list.to_finset L ∈ S.faces ∧ X = },
  indep := _,
  down_closed := _,
  disjoint := _ }-/


-- TODO: We need the diameter of the convexhull of A.
-- TODO: We need to take the maximum of this finite set.
def diameter_face (A : finset E): ℝ :=
  sorry
--  {d | (∃ x y ∈ A, d = dist x y)}


open affine
open set

-- simplicial_complex.mesh_size
def diameter (S: simplicial_complex E) [simplicial_complex.finite S]: ℝ :=
 sorry
 -- maxim diametre entre totes les cares.
