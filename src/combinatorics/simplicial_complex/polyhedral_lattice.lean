/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.polyhedron
import combinatorics.simplicial_complex.polytope

open set affine poly

variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {X Y : finset E} {C : set E}

/-- Faces of a polytope form a complete lattice. -/
def complete_lattice_faces (P : poly.polytope E) : complete_lattice (polytope.to_simplicial_complex P).faces :=
sorry 
