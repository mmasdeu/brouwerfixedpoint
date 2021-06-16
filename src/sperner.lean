import tactic
import data.set.finite
import data.real.basic
import linear_algebra.affine_space.independent
import analysis.convex.basic
import topology.sequences

noncomputable theory
open set
open affine
open topological_space

open_locale affine
open_locale filter

variables  {V : Type*} [add_comm_group V] [module ℝ V]
variables [affine_space V V]

variables {k n : ℕ}

variables (Δ : simplex ℝ V n)

def pts (C : simplex ℝ V k) : set V := convex_hull (C.points '' univ)

structure triangulation :=
(simps : set (@simplex ℝ V V _ _ _ _ n) )
(cov : (⋃ s ∈ simps, (pts s)) = pts Δ)
--(inter : ∀ s t ∈ simps, (pts s) ∩ (pts t) ≠ ∅ → ∃ (m : ℕ) (st m),
--  (pts s) ∩ (pts t) = pts st)
-- exercici: escriure la condició d'intersecció fent servir "face".


lemma fixed_point_of_epsilon_fixed (X : Type) [metric_space X]
  [hsq : seq_compact_space X]
  (f : X → X) (hf : continuous f)
  (h : ∀ (ε : ℝ), 0 < ε → ∃ x, dist x (f x) < ε) :
  ∃ x : X, f x = x :=
begin
  have hpos : ∀ (n : ℕ), 0 < 1 / ((n+1) : ℝ),
  {
    apply nat.one_div_pos_of_nat,
  },
  let a : ℕ → X := λ n, classical.some (h (1 / ((n+1) : ℝ)) (hpos n)),
  have ha : ∀ n, dist (a n) (f (a n)) < 1 / ((n+1) : ℝ) :=
    λ n, classical.some_spec (h (1 / ((n+1) : ℝ)) (hpos n)),
  have exists_lim : ∃ (z ∈ univ) (Φ : ℕ → ℕ),
  strict_mono Φ ∧ filter.tendsto (a ∘ Φ) filter.at_top (nhds z),
  {
    apply hsq.seq_compact_univ,
    exact λ n, by tauto,
  },
  obtain ⟨z, ⟨_, ⟨Φ, ⟨hΦ1, hΦ2⟩⟩⟩ ⟩ := exists_lim,
  use z,
  suffices : ∀ ε > 0, dist z (f z) ≤ ε,
  {
    rw [←dist_le_zero, dist_comm],
    exact le_of_forall_le_of_dense this,
  },
  intros ε hε,
  have H1 : ∀ δ, 0 < δ →  ∃ (n : ℕ), ∀ m ≥ n, dist z ((a ∘ Φ) m) < δ,
  {
    intros δ hδ,
    rw seq_tendsto_iff at hΦ2,
    specialize hΦ2 (metric.ball z (δ)) (_) (metric.is_open_ball),
    {
      rw [metric.mem_ball, dist_self],
      linarith,
    },
    simp [metric.mem_ball, dist_comm] at hΦ2,
    simp [←dist_comm],
    exact hΦ2,
  },
  have H2 : ∃ (n : ℕ), ∀ m ≥ n, dist ((a∘Φ) m) (f ((a∘Φ) m)) ≤ ε/3,
  {
    have hkey : ∃ (n : ℕ), 1 / ((n+1):ℝ) < ε/3,
    {
      have hnlarge : ∃ (n : ℕ), (n :ℝ) > 3 / ε := exists_nat_gt (3 / ε),
      obtain ⟨n, hn⟩:= hnlarge,
      use n,
      have hn' : (n+1 : ℝ) > 3 / ε, by linarith,
      refine (inv_lt_inv _ (hpos n)).mp _, by linarith,
      field_simp,
      linarith,
    },
    obtain ⟨n, hn⟩ := hkey,
    use n,
    intros m hm,
    specialize ha (Φ m),
    have hmn : 1 / ((m + 1) : ℝ) ≤ 1 / ((n + 1) : ℝ),
    {
      apply nat.one_div_le_one_div hm,
    },
    have hinc : 1 / ((Φ m) + 1:ℝ) ≤ 1 / ((m + 1):ℝ),
    {
      have h' : m ≤ Φ m := strict_mono.id_le hΦ1 m,
      apply nat.one_div_le_one_div h',
    },
    linarith,
  },
  have H3 : ∃ (n : ℕ), ∀ m ≥ n, dist (f ((a∘Φ) m)) (f z) < ε/3,
  {
    rw metric.continuous_iff at hf,
    specialize hf z (ε/3) (by linarith),
    obtain ⟨δ, ⟨hδpos, h'⟩⟩ := hf,
    obtain ⟨n1, hn1⟩ := H1 δ hδpos,
    use n1,
    intros m hm,
    specialize hn1 m hm,
    rw dist_comm at hn1,
    specialize h' (a (Φ m)) hn1,
    exact h',
  },
  obtain ⟨n1, hn1⟩ := H1 (ε / 3) (by linarith),
  obtain ⟨n2, hn2⟩ := H2,
  obtain ⟨n3, hn3⟩ := H3,
  let n := max (max n1 n2) n3,
  specialize hn1 n _,
  {
    calc n ≥ max n1 n2 : by {exact le_max_left (max n1 n2) n3}
    ... ≥ n1 : by {exact le_max_left n1 n2}
  },
  specialize hn2 n _,
  {
    calc n ≥ max n1 n2 : by {exact le_max_left (max n1 n2) n3}
    ... ≥ n2 : by {exact le_max_right n1 n2}
  },
  specialize hn3 n (le_max_right (max n1 n2) n3),
  calc
  dist z (f z) ≤ dist z ((a ∘ Φ) n)
                + dist ((a ∘ Φ) n) (f ((a ∘ Φ) n))
                + dist (f ((a ∘ Φ) n)) (f z) : dist_triangle4 z ((a ∘ Φ) n) (f ((a ∘ Φ) n)) (f z)
  ... ≤ ε/3 + ε/3 + ε/3 : by { linarith [hn1, hn2, hn3] }
  ... = ε : by {linarith}
end

lemma diameter_growth (X : Type) [metric_space X] (S : set X)
(f : X → X) (hf : uniform_continuous_on f S) (ε : ℝ) (hε : 0 < ε)
: ∃ δ > 0, ∀ T ⊆ S, metric.diam T < δ → metric.diam (f '' T) < ε :=
begin
  sorry
end