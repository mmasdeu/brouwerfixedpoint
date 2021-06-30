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
open_locale big_operators

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
  have hpos : ∀ (n : ℕ), 0 < 1 / ((n+1) : ℝ), by apply nat.one_div_pos_of_nat,
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
    specialize hΦ2 (metric.ball z (δ)) (by rwa [metric.mem_ball, dist_self]) (metric.is_open_ball),
    simp [metric.mem_ball, dist_comm] at hΦ2,
    simp only [function.comp_app],
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
    have hmn : 1 / ((m + 1) : ℝ) ≤ 1 / ((n + 1) : ℝ), by apply nat.one_div_le_one_div hm,
    have hinc : 1 / ((Φ m) + 1:ℝ) ≤ 1 / ((m + 1):ℝ),
    {
      have h' : m ≤ Φ m := strict_mono.id_le hΦ1 m,
      apply nat.one_div_le_one_div h',
    },
    linarith,
  },
  have H3 : ∃ (n : ℕ), ∀ m ≥ n, dist (f ((a∘Φ) m)) (f z) < ε/3 := 
      let ⟨δ, ⟨hδpos, h'⟩⟩ := (metric.continuous_iff.1 hf) z (ε/3) (by linarith), ⟨n1, hn1⟩ := H1 δ hδpos in 
        ⟨n1, λ m hm, let h := hn1 m hm in h' (a (Φ m)) (by rwa dist_comm)⟩,
  obtain ⟨⟨n1, hn1⟩, ⟨n2, hn2⟩, ⟨n3, hn3⟩⟩ := ⟨H1 (ε / 3) (by linarith), H2, H3⟩,
  let n := max (max n1 n2) n3,
  specialize hn1 n (le_of_max_le_left (le_max_left (max n1 n2) n3)),
  specialize hn2 n (le_trans (le_max_right n1 n2) (le_max_left (max n1 n2) n3)),
  specialize hn3 n (le_max_right (max n1 n2) n3),
  calc
  dist z (f z) ≤ dist z ((a ∘ Φ) n)
                + dist ((a ∘ Φ) n) (f ((a ∘ Φ) n))
                + dist (f ((a ∘ Φ) n)) (f z) : dist_triangle4 z ((a ∘ Φ) n) (f ((a ∘ Φ) n)) (f z)
  ... ≤ ε/3 + ε/3 + ε/3 : by { linarith [hn1, hn2, hn3] }
  ... = ε : by {ring},
end

lemma characterisation_uniform_continuous_on {X : Type} [metric_space X] (S : set X) (f : X → X):
  uniform_continuous_on f S ↔ ∀ (ε : nnreal) (hε : ε > 0), ∃ (δ : nnreal) (hδ : δ > 0), 
  ∀ (x y : X), edist x y ≤ δ → edist (f x) (f y) ≤ ε :=
begin
  sorry
end

lemma enndiameter_growth (X : Type) [metric_space X] (S : set X)
  (f : X → X) (hf : uniform_continuous_on f S) (ε : nnreal) (hε : 0 < ε) : 
  ∃ (δ : nnreal) (hδ : δ > 0), ∀ T ⊆ S, emetric.diam T ≤ δ → emetric.diam (f '' T) ≤ ε :=
let ⟨δ, hδ, H⟩ := (characterisation_uniform_continuous_on S f).1 hf ε hε in 
  ⟨δ, hδ, (λ R hR hdR, emetric.diam_image_le_iff.2 (λ x hx y hy, H x y (emetric.diam_le_iff.1 hdR x hx y hy)))⟩

lemma diameter_growth (X : Type) [metric_space X] (S : set X)
  (f : X → X) (hf : uniform_continuous_on f S) (ε : ℝ) (hε : 0 < ε) : 
  ∃ δ > 0, ∀ T ⊆ S, metric.bounded T → metric.diam T ≤ δ →
  metric.bounded (f '' T) ∧ metric.diam (f '' T) ≤ ε :=
let ⟨δ, ⟨hδ,HH⟩⟩ := enndiameter_growth _ _ _ hf _ (real.to_nnreal_pos.mpr hε),
h2 : ∀ (T : set X), T ⊆ S → metric.bounded T → metric.diam T ≤ ↑δ → metric.bounded (f '' T) ∧ metric.diam (f '' T) ≤ ε :=
  (λ T hT1 hTb hT2, let hT2 : emetric.diam T ≤ δ := 
    (let htop := metric.bounded.ediam_ne_top hTb in
      (ennreal.to_real_le_to_real htop (ennreal.coe_ne_top)).mp (by rwa ennreal.coe_to_real)), 
    hHH := HH T hT1 hT2 in 
    by
    begin
      split,
      {
        sorry
      },
      rwa [metric.diam, ←@ennreal.le_of_real_iff_to_real_le (emetric.diam (f '' T)) ε
      (λ hc, ennreal.not_top_le_coe (by rwa ← hc)) (le_of_lt hε)]
    end
  ) in
⟨δ, nnreal.coe_pos.mpr hδ, h2⟩

variables {d : ℕ} [hd: 0 < d]
local notation `E` := fin d → ℝ

-- S is the set of vertices of a simplex
variables (S: set E) [hS: ∀ (s : E), s ∈ S → (∑ (i : fin d), s i) = 1]

variables (f: E → E) [hf: uniform_continuous_on f S]

-- per tota coordenada i, existeix un vertex v tal que la coordenada i-èssima 
-- és la primera que complex que f(v)_i < f(v)
def is_sperner_triangle (f: E → E): Prop := 
  ∀ i: fin d, ∃ p: E, p ∈ S → (∀ j < i, (f p) j ≥  (p:E) j) →  (((f p) i) < p i)


lemma ordered_vertices_implies_epsilon_fixed (S : set E)
(f : E → E)
(hS : ∀ (s : E), s ∈ S → (∑ (i : fin d), s i) = 1)
(hf : uniform_continuous_on f (convex_hull S)) (ε : nnreal) (hε : 0 < ε)
: ∃ δ > 0, ∀ T ⊆ S, emetric.diam T < δ ∧
is_sperner_triangle S f
→ ∃ x ∈ T, edist (f x) x < ε :=
begin
  sorry
end
