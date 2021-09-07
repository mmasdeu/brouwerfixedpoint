import tactic
import data.set.finite
import data.real.basic
import data.real.ereal
import linear_algebra.affine_space.independent
import analysis.convex.basic
import topology.sequences

noncomputable theory
open set affine topological_space 
open_locale affine filter big_operators

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
    have hinc : 1 / ((Φ m) + 1:ℝ) ≤ 1 / ((m + 1):ℝ), by exact nat.one_div_le_one_div (strict_mono.id_le hΦ1 m),
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

lemma le_min_right_or_left {α : Type*} [linear_order α] (a b : α) : a ≤ min a b ∨ b ≤ min a b :=
by cases (le_total a b) with h; simp [true_or, le_min rfl.ge h]; exact or.inr h

lemma max_le_right_or_left {α : Type*} [linear_order α] (a b : α) : max a b ≤ a ∨ max a b ≤ b :=
by cases (le_total a b) with h; simp [true_or, max_le rfl.ge h]; exact or.inr h

lemma edist_lt_of_diam_lt {X : Type*} [pseudo_emetric_space X] (s : set X)  {d : ennreal} :
  emetric.diam s < d → ∀ (x ∈ s) (y ∈ s), edist x y < d :=
λ h x hx y hy, gt_of_gt_of_ge h (emetric.edist_le_diam_of_mem hx hy)

lemma enndiameter_growth' {X : Type} [pseudo_emetric_space X] {S : set X}
  {f : X → X} (hf : uniform_continuous_on f S) : ∀ ε > 0,  ∃ δ > 0, 
  ∀ T ⊆ S, emetric.diam T < δ → emetric.diam (f '' T) ≤ ε :=
λ ε hε, let ⟨δ, hδ, H⟩ := emetric.uniform_continuous_on_iff.1 hf ε hε in
  ⟨δ, hδ, λ R hR hdR, emetric.diam_image_le_iff.2 
  (λ x hx y hy, le_of_lt (H (hR hx) (hR hy) (edist_lt_of_diam_lt R hdR x hx y hy)))⟩

lemma enndiameter_growth {X : Type} [pseudo_emetric_space X] {S : set X}
  {f : X → X} (hf : uniform_continuous_on f S) : ∀ ε > 0,  ∃ δ > 0, 
  ∀ T ⊆ S, emetric.diam T < δ → emetric.diam (f '' T) < ε :=
begin
  intros ε hε,
  set γ := min 1 (ε/2) with hhγ,
  have hγ : γ > 0,
  { cases (le_min_right_or_left 1 (ε/2)),
    { exact lt_of_lt_of_le (ennreal.zero_lt_one) h },
    { exact lt_of_lt_of_le (ennreal.div_pos_iff.2 ⟨ne_of_gt hε, ennreal.two_ne_top⟩) h } },
  obtain ⟨δ, hδ, H⟩ := enndiameter_growth' hf γ hγ,
  have hγε: γ < ε,
  { cases (lt_or_ge 1 ε),
    { exact lt_of_le_of_lt (min_le_left 1 (ε/2)) h },
    { have hεtop := ne_of_lt (lt_of_le_of_lt h (lt_of_le_of_ne le_top ennreal.one_ne_top)),
      exact lt_of_le_of_lt (min_le_right 1 (ε/2)) (ennreal.half_lt_self (ne_of_gt hε) hεtop) } },
  exact ⟨δ, hδ, (λ R hR hdR, lt_of_le_of_lt (H R hR hdR) hγε)⟩,
end

lemma diameter_growth (X : Type) [metric_space X] (S : set X)
  (f : X → X) (hf : uniform_continuous_on f S) (ε : ℝ) (hε : 0 < ε) : 
  ∃ δ > 0, ∀ T ⊆ S, metric.bounded T → metric.diam T ≤ δ →
  metric.bounded (f '' T) ∧ metric.diam (f '' T) ≤ ε :=
begin
  sorry
end

variables {d : ℕ}
local notation `E` := fin d → ℝ

def H := { x: E | (∑ (i : fin d), x i) = 1}

variables (f: E → E)

example (a b : real) (r : ennreal) (h1 : (a : ereal) ≤ (b : ereal) + r) (h2 : (a : ereal) ≥ (b : ereal) - r) :
  ennreal.of_real (abs (a - b)) ≤ r :=
begin
  sorry
end

lemma points_coordinates_bounded_distance (x y : E) (i : fin d) :
  ennreal.of_real (abs (x i - y i)) ≤ edist x y :=
begin
  sorry
end

lemma points_coordinates_bounded_diam (S : set E) (x y : E) (hx : x ∈ S) (hy : y ∈ S)
(i : fin d) : ennreal.of_real (abs (x i - y i)) ≤ emetric.diam S :=
begin
  sorry
end


-- per tota coordenada i, existeix un vertex v tal que la coordenada i-èssima 
-- és la primera que complex que f(v)_i < f(v)
def is_sperner_set (f: E → E) (S : set E)  := 
  ∀ i: fin d, ∃ v : E, v ∈ S ∧
  (∀ j < i, (f v) j ≥  (v j)) ∧ (((f v) i) < v i)

lemma epsilon_fixed_condition
{f : E → E} {S : set E} (hs : S ⊆ H) (hd : 0 < d)
(hf : uniform_continuous_on f S) 
{ε : real} (hε : 0 < ε)
: ∃ δ, 0 < δ ∧
∀ T ⊆ S,
  metric.bounded T → metric.diam T < δ →
  is_sperner_set f T →
  ∀ x ∈ T, dist (f x) x < ε :=
begin
  let ε₁ := ε / (2 * d),
  have h₁ := div_pos hε (mul_pos zero_lt_two (nat.cast_pos.mpr hd)),
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := metric.uniform_continuous_on_iff.mp hf ε₁ h₁,
  let δ := min δ₀ (ε₁/2),
  use δ,
  split,
  { cases le_min_right_or_left δ₀ (ε₁/2),
    { exact gt_of_ge_of_gt h hδ₀pos },
    { exact lt_min hδ₀pos (half_pos h₁) } },
  intros T hTS hbT hdT hfT x hx,
  have hmost : ∀ (i : fin d) (hi : (i : ℕ) ≠ d-1),
    abs (((f x) i)-(x i))
     ≤ δ + (metric.diam (f '' T)),
  {
    intros i hi,
    rw abs_sub_le_iff,
    split,
    {
      sorry
    },
    {
      sorry
    }
  },
  have hlast : abs(((f x) ⟨d-1, buffer.lt_aux_2 hd⟩)) - x ⟨d-1, buffer.lt_aux_2 hd⟩ ≤ (d-1) * (δ + (metric.diam (f '' T))),
  {
    sorry
  },
  sorry
end
