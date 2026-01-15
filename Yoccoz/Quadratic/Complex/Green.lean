import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Escape
import Yoccoz.Quadratic.Complex.GreenLemmas

/-!
# Green's Function for the Quadratic Family

This file defines the Green's function `G_c(z)` for the filled Julia set `K(c)`.
The Green's function measures the rate of escape to infinity.

## Connection to MLC

The Green's function is used to construct Yoccoz puzzles, which are central to the proof of the
Mandelbrot Local Connectivity (MLC) conjecture.

*   **Equipotentials and Rays**: Level sets of `G_c` (equipotentials) and their orthogonal trajectories
    (external rays) form a grid on `ℂ \ K(c)`.
*   **Yoccoz Puzzles**: Intersections of these curves define puzzle pieces used to analyze the combinatorics
    of orbits.
*   **Böttcher Coordinates**: `G_c` is the real part of the Böttcher coordinate, conjugating `f_c` to `z ↦ z^2`
    near infinity.

## Main Definitions

* `potential_seq c z n`: The sequence `1/2^n * log ‖f_c^n(z)‖`.
* `green_function c z`: The limit of `potential_seq` as `n → ∞`.

## Main Results (Sketched)

* `green_function_eq_zero_iff_mem_K`: `G_c(z) = 0 ↔ z ∈ K(c)`.
* `green_function_functional_eq`: `G_c(f_c(z)) = 2 * G_c(z)`.
* `green_function_harmonic`: `G_c` is harmonic on `ℂ \ K(c)`.

-/

namespace MLC.Quadratic

open scoped Complex
open Complex Topology Filter Real

noncomputable section

variable {c z : ℂ}

set_option maxHeartbeats 4000000

/-- The Green's function satisfies the functional equation `G(f(z)) = 2 * G(z)`.
    Proof idea:
    `G(f(z)) = lim_{n→∞} 1/2^n log |f^n(f(z))|`
    `= lim_{n→∞} 1/2^n log |f^{n+1}(z)|`
    `= lim_{n→∞} 2 * (1/2^{n+1} log |f^{n+1}(z)|)`
    `= 2 * G(z)`. -/
lemma green_function_functional_eq (c z : ℂ) :
    green_function c (fc c z) = 2 * green_function c z := by
  have h_lim : Tendsto (fun n => potential_seq c (fc c z) n) atTop (𝓝 (2 * green_function c z)) := by
    have h_shift : ∀ n, potential_seq c (fc c z) n = 2 * potential_seq c z (n + 1) := by
      intro n
      dsimp [potential_seq]
      have h_orb : orbit c (fc c z) n = orbit c z (n + 1) := by
        induction n with
        | zero => simp
        | succ n ih => simp [orbit_succ, ih]
      rw [h_orb]
      rw [pow_succ' 2 n]
      field_simp
    simp_rw [h_shift]
    apply Tendsto.const_mul
    have h_tendsto := green_function_eq_lim c z
    exact h_tendsto.comp (tendsto_add_atTop_nat 1)
  
  have h_eq : green_function c (fc c z) = 2 * green_function c z := by
    rw [green_function, limUnder, lim]
    have h_ex : ∃ x, map (potential_seq c (fc c z)) atTop ≤ 𝓝 x := ⟨2 * green_function c z, h_lim⟩
    have h_spec := Classical.epsilon_spec h_ex
    exact (tendsto_nhds_unique h_lim h_spec).symm
  exact h_eq

/-- The Green's function is non-negative. -/
lemma green_function_nonneg (c z : ℂ) : 0 ≤ green_function c z := by
  have h_lim : Tendsto (fun n => - potential_seq c z n) atTop (𝓝 (- green_function c z)) :=
    (green_function_eq_lim c z).neg
  have h_le : - green_function c z ≤ 0 := by
    apply le_of_tendsto' h_lim
    intro n
    simp only [neg_nonpos]
    rw [potential_seq]
    apply mul_nonneg
    · positivity
    · apply Real.log_nonneg
      apply le_max_left
  linarith

lemma green_function_iterate (c z : ℂ) (n : ℕ) :
    green_function c (orbit c z n) = 2^n * green_function c z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [orbit_succ, green_function_functional_eq, ih]
    rw [pow_succ]
    ring

lemma green_function_pos_of_large_norm (c z : ℂ) (h : ‖z‖ > escape_bound c) :
    0 < green_function c z := by
  have h_conv : Tendsto (potential_seq c z) atTop (𝓝 (green_function c z)) :=
    green_function_eq_lim c z
  
  let M := 2 * ‖c‖ / (escape_bound c)^2
  have h_diff : ∀ k, ‖orbit c z k‖ > escape_bound c →
      dist (potential_seq c z k) (potential_seq c z (k + 1)) ≤ (1 / 2 ^ (k + 1)) * M := by
    intro k hk
    exact potential_seq_diff_le c z k hk
  
  have h_orbit_large : ∀ k, ‖orbit c z k‖ > escape_bound c := by
    intro k
    have h_R : ‖z‖ > R c := lt_of_le_of_lt (escape_bound_ge_R c) h
    have := norm_orbit_ge_of_norm_ge_R c z k h_R
    apply lt_of_lt_of_le h this
  
  have h_cauchy : ∀ k, dist (potential_seq c z k) (potential_seq c z (k + 1)) ≤ (1 / 2 ^ (k + 1)) * M :=
    fun k => h_diff k (h_orbit_large k)
  
  have h_dist_0_L : dist (potential_seq c z 0) (green_function c z) ≤ M := by
    let d : ℕ → ℝ := fun k => (1 / 2) ^ (k + 1) * M
    
    have h_summable_bound : Summable d := by
      dsimp [d]
      simp_rw [pow_succ]
      apply Summable.mul_right
      apply Summable.mul_right
      apply summable_geometric_of_lt_one
      · norm_num
      · norm_num

    have h_dist_le_bound : ∀ k, dist (potential_seq c z k) (potential_seq c z (k + 1)) ≤ d k := by
      intro k
      specialize h_cauchy k
      dsimp [d]
      convert h_cauchy using 1
      simp only [one_div, inv_pow]

    apply le_trans (dist_le_tsum_of_dist_le_of_tendsto₀ d h_dist_le_bound h_summable_bound h_conv)
    
    dsimp [d]
    rw [tsum_mul_right]
    simp_rw [pow_succ]
    rw [tsum_mul_right]
    have h_sum_geom : ∑' (n : ℕ), (1 / 2 : ℝ) ^ n = 2 := by
      rw [tsum_geometric_of_lt_one]
      · norm_num
      · norm_num
      · norm_num
    rw [h_sum_geom]
    field_simp
    apply le_refl
  
  rw [dist_eq_norm, Real.norm_eq_abs] at h_dist_0_L
  rw [abs_le] at h_dist_0_L
  
  have h_a0 : potential_seq c z 0 = Real.log ‖z‖ := by
    simp [potential_seq]
    rw [max_eq_right]
    apply le_trans (le_trans one_le_two (R_ge_two c))
    apply le_trans (escape_bound_ge_R c) (le_of_lt h)
  
  rw [h_a0] at h_dist_0_L
  have h_lower : Real.log ‖z‖ - M ≤ green_function c z := by linarith
  
  apply lt_of_lt_of_le _ h_lower
  rw [sub_pos]
  apply lt_trans _ (Real.log_lt_log (lt_of_lt_of_le zero_lt_two (le_trans (R_ge_two c) (escape_bound_ge_R c))) h)
  exact log_escape_bound_gt_two_mul_norm_c_div_sq c

/-- A point is in the filled Julia set iff its Green's function is zero.
    Proof idea:
    *   `→`: If `G(z) = 0`, suppose `z ∉ K(c)`. Then `z` escapes, and we can show `G(z) > 0`
        (using the positive growth rate outside `K(c)`). Contradiction.
    *   `←`: If `z ∈ K(c)`, the orbit is bounded, so `potential_seq` converges to 0. -/
lemma green_function_eq_zero_iff_mem_K (c z : ℂ) :
    green_function c z = 0 ↔ z ∈ K c := by
  constructor
  · intro h
    by_contra h_esc
    dsimp [K, boundedOrbit] at h_esc
    push_neg at h_esc
    obtain ⟨n, hn⟩ := h_esc (escape_bound c)
    have h_pos : 0 < green_function c (orbit c z n) := 
      green_function_pos_of_large_norm c (orbit c z n) hn
    rw [green_function_iterate] at h_pos
    rw [h, mul_zero] at h_pos
    linarith
  · intro h
    apply le_antisymm
    · have h_lim := potential_seq_converges_of_mem_K h
      rw [green_function]
      exact le_of_eq (tendsto_nhds_unique (green_function_eq_lim c z) h_lim)
    · exact green_function_nonneg c z

/-- The Green's function is positive on the basin of infinity. -/
lemma green_function_pos_iff_not_mem_K (c z : ℂ) :
    0 < green_function c z ↔ z ∉ K c := by
  rw [← not_iff_not]
  push_neg
  have : green_function c z ≤ 0 ↔ green_function c z = 0 := by
    constructor
    · intro h; exact le_antisymm h (green_function_nonneg c z)
    · intro h; rw [h]
  rw [this]
  rw [green_function_eq_zero_iff_mem_K]



end

end MLC.Quadratic