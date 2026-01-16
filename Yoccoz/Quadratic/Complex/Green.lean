import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Escape
import Yoccoz.Quadratic.Complex.GreenLemmas
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace MLC.Quadratic

open scoped Complex
open Complex Topology Filter Real Metric

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

/-- `‖z^2 + c‖ ≤ ‖z‖^2 + ‖c‖` -/
lemma norm_fc_le_norm_sq_add_norm_c (c z : ℂ) : ‖fc c z‖ ≤ ‖z‖^2 + ‖c‖ := by
  rw [fc]
  apply le_trans (norm_add_le (z^2) c)
  simp


lemma continuous_fc (c : ℂ) : Continuous (fc c) := by
  unfold fc
  apply Continuous.add
  · apply continuous_pow 2
  · exact continuous_const

lemma continuous_orbit (c : ℂ) (n : ℕ) : Continuous (fun z => orbit c z n) := by
  induction n with
  | zero => simp; exact continuous_id
  | succ n ih =>
    simp only [orbit_succ]
    exact (continuous_fc c).comp ih

lemma continuous_potential_seq (c : ℂ) (n : ℕ) : Continuous (fun z => potential_seq c z n) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  dsimp [potential_seq]
  apply ContinuousAt.mul
  · exact continuousAt_const
  · apply ContinuousAt.comp (g := Real.log)
    · apply Real.continuousAt_log
      apply ne_of_gt
      apply lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
    · apply Continuous.continuousAt
      apply Continuous.max continuous_const
      apply continuous_norm.comp
      exact continuous_orbit c n

lemma norm_orbit_gt_escape_bound_of_ge (c z : ℂ) (k : ℕ) (n : ℕ) (hn : k ≤ n) 
    (h_esc : ‖orbit c z k‖ > escape_bound c) :
    ‖orbit c z n‖ > escape_bound c := by
  have h_R : ‖orbit c z k‖ > R c := lt_of_le_of_lt (escape_bound_ge_R c) h_esc
  let w := orbit c z k
  let m := n - k
  have h_eq : n = m + k := by rw [← Nat.add_sub_of_le hn, add_comm]
  rw [h_eq]
  dsimp [orbit]
  rw [Function.iterate_add_apply]
  have h_growth : ‖(Nat.iterate (fc c) m) w‖ ≥ ‖w‖ :=
     norm_orbit_ge_of_norm_ge_R c w m h_R
  apply lt_of_lt_of_le h_esc h_growth

lemma dist_potential_seq_green_function_le_of_escaping (c z : ℂ) (k : ℕ) 
    (hk : ‖orbit c z k‖ > escape_bound c) :
    dist (potential_seq c z k) (green_function c z) ≤ (1 / 2 ^ k) * (2 * ‖c‖ / (escape_bound c)^2) := by
  let B := escape_bound c
  let M := 2 * ‖c‖ / B^2
  
  have h_diff : ∀ j, dist (potential_seq c z (k + j)) (potential_seq c z (k + j + 1)) ≤ (1 / 2 ^ (k + j + 1)) * M := by
    intro j
    apply potential_seq_diff_le
    apply norm_orbit_gt_escape_bound_of_ge c z k (k + j) (Nat.le_add_right k j) hk
  
  have h_conv : Tendsto (fun m => potential_seq c z (k + m)) atTop (𝓝 (green_function c z)) := by
    have h := green_function_eq_lim c z
    have h_shift : (fun m => potential_seq c z (k + m)) = (potential_seq c z) ∘ (fun m => m + k) := by
      ext m
      congr 1
      rw [add_comm]
    rw [h_shift]
    exact h.comp (tendsto_add_atTop_nat k)

  let d : ℕ → ℝ := fun j => (1 / 2) ^ (k + j + 1) * M
  have h_dist_le : ∀ j, dist (potential_seq c z (k + j)) (potential_seq c z (k + j + 1)) ≤ d j := by
    intro j
    specialize h_diff j
    convert h_diff using 1
    simp [d, one_div, inv_pow]
  
  have h_summable : Summable d := by
    dsimp [d]
    have : ∀ j, d j = ((1/2)^(k+1) * M) * (1/2)^j := by
      intro j
      simp_rw [pow_add, pow_one]
      ring
    refine Summable.congr ?_ (fun j => (this j).symm)
    apply Summable.mul_left
    apply summable_geometric_of_lt_one <;> norm_num

  have h_sum : ∑' j, d j = (1 / 2 ^ k) * M := by
    dsimp [d]
    have : ∀ j, d j = ((1/2)^(k+1) * M) * (1/2)^j := by
      intro j
      simp_rw [pow_add, pow_one]
      ring
    rw [tsum_congr this]
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one] <;> try norm_num
    simp [pow_succ]
    ring
  
  convert dist_le_tsum_of_dist_le_of_tendsto₀ d h_dist_le h_summable h_conv
  rw [h_sum]

-- Assumption: The Green's function is continuous.
lemma continuous_green_function (c : ℂ) : Continuous (green_function c) := by
  have h_unif : TendstoUniformly (fun n z => potential_seq c z n) (green_function c) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
  
    let B := escape_bound c
    let M := 2 * ‖c‖ / B^2
    let C := Real.log B + Real.log (B^2 + ‖c‖) + M
    
    have h_B_ge_1 : B ≥ 1 := le_trans (le_trans one_le_two (R_ge_two c)) (escape_bound_ge_R c)
    have h_B2_c_ge_1 : B^2 + ‖c‖ ≥ 1 := by
      have : 1 ≤ B^2 := by nlinarith
      linarith [norm_nonneg c]

    have h_C_nonneg : 0 ≤ C := by
      apply add_nonneg
      apply add_nonneg
      · apply Real.log_nonneg h_B_ge_1
      · apply Real.log_nonneg h_B2_c_ge_1
      · apply div_nonneg (mul_nonneg zero_le_two (norm_nonneg c)) (pow_nonneg (le_trans zero_le_one h_B_ge_1) 2)
    
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε (add_pos_of_nonneg_of_pos h_C_nonneg zero_lt_one)) (by norm_num : |(1/2 : ℝ)| < 1)
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at hN
    
    rw [Filter.eventually_atTop]
    use N
    intro n hn z
    
    have h_bound : dist (green_function c z) (potential_seq c z n) ≤ (1 / 2 ^ n) * C := by
      by_cases h_esc : ∃ k, ‖orbit c z k‖ > B
      · let k := Nat.find h_esc
        have hk_gt : ‖orbit c z k‖ > B := Nat.find_spec h_esc
        have hk_min : ∀ j < k, ‖orbit c z j‖ ≤ B := fun j hj => not_lt.mp (Nat.find_min h_esc hj)
        
        by_cases h_nk : n < k
        · calc dist (green_function c z) (potential_seq c z n)
            _ ≤ dist (green_function c z) 0 + dist 0 (potential_seq c z n) := dist_triangle _ _ _
            _ = |green_function c z| + |potential_seq c z n| := by simp only [dist_zero_right, dist_zero_left, Real.norm_eq_abs]
            _ = |potential_seq c z n| + |green_function c z| := add_comm _ _
            _ ≤ |potential_seq c z n| + (|potential_seq c z k| + dist (potential_seq c z k) (green_function c z)) := by
              simp only [add_le_add_iff_left]
              rw [dist_eq_norm, Real.norm_eq_abs]
              calc |green_function c z| = dist (green_function c z) 0 := by rw [dist_zero_right, Real.norm_eq_abs]
                _ ≤ dist (green_function c z) (potential_seq c z k) + dist (potential_seq c z k) 0 := dist_triangle _ _ _
                _ = dist (potential_seq c z k) (green_function c z) + |potential_seq c z k| := by rw [dist_comm, dist_zero_right, Real.norm_eq_abs]
                _ = |potential_seq c z k| + dist (potential_seq c z k) (green_function c z) := add_comm _ _
            _ ≤ (1/2^n * Real.log B) + (1/2^k * Real.log (B^2 + ‖c‖)) + (1/2^k * M) := by
               rw [← add_assoc]
               apply add_le_add
               · apply add_le_add
                 · rw [potential_seq, abs_mul, abs_of_nonneg (by positivity)]
                   gcongr
                   rw [abs_of_nonneg]
                   · apply Real.log_le_log
                     · apply lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
                     · apply max_le h_B_ge_1 (hk_min n h_nk)
                   · apply Real.log_nonneg
                     apply le_max_left
                 · rw [potential_seq, abs_mul, abs_of_nonneg (by positivity)]
                   gcongr
                   rw [abs_of_nonneg]
                   · apply Real.log_le_log
                     · apply lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
                     · apply max_le
                       · exact h_B2_c_ge_1
                       · cases hk : k with
                         | zero => rw [hk] at h_nk; exact (Nat.not_lt_zero n h_nk).elim
                         | succ k_pred =>
                           rw [hk] at hk_min
                           rw [orbit_succ]
                           apply le_trans (norm_fc_le_norm_sq_add_norm_c c (orbit c z k_pred))
                           gcongr
                           exact hk_min k_pred (Nat.lt_succ_self k_pred)
                   · apply Real.log_nonneg
                     apply le_max_left
               · exact dist_potential_seq_green_function_le_of_escaping c z k hk_gt
            _ ≤ (1/2^n * Real.log B) + (1/2^n * Real.log (B^2 + ‖c‖)) + (1/2^n * M) := by
               apply add_le_add
               · apply add_le_add
                 · apply le_refl _
                 · apply mul_le_mul_of_nonneg_right
                   · apply one_div_le_one_div_of_le
                     · apply pow_pos (by norm_num)
                     · gcongr; try norm_num; try exact le_of_lt h_nk
                   · apply Real.log_nonneg h_B2_c_ge_1
               · apply mul_le_mul_of_nonneg_right
                 · apply one_div_le_one_div_of_le
                   · apply pow_pos (by norm_num)
                   · gcongr; try norm_num; try exact le_of_lt h_nk
                 · apply div_nonneg (mul_nonneg zero_le_two (norm_nonneg c)) (pow_nonneg (le_trans zero_le_one h_B_ge_1) 2)
            _ = (1/2^n) * C := by dsimp [C]; ring
        
        · have hn_gt : ‖orbit c z n‖ > B := norm_orbit_gt_escape_bound_of_ge c z k n (not_lt.mp h_nk) hk_gt
          rw [dist_comm]
          apply le_trans (dist_potential_seq_green_function_le_of_escaping c z n hn_gt)
          dsimp [C]
          rw [← one_div_pow]
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : 0 ≤ (1/2:ℝ)) n)
          apply le_add_of_nonneg_left
          apply add_nonneg <;> apply Real.log_nonneg
          · exact h_B_ge_1
          · exact h_B2_c_ge_1

      · push_neg at h_esc
        have hK : z ∈ K c := by
          dsimp [K, boundedOrbit]
          exact ⟨B, h_esc⟩
        rw [← green_function_eq_zero_iff_mem_K] at hK
        rw [hK]
        rw [dist_zero_left]
        rw [potential_seq]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
        dsimp [C]
        gcongr
        -- Manual proof of log bound
        trans Real.log B
        · rw [abs_of_nonneg (Real.log_nonneg (le_max_left 1 _))]
          apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left 1 _))
          apply max_le h_B_ge_1 (h_esc n)
        · rw [add_assoc]
          apply le_add_of_nonneg_right
          apply add_nonneg (Real.log_nonneg h_B2_c_ge_1) (by positivity)

    calc dist (green_function c z) (potential_seq c z n)
      _ ≤ (1 / 2 ^ n) * C := h_bound
      _ ≤ (1 / 2 ^ N) * C := by 
         refine mul_le_mul_of_nonneg_right ?_ h_C_nonneg
         gcongr; try norm_num; try exact hn
      _ < ε := by
        have h_pos : 0 < C + 1 := add_pos_of_nonneg_of_pos h_C_nonneg zero_lt_one
        rw [lt_div_iff₀ h_pos] at hN
        apply lt_of_le_of_lt _ hN
        rw [← one_div_pow]
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : 0 ≤ (1/2:ℝ)) N)
        · linarith

  exact TendstoUniformly.continuous h_unif (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun n => continuous_potential_seq c n)))



end

end MLC.Quadratic