import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Escape

namespace MLC.Quadratic

open scoped Complex
open Complex Topology Filter Real

noncomputable section

lemma log_ge_one_sub_inv {x : ℝ} (hx : 0 < x) : Real.log x ≥ 1 - 1/x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  rw [inv_eq_one_div] at h
  linarith

lemma abs_log_le_two_mul_abs_sub_one {x : ℝ} (hx : 0.5 ≤ x) : |Real.log x| ≤ 2 * |x - 1| := by
  by_cases h1 : 1 ≤ x
  · rw [abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (sub_nonneg.mpr h1)]
    apply le_trans (Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num) h1))
    linarith
  · push_neg at h1
    rw [abs_of_neg (Real.log_neg (by linarith) h1), abs_of_neg (sub_neg.mpr h1)]
    have h_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx
    have h_log : Real.log x ≥ 1 - 1/x := log_ge_one_sub_inv h_pos
    rw [neg_sub]
    have h_ineq : 1 - 1/x ≥ 2 * x - 2 := by
      rw [ge_iff_le]
      rw [← mul_le_mul_iff_left₀ h_pos]
      rw [sub_mul]
      field_simp [h_pos.ne']
      have h_sub_neg : x - 1 < 0 := by linarith
      nth_rw 2 [← one_mul (x - 1)]
      rw [mul_le_mul_right_of_neg h_sub_neg]
      linarith
    linarith

variable {c z : ℂ}

/-- A bound used to ensure the orbit is large enough for the log approximation. -/
def escape_bound (c : ℂ) : ℝ := max (R c) (Real.sqrt (2 * ‖c‖ + 1))

lemma escape_bound_ge_R (c : ℂ) : R c ≤ escape_bound c := le_max_left _ _

lemma escape_bound_sq_ge (c : ℂ) : 2 * ‖c‖ + 1 ≤ (escape_bound c)^2 := by
  have h_nonneg : 0 ≤ 2 * ‖c‖ + 1 := by positivity
  have h_sqrt : Real.sqrt (2 * ‖c‖ + 1) ≤ escape_bound c := le_max_right _ _
  rw [Real.sqrt_le_iff] at h_sqrt
  exact h_sqrt.2

lemma norm_orbit_succ_div_sq_eq (c z : ℂ) (n : ℕ) (h_zn_pos : 0 < ‖orbit c z n‖) :
    ‖orbit c z (n + 1)‖ / ‖orbit c z n‖^2 = ‖1 + c / (orbit c z n)^2‖ := by
  let zn := orbit c z n
  let zn1 := orbit c z (n + 1)
  have h_zn1_eq : zn1 = zn^2 + c := by
    dsimp [zn1, zn]
    rw [orbit_succ, fc]
  change ‖zn1‖ / ‖zn‖^2 = _
  rw [h_zn1_eq]
  have h_zn_sq_ne_zero : zn^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mp (ne_of_gt h_zn_pos))
  rw [div_eq_iff (ne_of_gt (pow_pos h_zn_pos 2))]
  rw [← norm_pow]
  rw [← norm_mul]
  congr
  rw [add_mul, one_mul, div_mul_cancel₀ _ h_zn_sq_ne_zero, add_comm]

lemma norm_u_le_half (c z : ℂ) (n : ℕ) (h : ‖orbit c z n‖ > escape_bound c) :
    ‖c / (orbit c z n)^2‖ ≤ 1/2 := by
  let zn := orbit c z n
  have h_zn : ‖zn‖ > escape_bound c := h
  have h_R : R c ≥ 2 := R_ge_two c
  have h_esc : escape_bound c ≥ R c := escape_bound_ge_R c
  have h_zn_gt_2 : ‖zn‖ > 2 := lt_of_le_of_lt (le_trans h_R h_esc) h_zn
  have h_zn_pos : 0 < ‖zn‖ := lt_trans zero_lt_two h_zn_gt_2
  
  rw [norm_div, norm_pow]
  rw [div_le_iff₀ (pow_pos h_zn_pos 2)]
  rw [← mul_le_mul_iff_right₀ (by norm_num : (0:ℝ) < 2)]
  field_simp
  have h_le : 2 * ‖c‖ ≤ 2 * ‖c‖ + 1 := le_add_of_nonneg_right zero_le_one
  apply le_trans h_le
  apply le_trans (escape_bound_sq_ge c)
  apply le_of_lt
  gcongr
  apply le_trans (Real.sqrt_nonneg _) (le_max_right _ _)

lemma log_bound_helper (u : ℂ) (hu : ‖u‖ ≤ 1/2) :
    |Real.log ‖1 + u‖| ≤ 2 * ‖u‖ := by
  apply le_trans (abs_log_le_two_mul_abs_sub_one _)
  · rw [mul_le_mul_iff_right₀ (by norm_num : (0:ℝ) < 2)]
    rw [abs_le]
    constructor
    · rw [neg_le_sub_iff_le_add]
      have := norm_sub_norm_le 1 (-u)
      simp at this
      linarith
    · rw [sub_le_iff_le_add]
      have := norm_add_le 1 u
      simp at this
      linarith
  · have := norm_sub_norm_le 1 (-u)
    simp at this
    linarith

lemma pow_le_pow_left_of_le {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hxy : x ≤ y) : x^n ≤ y^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    rw [mul_comm (x^n), mul_comm (y^n)]
    apply mul_le_mul hxy ih (pow_nonneg hx n) (le_trans hx hxy)

lemma log_orbit_diff_le (c z : ℂ) (n : ℕ) (h : ‖orbit c z n‖ > escape_bound c) :
    |Real.log ‖orbit c z (n + 1)‖ - 2 * Real.log ‖orbit c z n‖| ≤ 2 * ‖c‖ / ‖orbit c z n‖^2 := by
  let zn := orbit c z n
  let zn1 := orbit c z (n + 1)
  have h_zn : ‖zn‖ > escape_bound c := h
  have h_R : R c ≥ 2 := R_ge_two c
  have h_esc : escape_bound c ≥ R c := escape_bound_ge_R c
  have h_zn_gt_2 : ‖zn‖ > 2 := lt_of_le_of_lt (le_trans h_R h_esc) h_zn
  have h_zn_pos : 0 < ‖zn‖ := lt_trans zero_lt_two h_zn_gt_2
  
  rw [show 2 * Real.log ‖zn‖ = Real.log (‖zn‖ ^ 2) by
    rw [Real.log_pow, Nat.cast_ofNat]
  ]
  
  have h_zn1_eq : zn1 = fc c zn := by
    dsimp [zn1, zn]
    rw [orbit_succ]

  have h_zn_sq_pos : 0 < ‖zn‖^2 := pow_pos h_zn_pos 2
  have h_zn1_pos : 0 < ‖zn1‖ := by
    rw [h_zn1_eq]
    have : ‖fc c zn‖ ≥ ‖zn‖^2 - ‖c‖ := norm_fc_ge_norm_sq_sub_norm_c c zn
    apply lt_of_lt_of_le _ this
    have : ‖c‖ < ‖zn‖^2 := by
      have h_esc_nonneg : 0 ≤ escape_bound c := le_trans (le_trans zero_le_two (R_ge_two c)) (escape_bound_ge_R c)
      have h_sq : (escape_bound c)^2 < ‖zn‖^2 := by gcongr
      have h_esc : 2 * ‖c‖ + 1 ≤ (escape_bound c)^2 := escape_bound_sq_ge c
      linarith
    linarith

  rw [← Real.log_div h_zn1_pos.ne' h_zn_sq_pos.ne']
  
  rw [norm_orbit_succ_div_sq_eq c z n h_zn_pos]
  
  let u := c / zn^2
  have h_u_norm : ‖u‖ = ‖c‖ / ‖zn‖^2 := by
    rw [norm_div, norm_pow]
  
  have h_u_le_half : ‖u‖ ≤ 1/2 := norm_u_le_half c z n h
  
  have h_log_bound : |Real.log ‖1 + u‖| ≤ 2 * ‖u‖ := log_bound_helper u h_u_le_half
  
  rw [h_u_norm] at h_log_bound
  rw [le_div_iff₀ (pow_pos h_zn_pos 2)]
  field_simp at h_log_bound
  exact h_log_bound

lemma escape_bound_eq_R (c : ℂ) : escape_bound c = R c := by
  rw [escape_bound]
  apply max_eq_left
  rw [R]
  have h : 1 + ‖c‖ ≥ Real.sqrt (2 * ‖c‖ + 1) := by
    rw [ge_iff_le, Real.sqrt_le_iff]
    constructor
    · positivity
    · have := norm_nonneg c
      nlinarith
  apply le_trans h
  apply le_max_right

lemma escape_bound_eq_max (c : ℂ) : escape_bound c = max 2 (1 + ‖c‖) := by
  rw [escape_bound_eq_R, R]

lemma escape_bound_sq_sub_norm_c_gt_escape_bound (c : ℂ) :
    (escape_bound c)^2 - ‖c‖ > escape_bound c := by
  rw [escape_bound_eq_max c]
  by_cases h : 1 + ‖c‖ ≤ 2
  · rw [max_eq_left h]
    have hc : ‖c‖ ≤ 1 := by linarith
    linarith
  · push_neg at h
    rw [max_eq_right (le_of_lt h)]
    have hc : ‖c‖ > 1 := by linarith
    nlinarith

lemma two_mul_norm_c_div_escape_bound_sq_le_half (c : ℂ) :
    2 * ‖c‖ / (escape_bound c)^2 ≤ 1/2 := by
  rw [escape_bound_eq_R]
  let x := ‖c‖
  have hx : 0 ≤ x := norm_nonneg c
  by_cases h1 : x ≤ 1
  · have hR : R c = 2 := by
      rw [R, max_eq_left]
      linarith
    rw [hR]
    field_simp
    linarith
  · push_neg at h1
    have hR : R c = 1 + x := by
      rw [R, max_eq_right]
      linarith
    rw [hR]
    rw [div_le_iff₀ (pow_pos (by linarith) 2)]
    linarith [sq_nonneg (1 - x)]

lemma log_escape_bound_gt_two_mul_norm_c_div_sq (c : ℂ) :
    Real.log (escape_bound c) > 2 * ‖c‖ / (escape_bound c)^2 := by
  apply lt_of_le_of_lt (two_mul_norm_c_div_escape_bound_sq_le_half c)
  have hB : escape_bound c ≥ 2 := le_trans (R_ge_two c) (escape_bound_ge_R c)
  apply lt_of_lt_of_le _ (Real.log_le_log (by norm_num) hB)
  rw [← Real.log_exp (1/2)]
  apply Real.log_lt_log (by positivity)
  have : Real.exp (1/2) < 2 ↔ (Real.exp (1/2))^2 < 2^2 := by
    rw [sq_lt_sq]
    rw [abs_of_pos (Real.exp_pos (1/2))]
    rw [abs_of_pos (by norm_num : 0 < (2:ℝ))]
  rw [this]
  rw [pow_two, ← Real.exp_add, add_halves]
  norm_num
  apply lt_trans Real.exp_one_lt_d9
  norm_num

/-- The n-th approximation of the Green's function: `1/2^n * log (max 1 ‖f_c^n(z)‖)`. -/
def potential_seq (c z : ℂ) (n : ℕ) : ℝ :=
  (1 / 2 ^ n) * Real.log (max 1 ‖orbit c z n‖)

lemma potential_seq_diff_le (c z : ℂ) (k : ℕ) (h_orbit : ‖orbit c z k‖ > escape_bound c) :
    dist (potential_seq c z k) (potential_seq c z (k + 1)) ≤ 
    (1 / 2 ^ (k + 1)) * (2 * ‖c‖ / (escape_bound c)^2) := by
  rw [dist_eq_norm, Real.norm_eq_abs]
  rw [potential_seq, potential_seq]
  have h_max_k : max 1 ‖orbit c z k‖ = ‖orbit c z k‖ := by
    rw [max_eq_right]
    apply le_trans (le_of_lt one_lt_two)
    apply le_trans (R_ge_two c)
    apply le_trans (escape_bound_ge_R c) (le_of_lt h_orbit)
  have h_max_k1 : max 1 ‖orbit c z (k + 1)‖ = ‖orbit c z (k + 1)‖ := by
    rw [max_eq_right]
    apply le_trans (le_of_lt one_lt_two)
    apply le_trans (R_ge_two c)
    apply le_trans (escape_bound_ge_R c)
    apply le_trans (le_of_lt h_orbit)
    have h_R : ‖orbit c z k‖ > R c := lt_of_le_of_lt (escape_bound_ge_R c) h_orbit
    have := norm_orbit_ge_of_norm_ge_R c (orbit c z k) 1 h_R
    rw [orbit_succ]
    exact this
  rw [h_max_k, h_max_k1]
  rw [pow_add, pow_one, one_div, inv_mul_eq_div, div_mul_eq_mul_div]
  rw [show Real.log ‖orbit c z k‖ / 2 ^ k = (2 * Real.log ‖orbit c z k‖) / (2 ^ k * 2) by
    field_simp
  ]
  rw [← sub_div, abs_div, abs_of_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (by norm_num : 0 ≤ (2:ℝ)))]
  rw [one_div_mul_eq_div]
  rw [div_le_div_iff_of_pos_right (mul_pos (pow_pos (by norm_num) k) (by norm_num : 0 < (2:ℝ)))]
  rw [one_mul]
  rw [abs_sub_comm]
  apply le_trans (log_orbit_diff_le c z k h_orbit)
  gcongr
  · apply pow_pos (lt_of_lt_of_le zero_lt_two (le_trans (R_ge_two c) (escape_bound_ge_R c))) 2
  · apply le_trans zero_le_two (le_trans (R_ge_two c) (escape_bound_ge_R c))

/-- The Green's function `G_c(z)`. Defined as the limit of `potential_seq`. -/
def green_function (c z : ℂ) : ℝ :=
  limUnder atTop (fun n => potential_seq c z n)

/-- Convergence of the potential sequence to 0 for `z ∈ K(c)`. -/
lemma potential_seq_converges_of_mem_K (h : z ∈ K c) :
    Tendsto (potential_seq c z) atTop (𝓝 0) := by
  rcases h with ⟨M, hM⟩
  let B := Real.log (max 1 M)
  have h_bound : ∀ n, |potential_seq c z n| ≤ (1 / 2 ^ n) * B := by
    intro n
    rw [potential_seq, abs_mul, abs_of_nonneg (by positivity)]
    gcongr
    rw [abs_of_nonneg (Real.log_nonneg (le_max_left 1 _))]
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left 1 _))
    apply max_le_max (le_refl 1) (hM n)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => -(1 / 2 ^ n * B))
    (h := fun n => 1 / 2 ^ n * B)
    _
    _
    (fun n => (abs_le.mp (h_bound n)).1)
    (fun n => (abs_le.mp (h_bound n)).2)
  · rw [← neg_zero]
    apply Tendsto.neg
    convert Filter.Tendsto.mul_const B (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) < 1))
    simp [one_div, inv_pow]
    ring
  · convert Filter.Tendsto.mul_const B (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) < 1))
    simp [one_div, inv_pow]
    ring

/-! ### Convergence for escaping points -/

/-- Convergence of the potential sequence for `z ∉ K(c)`. -/
lemma potential_seq_converges_of_escapes (h : z ∉ K c) :
    ∃ L, Tendsto (potential_seq c z) atTop (𝓝 L) := by
  dsimp [K, boundedOrbit] at h
  push_neg at h
  
  let B := escape_bound c
  obtain ⟨n0, hn0⟩ := h B
  have hn0_R : ‖orbit c z n0‖ > R c := lt_of_le_of_lt (escape_bound_ge_R c) hn0
  
  obtain ⟨N_large, h_growth⟩ := escape_lemma n0 hn0_R B
  
  refine cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist ?_)
  
  let a := potential_seq c z
  rw [← summable_nat_add_iff (n0 + N_large)]
  
  have h_bound : ∀ k, dist (a (k + (n0 + N_large))) (a (k + (n0 + N_large) + 1)) ≤ (1 / 2 ^ (k + (n0 + N_large) + 1)) * (2 * ‖c‖ / B^2) := by
    intro k
    let n := k + (n0 + N_large)
    have hn_B : ‖orbit c z n‖ > B := by
      apply h_growth
      dsimp [n]
      linarith
    exact potential_seq_diff_le c z n hn_B

  dsimp [a]
  refine Summable.of_nonneg_of_le (fun k => dist_nonneg) (fun k => h_bound k) ?_
  simp only [pow_add, one_div, mul_inv]
  have : ∀ i : ℕ, (2 ^ i : ℝ)⁻¹ = (2⁻¹) ^ i := fun i => by rw [inv_pow]
  simp_rw [this]
  apply Summable.mul_right
  apply Summable.mul_right
  apply Summable.mul_right
  apply summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-- Convergence of the potential sequence for all `z`. -/
lemma potential_seq_converges (c z : ℂ) :
    ∃ L, Tendsto (potential_seq c z) atTop (𝓝 L) := by
  by_cases h : z ∈ K c
  · use 0; exact potential_seq_converges_of_mem_K h
  · exact potential_seq_converges_of_escapes h

/-- `G_c(z)` equals the limit of the potential sequence. -/
lemma green_function_eq_lim (c z : ℂ) :
    Tendsto (potential_seq c z) atTop (𝓝 (green_function c z)) := by
  obtain ⟨L, hL⟩ := potential_seq_converges c z
  have h_eq : green_function c z = L := by
    rw [green_function, limUnder, lim]
    have h_ex : ∃ x, map (potential_seq c z) atTop ≤ 𝓝 x := ⟨L, hL⟩
    have h_spec := Classical.epsilon_spec h_ex
    exact (tendsto_nhds_unique hL h_spec).symm
  rw [h_eq]
  exact hL

end

end MLC.Quadratic