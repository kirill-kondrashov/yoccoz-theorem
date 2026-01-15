import Yoccoz.Quadratic.Complex.Basic

/-!
# Escape Lemma for the Quadratic Family

This file proves the escape lemma: if the orbit of a point ever leaves the disk of
radius `R(c)`, then it escapes to infinity.

Reference: "Conformal Geometry and Dynamics of Quadratic Polynomials",
https://indico.ictp.it/event/a12182/session/2/contribution/1/material/0/0.pdf
(See Section 21.2, p. 125 for the escape lemma)

## Connection to MLC

The escape lemma is the foundational result for the construction of Yoccoz puzzles,
which are central to the proof of the Mandelbrot Local Connectivity (MLC) conjecture.

1.  **Basin of Infinity**: It establishes that the basin of attraction of infinity,
    $A(\infty) = \{z \mid f_c^n(z) \to \infty\}$, contains the complement of the disk $D(0, R(c))$.
2.  **Green's Function**: This allows defining the Green's function $G(z) = \lim \frac{1}{2^n} \log|f_c^n(z)|$
    for $z \in A(\infty)$.
3.  **Böttcher Coordinates**: The Green's function is used to construct the Böttcher coordinate
    $\phi_c(z)$ near infinity, which conjugates $f_c$ to $z \mapsto z^2$.
4.  **Rays and Equipotentials**: The level sets of $G(z)$ (equipotentials) and the gradient lines
    of $G(z)$ (external rays) form the grid for the Yoccoz puzzle partition.

Thus, this lemma justifies the existence of the dynamical plane structures required for the
combinatorial analysis in the MLC proof.
-/

namespace MLC.Quadratic

open scoped Complex
open Complex Topology Filter Real

noncomputable section

variable {c z : ℂ}

lemma norm_sq_sub_norm_c_ge (c z : ℂ) : ‖z^2‖ - ‖c‖ ≥ ‖z‖^2 - (R c - 1) := by
  simp only [norm_sq]
  linarith [R_ge_one_plus_c c]

lemma norm_growth (c z : ℂ) : ‖fc c z‖ ≥ ‖z‖^2 - (R c - 1) := by
  rw [fc]
  have h_tri : ‖z^2 + c‖ ≥ ‖z^2‖ - ‖c‖ := by
    have := norm_add_le (z^2 + c) (-c)
    simp only [add_neg_cancel_right, norm_neg] at this
    linarith
  rw [norm_sq] at h_tri
  linarith [R_ge_one_plus_c c]

lemma norm_fc_ge_norm_sq_sub_norm_c (c z : ℂ) : ‖fc c z‖ ≥ ‖z‖^2 - ‖c‖ := by
  rw [fc]
  have := norm_add_le (z^2 + c) (-c)
  simp only [add_neg_cancel_right, norm_neg] at this
  rw [norm_sq] at this
  linarith

lemma sub_div_mono (c : ℂ) : StrictMonoOn (fun x : ℝ => x - ‖c‖ / x) (Set.Ioi 0) := by
  intro x hx y _ hxy
  dsimp
  apply add_lt_add_of_lt_of_le hxy
  rw [neg_le_neg_iff]
  apply div_le_div_of_nonneg_left (norm_nonneg c) hx (le_of_lt hxy)

lemma factor_gt_one (c z : ℂ) (h : ‖z‖ > R c) : ‖z‖ - ‖c‖ / ‖z‖ > 1 := by
  have R_pos : R c > 0 := by linarith [R_ge_two c]
  have z_pos : ‖z‖ > 0 := by linarith
  have key : ‖z‖ - ‖c‖ / ‖z‖ > R c - ‖c‖ / R c := sub_div_mono c R_pos z_pos h
  have R_ge : R c - ‖c‖ / R c ≥ 1 := by
    have hR2 : R c ≥ 2 := R_ge_two c
    have hRc : R c ≥ 1 + ‖c‖ := R_ge_one_plus_c c
    rw [ge_iff_le, le_sub_iff_add_le, add_comm 1, ← le_sub_iff_add_le]
    rw [div_le_iff₀ R_pos]
    have h_calc := calc
      ‖c‖ = 1 * ‖c‖ := by simp
      _ ≤ (R c - 1) * (R c - 1) := by
        nlinarith
      _ ≤ (R c - 1) * R c := by
        apply mul_le_mul_of_nonneg_left
        · linarith
        · linarith
      _ = R c * R c - R c := by ring
    linarith
  linarith

lemma R_pos (c : ℂ) : R c > 0 := by
  have := R_ge_two c
  linarith

/-- Escape lemma: if the orbit of z ever leaves the disk of radius R(c), then it
escapes to infinity.

Proof idea:
We define a 'growth factor' `λ(w) = |w| - |c|/|w|`.
We show that if `|w| > R(c)`, then `λ(w) > 1`.
We then prove by induction that `|f_c^k(w)| ≥ |w| * λ(w)^k`.
Since `λ(w) > 1`, the term `λ(w)^k` grows to infinity, so the orbit norm grows unbounded. -/
lemma escape_lemma (n : ℕ) (h : ‖orbit c z n‖ > R c) :
    ∀ M : ℝ, ∃ N : ℕ, ∀ m ≥ N, ‖orbit c z m‖ > M := by
  let w := orbit c z n
  let lam := ‖w‖ - ‖c‖ / ‖w‖
  have hlam : lam > 1 := factor_gt_one c w h
  have hw_pos : ‖w‖ > 0 := lt_trans (R_pos c) h

  have growth : ∀ k, ‖orbit c w k‖ ≥ ‖w‖ * lam ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      let z_k := orbit c w k
      have h_zk_ge : ‖z_k‖ ≥ ‖w‖ := by
        calc ‖z_k‖ ≥ ‖w‖ * lam ^ k := ih
          _ ≥ ‖w‖ * 1 := by
            gcongr
            exact one_le_pow₀ (le_of_lt hlam)
          _ = ‖w‖ := by simp

      have h_zk_pos : ‖z_k‖ > 0 := lt_of_lt_of_le hw_pos h_zk_ge

      calc ‖orbit c w (k + 1)‖
        _ = ‖fc c z_k‖ := by rw [orbit_succ]
        _ ≥ ‖z_k‖^2 - ‖c‖ := norm_fc_ge_norm_sq_sub_norm_c c z_k
        _ = ‖z_k‖ * (‖z_k‖ - ‖c‖ / ‖z_k‖) := by field_simp [h_zk_pos.ne']
        _ ≥ ‖z_k‖ * lam := by
          gcongr
          apply (sub_div_mono c).monotoneOn
          · exact hw_pos
          · exact h_zk_pos
          · exact h_zk_ge
        _ ≥ (‖w‖ * lam ^ k) * lam := by
          apply mul_le_mul_of_nonneg_right ih
          exact le_of_lt (lt_trans zero_lt_one hlam)
        _ = ‖w‖ * lam ^ (k + 1) := by
          rw [pow_succ]
          ring

  intro M
  have h_tendsto : Tendsto (fun k => ‖w‖ * lam ^ k) atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hw_pos
    apply tendsto_pow_atTop_atTop_of_one_lt hlam

  rcases (Filter.tendsto_atTop_atTop.mp h_tendsto) (M + 1) with ⟨N0, hN0⟩
  use n + N0
  intro m hm
  let k := m - n
  have hnm : n ≤ m := le_trans (Nat.le_add_right n N0) hm
  have hk : m = n + k := (Nat.add_sub_of_le hnm).symm
  rw [hk, add_comm]
  dsimp [orbit]
  rw [Function.iterate_add_apply]
  have hm' : N0 + n ≤ m := by rwa [add_comm]
  specialize hN0 k (Nat.le_sub_of_add_le hm')
  calc ‖orbit c w k‖ ≥ ‖w‖ * lam ^ k := growth k
    _ ≥ M + 1 := hN0
    _ > M := lt_add_one M

lemma norm_orbit_ge_of_norm_ge_R (c z : ℂ) (n : ℕ) (h : ‖z‖ > R c) :
    ‖orbit c z n‖ ≥ ‖z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_n : ‖orbit c z n‖ ≥ ‖z‖ := ih
    have h_n_R : ‖orbit c z n‖ > R c := lt_of_lt_of_le h h_n
    rw [orbit_succ]
    have : ‖fc c (orbit c z n)‖ ≥ ‖orbit c z n‖^2 - ‖c‖ := norm_fc_ge_norm_sq_sub_norm_c c _
    apply le_trans h_n
    apply le_trans _ this
    have h_zn : ‖orbit c z n‖ > R c := h_n_R
    have h_R : R c ≥ 1 + ‖c‖ := R_ge_one_plus_c c
    have h_R2 : R c ≥ 2 := R_ge_two c
    have h_zn_gt_1 : ‖orbit c z n‖ > 1 := lt_of_le_of_lt (by linarith) h_zn
    have h_zn_sub_1 : ‖orbit c z n‖ - 1 > ‖c‖ := by linarith
    have : ‖orbit c z n‖ * (‖orbit c z n‖ - 1) > 1 * ‖c‖ := by
      by_cases hc : ‖c‖ = 0
      · rw [hc, mul_zero]
        apply mul_pos
        · linarith
        · linarith
      · have h_calc : 1 * ‖c‖ < ‖orbit c z n‖ * (‖orbit c z n‖ - 1) := calc
          1 * ‖c‖ < 1 * (‖orbit c z n‖ - 1) := by
            gcongr
          _ < ‖orbit c z n‖ * (‖orbit c z n‖ - 1) := by
            apply mul_lt_mul_of_pos_right
            · exact h_zn_gt_1
            · linarith
        exact h_calc
    rw [one_mul] at this
    rw [mul_sub, mul_one] at this
    linarith

end

end MLC.Quadratic
