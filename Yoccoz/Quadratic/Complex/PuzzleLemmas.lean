import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Yoccoz.Quadratic.Complex.Puzzle

namespace MLC.Quadratic

open Complex Topology Filter Set

noncomputable section

variable (c : ℂ)

theorem dynamical_puzzle_piece_nested (c : ℂ) (n : ℕ) :
    DynamicalPuzzlePiece c (n + 1) 0 ⊆ DynamicalPuzzlePiece c n 0 := by
  apply connectedComponentIn_mono
  intro w hw
  dsimp at *
  -- Proof idea: The level sets are defined by `G(w) < 1/2^n`.
  -- Since `1/2^{n+1} < 1/2^n`, the set for `n+1` is contained in the set for `n`.
  -- Connected component of a subset is contained in the connected component of the superset.
  apply lt_trans hw
  rw [pow_succ]
  nth_rw 2 [← one_mul ((1 / 2 : ℝ) ^ n)]
  rw [mul_comm]
  apply mul_lt_mul_of_pos_right
  · norm_num
  · apply pow_pos
    norm_num

theorem mem_dynamical_puzzle_piece_self (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ) :
    0 ∈ DynamicalPuzzlePiece c n 0 := by
  -- Proof idea: Since `c ∈ M`, `0 ∈ K(c)`.
  -- Points in `K(c)` have Green's function 0.
  -- Since `0 < 1/2^n`, `0` satisfies the condition `G(0) < 1/2^n`.
  -- Thus `0` is in the connected component of the level set containing `0`.
  have h0 : 0 ∈ K c := hc
  rw [← green_function_eq_zero_iff_mem_K] at h0
  dsimp [DynamicalPuzzlePiece]
  apply mem_connectedComponentIn
  change green_function c 0 < (1 / 2) ^ n
  rw [h0]
  apply pow_pos
  norm_num

theorem dynamical_puzzle_piece_empty_of_large_n (c : ℂ) (hc : c ∉ MandelbrotSet) :
    ∃ N, ∀ n ≥ N, 0 ∉ DynamicalPuzzlePiece c n 0 := by
  -- Proof idea: If `c ∉ M`, then `0 ∉ K(c)`, so `G(0) > 0`.
  -- Since `1/2^n → 0`, eventually `1/2^n < G(0)`.
  -- At that point, `0` is no longer in the set `{w | G(w) < 1/2^n}`.
  have h_not_in_K : 0 ∉ K c := hc
  rw [← green_function_pos_iff_not_mem_K] at h_not_in_K
  have h_pos : 0 < green_function c 0 := h_not_in_K

  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < green_function c 0 := by
    have h_tendsto : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      apply tendsto_pow_atTop_nhds_zero_of_lt_one
      · norm_num
      · norm_num
    exact ((tendsto_order.1 h_tendsto).2 (green_function c 0) h_pos).exists

  use N
  intro n hn
  dsimp [DynamicalPuzzlePiece]
  intro h_mem
  have h_in_set : 0 ∈ {w | green_function c w < (1 / 2) ^ n} :=
    (connectedComponentIn_subset {w | green_function c w < (1 / 2) ^ n} 0) h_mem
  rw [mem_setOf_eq] at h_in_set
  have h_le : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N := by
    apply pow_le_pow_of_le_one
    · norm_num
    · norm_num
    · exact hn
  have h_lt : (1 / 2 : ℝ) ^ n < green_function c 0 :=
    lt_of_le_of_lt h_le hN
  linarith

end

end MLC.Quadratic
