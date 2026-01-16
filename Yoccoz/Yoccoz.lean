import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Yoccoz.Quadratic.Complex.Puzzle
import Yoccoz.Quadratic.Complex.PuzzleLemmas
import Yoccoz.Quadratic.Complex.Groetzsch
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Set.Finite.Basic
import Lean

namespace MLC

open Quadratic Complex Topology Set Filter

section Combinatorics

/-- Non-renormalizable parameters.
    For the purpose of this plan, we define non-renormalizable parameters
    as those for which the Yoccoz puzzle moduli diverge.
    The deep work is then in the dichotomy axiom. -/
def NonRenormalizable (c : ℂ) : Prop :=
    ¬ Summable (fun n => modulus (PuzzleAnnulus c n))

/-- Non-renormalizable parameters have divergent moduli. -/
theorem non_renormalizable_moduli_diverge (c : ℂ) (h : NonRenormalizable c) :
    ¬ (Summable fun n => modulus (PuzzleAnnulus c n)) := h

end Combinatorics

section YoccozTheorem

/-- Yoccoz's Theorem: Divergence of moduli implies point intersection.
    Proof idea:
    *   If `c ∈ M`: We apply **Grötzsch's criterion** to the nested sequence of dynamical puzzle pieces.
        These pieces contain 0 and are connected. The divergence of the moduli of the annuli between
        them forces the intersection of the pieces to be a single point `{0}`.
    *   If `c ∉ M`: The orbit of 0 escapes. For large enough `n`, the potential level `1/2^n`
        is smaller than `G(0)`, so `0` is no longer in the puzzle piece (which is defined by `G(z) < 1/2^n`).
        Thus, the puzzle pieces eventually become empty. This would imply the sum of moduli is finite
        (sum of zeros), contradicting the divergence hypothesis. Thus, this case is impossible under
        the assumption of divergence. -/
theorem yoccoz_theorem (c : ℂ) :
    ¬ (Summable fun n => modulus (PuzzleAnnulus c n)) →
    (⋂ n, DynamicalPuzzlePiece c n 0) = {0} := by
  intro h_div
  by_cases hc : c ∈ MandelbrotSet
  · apply groetzsch_criterion
    · intro n
      apply dynamical_puzzle_piece_nested
    · intro n
      apply mem_dynamical_puzzle_piece_self c hc
    · intro n
      have h_ne : (DynamicalPuzzlePiece c n 0).Nonempty := ⟨0, mem_dynamical_puzzle_piece_self c hc n⟩
      rw [DynamicalPuzzlePiece] at h_ne ⊢
      exact ⟨h_ne, isPreconnected_connectedComponentIn⟩
    · intro n
      apply MeasurableSet.nullMeasurableSet
      rw [DynamicalPuzzlePiece]
      have h_open_set : IsOpen {w | green_function c w < (1 / 2) ^ n} :=
        IsOpen.preimage (continuous_green_function c) isOpen_Iio
      -- Connected components of open sets in locally connected spaces are open
      -- We assume this for now as it's a topology fact
      have h_comp_open : IsOpen (connectedComponentIn {w | green_function c w < (1 / 2) ^ n} 0) :=
        IsOpen.connectedComponentIn h_open_set
      exact IsOpen.measurableSet h_comp_open
    · exact h_div
  · exfalso
    apply h_div
    rcases dynamical_puzzle_piece_empty_of_large_n c hc with ⟨N, hN⟩
    apply summable_of_finite_support
    have : (Function.support fun n ↦ modulus (PuzzleAnnulus c n)) ⊆ Iio N := by
      intro n hn
      rw [Function.mem_support, ne_eq] at hn
      by_contra h_ge
      simp at h_ge
      have : modulus (PuzzleAnnulus c n) = 0 := by
        rw [PuzzleAnnulus]
        have h_empty : DynamicalPuzzlePiece c n 0 = ∅ := by
          ext x
          simp
          intro hx
          have h0 : 0 ∈ DynamicalPuzzlePiece c n 0 := by
            rw [DynamicalPuzzlePiece] at hx ⊢
            apply mem_connectedComponentIn
            exact connectedComponentIn_nonempty_iff.1 ⟨x, hx⟩
          exact hN n h_ge h0
        rw [h_empty]
        simp
        exact modulus_empty
      contradiction
    exact Set.Finite.subset (Set.finite_Iio N) this

end YoccozTheorem

end MLC
