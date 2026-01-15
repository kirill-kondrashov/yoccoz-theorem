import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Groetzsch
import Yoccoz.Quadratic.Complex.Green
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

namespace MLC.Quadratic

open Complex Topology Filter Set

noncomputable section

variable (c : ℂ)

/-- The dynamical puzzle piece of depth n containing z.
    Definition: The connected component of `{z | G(z) < 1/2^n}` containing `z`.
    These pieces form the basis of the Yoccoz puzzle construction. -/
def DynamicalPuzzlePiece (c : ℂ) (n : ℕ) (z : ℂ) : Set ℂ :=
  connectedComponentIn {w | green_function c w < (1 / 2) ^ n} z

/-- The annulus between two nested puzzle pieces around the critical point.
    Definition: The annulus between two nested puzzle pieces `P_n \ P_{n+1}`.
    The sum of their moduli determines renormalizability. -/
def PuzzleAnnulus (c : ℂ) (n : ℕ) : Set ℂ :=
  DynamicalPuzzlePiece c n 0 \ DynamicalPuzzlePiece c (n + 1) 0

/-- A para-puzzle piece in the parameter plane.
    Definition: The set of parameters `c` for which the critical point 0 lies in the
    dynamical puzzle piece of depth `n`. -/
def ParaPuzzlePiece (n : ℕ) : Set ℂ := {c | c ∈ DynamicalPuzzlePiece c n 0}

end

end MLC.Quadratic
