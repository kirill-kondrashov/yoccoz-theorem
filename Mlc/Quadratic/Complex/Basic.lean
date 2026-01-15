import Mathlib

/-!
# Quadratic family basics (Lyubich I–II notation)

We set up the quadratic family `f_c(z) = z^2 + c`, iterates, filled Julia set `K(c)`,
and Julia set `J(c) = ∂K(c)`. We also state (and stub) the standard escape and
compactness lemmas you’ll prove next.
-/

namespace MLC
namespace Quadratic

open scoped Complex
open Complex Topology Filter
noncomputable section

/-- The quadratic polynomial `f_c(z) = z^2 + c`. -/
def fc (c : ℂ) : ℂ → ℂ := fun z => z^2 + c

/-- The forward orbit of `z0` under `f_c`. -/
def orbit (c : ℂ) (z0 : ℂ) : ℕ → ℂ := fun n => (Nat.iterate (fc c) n) z0

@[simp] lemma orbit_zero (c z : ℂ) : orbit c z 0 = z := rfl

@[simp] lemma orbit_succ (c z : ℂ) (n : ℕ) :
    orbit c z (n+1) = fc c (orbit c z n) := by
  -- `Function.iterate_succ : iterate f (n+1) = iterate f n ∘ f`
  simpa [orbit, Function.comp] using
    congrArg (fun g => g z) (Function.iterate_succ' (fc c) n)

/-- Boundedness of an orbit. -/
def boundedOrbit (c z : ℂ) : Prop :=
  ∃ M : ℝ, ∀ n, ‖orbit c z n‖ ≤ M

/-- Filled Julia set. -/
def K (c : ℂ) : Set ℂ := { z | boundedOrbit c z }

/-- Julia set as the topological boundary of `K(c)`. -/
def J (c : ℂ) : Set ℂ := frontier (K c)

/-- The Mandelbrot set is the set of parameters `c` for which the orbit of `0` is bounded. -/
def MandelbrotSet : Set ℂ := { c | boundedOrbit c 0 }

/-! ## Elementary norm facts -/

@[simp] lemma norm_sq (z : ℂ) : ‖z^2‖ = ‖z‖^2 := by
  -- ‖z^2‖ = ‖z‖ * ‖z‖ and `‖z‖^2` is `(‖z‖)^2`.
  simp [pow_two]

/-- A convenient escape radius depending on `‖c‖`. -/
def R (c : ℂ) : ℝ := max 2 (1 + ‖c‖)

@[simp] lemma R_ge_two (c : ℂ) : R c ≥ 2 := by simp [R]
@[simp] lemma R_ge_one_plus_c (c : ℂ) : R c ≥ 1 + ‖c‖ := by simp [R]

/-- The Mandelbrot set is connected.
    See: [Douady and Hubbard, Etude dynamique des polynômes complexes, 1984, Theorem 1, Chapter VIII] <https://pi.math.cornell.edu/~hubbard/OrsayEnglish.pdf> (p. 47) -/
axiom mandelbrot_set_connected : IsConnected MandelbrotSet

/-- The filled Julia set is connected if c is in the Mandelbrot set.
    See: [Douady and Hubbard, Etude dynamique des polynômes complexes, 1984, Proposition 1, Chapter VIII] <https://pi.math.cornell.edu/~hubbard/OrsayEnglish.pdf> (p. 47) -/
axiom filled_julia_set_connected {c : ℂ} (h : c ∈ MandelbrotSet) : IsConnected (K c)

end

end Quadratic
end MLC
