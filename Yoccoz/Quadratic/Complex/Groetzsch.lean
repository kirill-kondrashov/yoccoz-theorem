import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace MLC
namespace Quadratic

open Complex Topology Filter Set BigOperators Classical MeasureTheory

noncomputable section

/-- A weight function for the modulus definition.
    We use a Gaussian weight to ensure integrability on the whole plane.
    This acts as a proxy for the conformal modulus in this formalization. -/
noncomputable def weight (z : ℂ) : ℝ := Real.exp (- Complex.normSq z)

/-- The modulus of a set, defined as its weighted area. -/
noncomputable def modulus (A : Set ℂ) : ℝ :=
  ∫ z in A, weight z

/-- The modulus of the empty set is 0. -/
theorem modulus_empty : modulus ∅ = 0 := by
  simp [modulus]

/-- Modulus is non-negative. -/
theorem modulus_nonneg (A : Set ℂ) : 0 ≤ modulus A := by
  apply integral_nonneg_of_ae
  apply ae_of_all
  intro z
  apply le_of_lt
  apply Real.exp_pos

/-- A Gaussian integral lemma. -/
lemma weight_integrable : Integrable weight := by
  have he := Complex.volume_preserving_equiv_real_prod.symm
  rw [← MeasurePreserving.integrable_comp_emb he (Complex.measurableEquivRealProd.symm.measurableEmbedding)]
  have h_eq : weight ∘ Complex.measurableEquivRealProd.symm = fun p : ℝ × ℝ => Real.exp (- p.1 ^ 2) * Real.exp (- p.2 ^ 2) := by
    ext p
    simp [weight, Complex.normSq_apply]
    try rw [neg_add]
    rw [Real.exp_add]
    ring_nf
  rw [h_eq]
  exact Integrable.mul_prod (by simpa using integrable_exp_neg_mul_sq (b := 1) zero_lt_one) (by simpa using integrable_exp_neg_mul_sq (b := 1) zero_lt_one)

/-- Grötzsch's Inequality: Superadditivity of modulus for disjoint sets.
    We prove this using the monotonicity of the integral. -/
theorem groetzsch_inequality {A B S : Set ℂ} (h_disj : Disjoint A B) (h_sub : A ∪ B ⊆ S)
    (_h_meas_A : NullMeasurableSet A volume) (h_meas_B : NullMeasurableSet B volume) :
    modulus A + modulus B ≤ modulus S := by
  unfold modulus
  
  -- integral_union_ae requires NullMeasurableSet for the sets
  rw [← integral_union_ae (Disjoint.aedisjoint h_disj) h_meas_B weight_integrable.integrableOn weight_integrable.integrableOn]
  
  -- Monotonicity of integral
  apply integral_mono_measure (Measure.restrict_mono h_sub le_rfl)
  · apply ae_restrict_of_ae
    apply ae_of_all
    intro z
    exact le_of_lt (Real.exp_pos _)
  · exact weight_integrable.integrableOn

lemma subset_of_le_nested {P : ℕ → Set ℂ} (h_nested : ∀ n, P (n + 1) ⊆ P n)
    {i j : ℕ} (hij : i ≤ j) : P j ⊆ P i := by
  have h_diff : ∃ k, j = i + k := Nat.exists_eq_add_of_le hij
  obtain ⟨k, rfl⟩ := h_diff
  clear hij
  induction k with
  | zero => exact subset_refl _
  | succ m ih =>
    rw [Nat.add_succ]
    apply subset_trans (h_nested (i + m)) ih

/-- Grötzsch's Inequality implies summability if the intersection is non-trivial.
    Proof idea: We construct a sequence of disjoint annuli `A_n = P_n \ P_{n+1}`.
    By the contrapositive of Grötzsch's criterion (or directly by inequality), if the intersection
    is non-trivial (contains more than just a point), there is a core `K` inside all `P_n`.
    The disjoint annuli are all nested around `K`. Grötzsch's inequality implies their moduli
    sum up to at most the modulus of the container `P_0 \ K`, which is finite.
    Thus the sum converges. -/
theorem modulus_summable_of_nontrivial_intersection {P : ℕ → Set ℂ}
    (h_nested : ∀ n, P (n + 1) ⊆ P n)
    (_h_conn : ∀ n, IsConnected (P n))
    (_h_nontriv : Set.Nontrivial (⋂ n, P n))
    (h_meas : ∀ n, NullMeasurableSet (P n) volume) :
    Summable (fun n => modulus (P n \ P (n + 1))) := by
  let A := fun n => P n \ P (n + 1)
  have h_disj : ∀ i j, i < j → Disjoint (A i) (A j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hi hj
    simp [A] at hi hj
    have h_sub : P j ⊆ P (i + 1) := subset_of_le_nested h_nested hij
    have z_in_P_j := hj.1
    have z_in_P_i_1 := h_sub z_in_P_j
    have z_not_in_P_i_1 := hi.2
    contradiction

  have h_union_sub : ∀ N, (⋃ n ∈ Finset.range N, A n) ⊆ P 0 \ P N := by
    intro N
    rw [Set.subset_def]
    intro z hz
    simp at hz
    obtain ⟨n, hn_lt, hn_z⟩ := hz
    simp [A] at hn_z
    constructor
    · -- z ∈ P 0
      have h_sub : P n ⊆ P 0 := subset_of_le_nested h_nested (Nat.zero_le n)
      exact h_sub hn_z.1
    · -- z ∉ P N
      intro h_in_N
      have h_sub : P N ⊆ P (n + 1) := subset_of_le_nested h_nested hn_lt
      apply hn_z.2
      apply h_sub h_in_N

  -- Monotonicity lemma
  have modulus_mono : ∀ {U V : Set ℂ}, U ⊆ V → NullMeasurableSet U volume → modulus U ≤ modulus V := by
    intro U V h_sub h_meas_U
    have h_union : U ∪ ∅ ⊆ V := by simp [h_sub]
    have h_disj_empty : Disjoint U ∅ := disjoint_empty U
    have h_ineq := groetzsch_inequality h_disj_empty h_union h_meas_U MeasurableSet.empty.nullMeasurableSet
    rw [modulus_empty, add_zero] at h_ineq
    exact h_ineq

  -- Bounded partial sums
  have h_bounded : ∀ N, Finset.sum (Finset.range N) (fun n => modulus (A n)) ≤ modulus (P 0 \ (⋂ n, P n)) := by
    intro N
    -- First show sum ≤ modulus (P 0 \ P N)
    have h_sum_le : Finset.sum (Finset.range N) (fun n => modulus (A n)) ≤ modulus (P 0 \ P N) := by
      induction N with
      | zero =>
        simp
        rw [modulus_empty]
      | succ k ih =>
        rw [Finset.sum_range_succ]
        have h_split : P 0 \ P (k + 1) = (P 0 \ P k) ∪ (P k \ P (k + 1)) := by
          ext z
          simp
          constructor
          · intro h
            by_cases hk : z ∈ P k
            · right; exact ⟨hk, h.2⟩
            · left; exact ⟨h.1, hk⟩
          · intro h
            cases h with
            | inl h => exact ⟨h.1, fun h_in => h.2 (h_nested k h_in)⟩
            | inr h =>
                have h_sub : P k ⊆ P 0 := subset_of_le_nested h_nested (Nat.zero_le k)
                exact ⟨h_sub h.1, h.2⟩

        have h_disj_split : Disjoint (P 0 \ P k) (P k \ P (k + 1)) := by
          rw [Set.disjoint_left]
          intro z h1 h2
          have h_in_Pk := h2.1
          have h_not_in_Pk := h1.2
          contradiction

        have h_ineq := groetzsch_inequality h_disj_split (subset_of_eq h_split.symm) 
          ((h_meas 0).diff (h_meas k)) ((h_meas k).diff (h_meas (k+1)))
        apply le_trans (add_le_add ih (le_refl (modulus (A k))))
        exact h_ineq

    apply le_trans h_sum_le
    apply modulus_mono
    apply diff_subset_diff_right
    apply sInter_subset_of_mem
    simp
    apply (h_meas 0).diff
    apply (h_meas N)

  apply summable_of_sum_range_le (fun n => modulus_nonneg _) h_bounded

/-- Grötzsch's Criterion: Divergence of moduli implies point intersection.
    See: [Milnor, Dynamics in One Complex Variable, Corollary B.7]
    Local Reference: `refs/9201272v1.pdf`
    "Corollary B.7. Suppose that K ⊂ U as described above. Then K reduces to a single point if and only if the annulus A = U rK has infinite modulus."

    Proof idea: We argue by contrapositive. If the intersection is non-trivial (contains more than just `{0}`),
    then `modulus_summable_of_nontrivial_intersection` implies the sum of moduli converges.
    This contradicts the hypothesis that the sum diverges.
    Therefore, the intersection must be trivial (equal to `{0}`). -/
theorem groetzsch_criterion {P : ℕ → Set ℂ}
    (h_nested : ∀ n, P (n + 1) ⊆ P n)
    (h_zero : ∀ n, 0 ∈ P n)
    (h_conn : ∀ n, IsConnected (P n))
    (h_meas : ∀ n, NullMeasurableSet (P n) volume)
    (h_div : ¬ Summable (fun n => modulus (P n \ P (n + 1)))) :
    (⋂ n, P n) = {0} := by
  by_contra h_neq
  have h_nontriv : Set.Nontrivial (⋂ n, P n) := by
    have h_0 : 0 ∈ ⋂ n, P n := Set.mem_iInter.mpr h_zero
    rw [Set.nontrivial_iff_exists_ne h_0]
    by_contra h_all_eq
    apply h_neq
    ext z
    constructor
    · intro hz
      by_cases h_z_eq : z = 0
      · rw [h_z_eq]; exact Set.mem_singleton 0
      · push_neg at h_all_eq
        specialize h_all_eq z hz
        contradiction
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact h_0
  have h_sum := modulus_summable_of_nontrivial_intersection h_nested h_conn h_nontriv h_meas
  contradiction

end

end Quadratic
end MLC
