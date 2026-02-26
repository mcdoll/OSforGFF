/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.MeasureTheory.Function.Holder

import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density

import OSforGFF.ForMathlib.LocallyIntegrable
import OSforGFF.ForMathlib.SchwartzMap

/-!
## Functional Analysis for AQFT

This file provides functional analysis tools for Algebraic Quantum Field Theory,
focusing on integrability, Schwartz function properties, and L² embeddings.

### Key Definitions & Theorems:

**Schwartz Space Properties:**
- `SchwartzMap.hasTemperateGrowth_general`: Schwartz functions have temperate growth
- `SchwartzMap.integrable_mul_bounded`: Schwartz × bounded → integrable
- `SchwartzMap.integrable_conj`: Conjugate of Schwartz function is integrable
- `SchwartzMap.translate`: Translation of Schwartz functions
- `schwartz_integrable_decay`: Decay bounds for Schwartz function integrals

**Complex Embeddings:**
- `Complex.ofRealCLM_isometry`: Real→Complex embedding is isometric
- `Complex.ofRealCLM_continuous_compLp`: Continuous lifting to Lp spaces
- `embedding_real_to_complex`: Canonical ℝ→ℂ embedding for Lp functions

**Schwartz→L² Embedding:**
- `schwartzToL2`: Embedding Schwartz functions into L² space
- `schwartzToL2'`: Alternative embedding for EuclideanSpace types

**L∞·L² Multiplication:**
- `linfty_mul_L2_CLM`: Continuous bilinear map L∞ × L² → L²
- `linfty_mul_L2_CLM_norm_bound`: Norm bound ‖f · g‖₂ ≤ ‖f‖∞ · ‖g‖₂

**Integrability Results:**
- `integrableOn_ball_of_radial`: Radial functions integrable on balls
- `integrableOn_ball_of_rpow_decay`: Power-law decay integrable on balls
- `integrableOn_compact_diff_ball`: Integrability on compact ∖ ball
- `locallyIntegrable_of_rpow_decay_real`: Local integrability from power decay (d ≥ 3)
- `polynomial_decay_integrable_3d`: 1/‖x‖ integrable on 3D balls
- `schwartz_bilinear_integrable_of_translationInvariant_L1`: Bilinear Schwartz integrability

**Vanishing & Bounds:**
- `schwartz_vanishing_linear_bound_general`: Linear vanishing bounds for Schwartz functions

**Bump Function Convolutions:**
- `bumpSelfConv`: Self-convolution of bump functions
- `bumpSelfConv_nonneg`, `bumpSelfConv_integral`: Properties of self-convolution
- `bumpSelfConv_support_subset`, `bumpSelfConv_support_tendsto`: Support control
- `double_mollifier_convergence`: Convergence of double mollifier approximations

**Utility Lemmas:**
- `norm_exp_I_mul_real`, `norm_exp_neg_I_mul_real`: ‖exp(±i·r)‖ = 1
- `sub_const_hasTemperateGrowth`: Translation has temperate growth
-/

open MeasureTheory NNReal ENNReal Complex
open TopologicalSpace Measure
open scoped FourierTransform

noncomputable section

/-! ## Proven theorems in this file

The following L∞ × L² multiplication theorems are fully proven (2025-12-13):
- `linfty_mul_L2_CLM` (line ~607): L∞ × L² → L² bounded linear operator
- `linfty_mul_L2_CLM_spec` (line ~639): pointwise specification (g·f)(x) = g(x)·f(x) a.e.
- `linfty_mul_L2_CLM_norm_bound` (line ~650): operator norm bound ‖T_g f‖ ≤ C·‖f‖
-/

open MeasureTheory.Measure


variable {d : ℕ} [NeZero d]

-- Add inner product space structure
variable [Fintype (Fin d)]

/-! ## Schwartz function properties -/

/- Multiplication of Schwarz functions
 -/

open scoped SchwartzMap

variable {𝕜 : Type} [RCLike 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- Measure lifting from real to complex Lp spaces -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

-- Add measurable space instances for Lp spaces
instance [MeasurableSpace α] (μ : Measure α) : MeasurableSpace (Lp ℝ 2 μ) := borel _
instance [MeasurableSpace α] (μ : Measure α) : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
instance [MeasurableSpace α] (μ : Measure α) : MeasurableSpace (Lp ℂ 2 μ) := borel _
instance [MeasurableSpace α] (μ : Measure α) : BorelSpace (Lp ℂ 2 μ) := ⟨rfl⟩

-- Use this to prove our specific case
lemma Complex.ofRealCLM_continuous_compLp {α : Type*} [MeasurableSpace α] {μ : Measure α} :
  Continuous (fun φ : Lp ℝ 2 μ => Complex.ofRealCLM.compLp φ : Lp ℝ 2 μ → Lp ℂ 2 μ) := by
  -- The function φ ↦ L.compLp φ is the application of the continuous linear map
  -- ContinuousLinearMap.compLpL p μ L, which is continuous
  exact (ContinuousLinearMap.compLpL 2 μ Complex.ofRealCLM).continuous

/--
Compose an Lp function with a continuous linear map.
This should be the canonical way to lift real Lp functions to complex Lp functions.
-/
noncomputable def composed_function {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) (A : ℝ →L[ℝ] ℂ): Lp ℂ 2 μ :=
  A.compLp f

-- Check that we get the expected norm bound
example {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) (A : ℝ →L[ℝ] ℂ) : ‖A.compLp f‖ ≤ ‖A‖ * ‖f‖ :=
  ContinuousLinearMap.norm_compLp_le A f

/--
Embedding from real Lp functions to complex Lp functions using the canonical embedding ℝ → ℂ.
-/
noncomputable def embedding_real_to_complex {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (φ : Lp ℝ 2 μ) : Lp ℂ 2 μ :=
  composed_function φ (Complex.ofRealCLM)

section LiftMeasure
  variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

  /--
  Lifts a probability measure from the space of real Lp functions to the space of
  complex Lp functions, with support on the real subspace.
  -/
  noncomputable def liftMeasure_real_to_complex
      (dμ_real : ProbabilityMeasure (Lp ℝ 2 μ)) :
      ProbabilityMeasure (Lp ℂ 2 μ) :=
    let dμ_complex_measure : Measure (Lp ℂ 2 μ) :=
      Measure.map embedding_real_to_complex dμ_real
    have h_ae : AEMeasurable embedding_real_to_complex dμ_real := by
      apply Continuous.aemeasurable
      unfold embedding_real_to_complex composed_function
      have : Continuous (fun φ : Lp ℝ 2 μ => Complex.ofRealCLM.compLp φ : Lp ℝ 2 μ → Lp ℂ 2 μ) :=
        Complex.ofRealCLM_continuous_compLp
      exact this
    have h_is_prob := isProbabilityMeasure_map h_ae
    ⟨dμ_complex_measure, h_is_prob⟩

end LiftMeasure



/-! ## Fourier Transform as Linear Isometry on L² Spaces

The key challenge in defining the Fourier transform on L² spaces is that the Fourier integral
∫ f(x) e^(-2πi⟨x,ξ⟩) dx may not converge for arbitrary f ∈ L²(ℝᵈ).

**Construction Strategy (following the Schwartz space approach):**
1. **Dense Core**: Use Schwartz functions 𝒮(ℝᵈ) as the dense subset where Fourier integrals converge
2. **Schwartz Fourier**: Apply the Fourier transform on Schwartz space (unitary)
3. **Embedding to L²**: Embed Schwartz functions into L² space
4. **Plancherel on Core**: Show ‖ℱf‖₂ = ‖f‖₂ for f ∈ 𝒮(ℝᵈ)
5. **Extension**: Use the universal property of L² to extend to all of L²

This construction gives a unitary operator ℱ : L²(ℝᵈ) ≃ₗᵢ[ℂ] L²(ℝᵈ).
-/

variable {d : ℕ} [NeZero d] [Fintype (Fin d)]

-- Type abbreviations for clarity
abbrev EuclideanRd (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev SchwartzRd (d : ℕ) := SchwartzMap (EuclideanRd d) ℂ
abbrev L2Complex (d : ℕ) := Lp ℂ 2 (volume : Measure (EuclideanRd d))

/-! ### Core construction components (using Mathlib APIs) -/


/-- Embedding Schwartz functions into L² space using Mathlib's toLpCLM.
    This is a continuous linear map from Schwartz space to L²(ℝᵈ, ℂ).
    ✅ IMPLEMENTED: Uses SchwartzMap.toLpCLM from Mathlib -/
noncomputable def schwartzToL2 (d : ℕ) : SchwartzRd d →L[ℂ] L2Complex d :=
  SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanRd d))

/-- Alternative embedding that produces the exact L² type expected by the unprimed theorems.
    This maps Schwartz functions to Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))).
    The difference from schwartzToL2 is only in the type representation, not the mathematical content. -/
noncomputable def schwartzToL2' (d : ℕ) [Fintype (Fin d)] :
  SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ →L[ℂ] Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-! ## L∞ Multiplication on L² Spaces

This section proves that multiplication by L∞ functions defines bounded operators on L².

Mathematical background:
- If g ∈ L∞(μ) with ‖g‖∞ ≤ C, then f ↦ g·f is a bounded linear operator L² → L²
- The operator norm satisfies ‖Mg‖ ≤ C
- The action is pointwise a.e.: (Mg f)(x) = g(x) · f(x) a.e.

Proof method (2025-12-13):
- Uses Mathlib's `eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm` for the L∞ × Lp → Lp bound
- For ℂ, multiplication equals scalar multiplication (g * f = g • f)
- Hölder's inequality via `MemLp.mul` with HolderTriple ∞ 2 2

These theorems are used to construct specific multiplication operators
(e.g., momentumWeightSqrt_mul_CLM) without repeating technical details.
-/

/-- Given a measurable function `g` that is essentially bounded by `C`,
    multiplication by `g` defines a bounded linear operator on `L²`. -/
noncomputable def linfty_mul_L2_CLM {μ : Measure α}
    (g : α → ℂ) (hg_meas : Measurable g) (C : ℝ)
    (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  have hg_mem : MemLp g ∞ μ := memLp_top_of_bound hg_meas.aestronglyMeasurable C hg_bound
  ContinuousLinearMap.holderL μ ∞ 2 2 (ContinuousLinearMap.mul _ _) hg_mem.toLp

/-- The multiplication operator acts pointwise almost everywhere on `L²`. -/
lemma linfty_mul_L2_CLM_spec {μ : Measure α}
    (g : α → ℂ) (hg_meas : Measurable g) (C : ℝ)
    (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (f : Lp ℂ 2 μ) :
    (linfty_mul_L2_CLM g hg_meas C hg_bound f) =ᵐ[μ] fun x => g x * f x := by
  simp only [linfty_mul_L2_CLM, ContinuousLinearMap.holderL_apply_apply]
  have hg_mem := memLp_top_of_bound hg_meas.aestronglyMeasurable C hg_bound
  filter_upwards [hg_mem.coeFn_toLp,
    (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) hg_mem.toLp f] with x hg h
  simp [h, hg]

/-- The operator norm of the multiplication operator is bounded by C.
    This gives ‖Mg f‖₂ ≤ C · ‖f‖₂ for all f ∈ L². -/
theorem linfty_mul_L2_CLM_norm_bound {μ : Measure α}
    (g : α → ℂ) (hg_meas : Measurable g) (C : ℝ) (hC : 0 ≤ C)
    (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (f : Lp ℂ 2 μ) :
    ‖linfty_mul_L2_CLM g hg_meas C hg_bound f‖ ≤ C * ‖f‖ := by
  have hg_mem := memLp_top_of_bound hg_meas.aestronglyMeasurable C hg_bound
  calc
    _ ≤ ‖(ContinuousLinearMap.mul ℂ ℂ)‖ * ‖hg_mem.toLp‖ * ‖f‖ := by
      apply (ContinuousLinearMap.mul ℂ ℂ).norm_holder_apply_apply_le
    _ ≤ C * ‖f‖ := by
      simp only [ContinuousLinearMap.opNorm_mul, Lp.norm_toLp, eLpNorm_exponent_top, one_mul]
      gcongr
      refine toReal_le_of_le_ofReal hC ?_
      exact eLpNormEssSup_le_of_ae_bound hg_bound

/-! ## Bilinear Integrability for L¹ Translation-Invariant Kernels

For translation-invariant kernels K₀ that are integrable (L¹), the bilinear form
f(x) K₀(x-y) g(y) with Schwartz test functions f, g is integrable on E × E.

This applies to exponentially decaying kernels like the massive free covariance.
-/

/-- For translation-invariant kernels K₀ that are **integrable** (L¹), the bilinear form
    with Schwartz test functions is integrable. This is the easiest case and applies to
    exponentially decaying kernels like the massive free covariance.

    Proof idea:
    - Schwartz functions are bounded: ‖f‖_∞ < ∞ (via toBoundedContinuousFunction)
    - Schwartz functions are integrable: ‖g‖_{L¹} < ∞
    - K₀ is integrable: ‖K₀‖_{L¹} < ∞
    - Then: ∫∫ |f(x) K₀(x-y) g(y)| dx dy ≤ ‖f‖_∞ · ‖K₀‖_{L¹} · ‖g‖_{L¹} < ∞ -/
theorem schwartz_bilinear_integrable_of_translationInvariant_L1
    {d : ℕ}
    (K₀ : EuclideanSpace ℝ (Fin d) → ℂ)
    (hK₀_int : Integrable K₀ volume)
    (f g : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      f p.1 * K₀ (p.1 - p.2) * g p.2) volume := by
  -- Get boundedness of f: Schwartz functions are bounded continuous
  have hf_bdd : ∃ Cf, ∀ x, ‖f x‖ ≤ Cf := by
    use ‖f.toBoundedContinuousFunction‖
    intro x
    exact BoundedContinuousFunction.norm_coe_le_norm f.toBoundedContinuousFunction x
  obtain ⟨Cf, hCf⟩ := hf_bdd

  -- Get integrability of g (Schwartz functions are integrable)
  have hg_int : Integrable g volume := g.integrable

  -- The dominating function: Cf * |K₀(x-y)| * |g(y)|
  let bound : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ :=
    fun p => Cf * ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖

  -- Use Integrable.mono' with the bound
  apply Integrable.mono'
  · -- Show the bound is integrable
    -- Key: ∫∫ |K₀(x-y)| |g(y)| dx dy = ‖K₀‖_{L¹} · ‖g‖_{L¹} (by Fubini + translation invariance)
    -- Get integrability of norms
    have hK_norm_int : Integrable (fun z => ‖K₀ z‖) volume := Integrable.norm hK₀_int
    have hg_norm_int : Integrable (fun y => ‖g y‖) volume := Integrable.norm hg_int
    -- Product of integrable real functions is integrable on product space
    have hprod : Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ‖K₀ p.1‖ * ‖g p.2‖) (volume.prod volume) := Integrable.mul_prod hK_norm_int hg_norm_int
    -- Change of variables: (z, y) ↦ (z + y, y) = (x, y), so z = x - y
    -- Use the MeasurableEquiv for (x, y) ↦ (x - y, y)
    let e : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ≃ᵐ
        EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) :=
      { toFun := fun p => (p.1 - p.2, p.2)
        invFun := fun p => (p.1 + p.2, p.2)
        left_inv := fun p => by simp [sub_add_cancel]
        right_inv := fun p => by simp [add_sub_cancel_right]
        measurable_toFun := Measurable.prodMk (measurable_fst.sub measurable_snd) measurable_snd
        measurable_invFun := Measurable.prodMk (measurable_fst.add measurable_snd) measurable_snd }
    -- The map preserves measure (translation invariance of Lebesgue measure)
    have he_preserves : MeasurePreserving e (volume.prod volume) (volume.prod volume) := by
      -- Use measurePreserving_sub_prod: (x, y) ↦ (x - y, y) preserves measure
      have := measurePreserving_sub_prod (G := EuclideanSpace ℝ (Fin d)) volume volume
      convert this using 1
    have hchange : Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖) (volume.prod volume) := by
      -- We have hprod : Integrable (fun p => ‖K₀ p.1‖ * ‖g p.2‖)
      -- We want: Integrable (fun p => ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖)
      -- These are related by: (fun p => ‖K₀ p.1‖ * ‖g p.2‖) ∘ e = (fun p => ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖)
      -- where e(p) = (p.1 - p.2, p.2)
      -- Use integrable_comp_emb: (Integrable g μb ↔ Integrable (g ∘ f) μa) for MeasurePreserving f
      have heq : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖) = (fun p => ‖K₀ p.1‖ * ‖g p.2‖) ∘ e := by
        ext p
        rfl
      rw [heq, he_preserves.integrable_comp_emb e.measurableEmbedding]
      exact hprod
    -- Multiply by constant Cf
    exact hchange.const_mul Cf

  · -- AEStronglyMeasurable of the integrand
    apply AEStronglyMeasurable.mul
    apply AEStronglyMeasurable.mul
    · exact f.continuous.aestronglyMeasurable.comp_measurable measurable_fst
    · -- K₀ is AEStronglyMeasurable on volume, need it on product
      -- Use that the shear map (x,y) ↦ (x-y, y) is measure-preserving
      have hK_ae : AEStronglyMeasurable K₀ volume := hK₀_int.1
      -- K₀ ∘ fst is AEStronglyMeasurable on volume.prod volume
      have hK_fst : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          K₀ p.1) (volume.prod volume) := hK_ae.comp_fst
      -- The shear map e(x,y) = (x-y, y) is measure-preserving
      have he_sub_preserves : MeasurePreserving
          (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => (p.1 - p.2, p.2))
          (volume.prod volume) (volume.prod volume) := by
        have := measurePreserving_sub_prod (G := EuclideanSpace ℝ (Fin d)) volume volume
        convert this using 1
      -- Composition: K₀ ∘ fst ∘ e = fun p => K₀ (p.1 - p.2)
      have heq : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => K₀ (p.1 - p.2)) =
          (fun p => K₀ p.1) ∘ (fun p => (p.1 - p.2, p.2)) := by
        ext p; simp only [Function.comp_apply]
      rw [heq]
      exact hK_fst.comp_measurePreserving he_sub_preserves
    · exact g.continuous.aestronglyMeasurable.comp_measurable measurable_snd

  · -- Pointwise bound: ‖f(x) K₀(x-y) g(y)‖ ≤ Cf * ‖K₀(x-y)‖ * ‖g(y)‖
    filter_upwards with p
    rw [norm_mul, norm_mul]
    calc ‖f p.1‖ * ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖
        ≤ Cf * ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖ := by
          have h := hCf p.1
          have h1 : 0 ≤ ‖K₀ (p.1 - p.2)‖ := norm_nonneg _
          have h2 : 0 ≤ ‖g p.2‖ := norm_nonneg _
          have h12 : 0 ≤ ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖ := mul_nonneg h1 h2
          calc ‖f p.1‖ * ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖
              = ‖f p.1‖ * (‖K₀ (p.1 - p.2)‖ * ‖g p.2‖) := by ring
            _ ≤ Cf * (‖K₀ (p.1 - p.2)‖ * ‖g p.2‖) := mul_le_mul_of_nonneg_right h h12
            _ = Cf * ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖ := by ring
      _ = Cf * (‖K₀ (p.1 - p.2)‖ * ‖g p.2‖) := by ring

/-! ## Schwartz Functions Times Bounded Functions

These lemmas establish integrability of Schwartz functions multiplied by bounded
measurable functions, which is essential for Fourier transform computations.
-/

section SchwartzBounded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {μ : Measure E} [μ.HasTemperateGrowth]

/-- A Schwartz function times a bounded measurable function is integrable.
    This is the key technical lemma for Fourier-type integrals. -/
lemma SchwartzMap.integrable_mul_bounded (f : SchwartzMap E ℂ) (g : E → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∀ x, ‖g x‖ ≤ 1) :
    Integrable (fun x => f x * g x) μ := by
  have hf_int : Integrable f μ := f.integrable
  -- Use bdd_mul: Integrable f → AEStronglyMeasurable g → (∀ᵐ x, ‖g x‖ ≤ C) → Integrable (g * f)
  -- Then convert by commutativity
  have hg_ae : AEStronglyMeasurable g μ := hg_meas.aestronglyMeasurable
  have hg_ae_bdd : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1 := Filter.Eventually.of_forall hg_bdd
  exact Integrable.mul_bdd hf_int hg_ae hg_ae_bdd

/-- The conjugate of a Schwartz function is integrable. -/
lemma SchwartzMap.integrable_conj (f : SchwartzMap E ℂ) :
    Integrable (fun y => starRingEnd ℂ (f y)) μ := by
  -- MD: this should be proved by showing that `(fun y => starRingEnd ℂ (f y))` is a Schwartz function
  have hf_int : Integrable f μ := f.integrable
  have hf_star_meas : AEStronglyMeasurable (fun y => starRingEnd ℂ (f y)) μ :=
    hf_int.aestronglyMeasurable.star
  have h_norm_eq : ∀ᵐ y ∂μ, ‖f y‖ = ‖starRingEnd ℂ (f y)‖ := by
    filter_upwards with y
    exact (RCLike.norm_conj (f y)).symm
  exact hf_int.congr' hf_star_meas h_norm_eq

end SchwartzBounded

/-! ## Phase Exponential Lemmas

Lemmas about complex exponentials of pure imaginary arguments, used in Fourier analysis.
-/

/-- Complex exponential of pure imaginary argument has norm 1. -/
lemma norm_exp_I_mul_real (r : ℝ) : ‖Complex.exp (Complex.I * r)‖ = 1 :=
  norm_exp_I_mul_ofReal r

/-- Complex exponential of negative pure imaginary argument has norm 1. -/
lemma norm_exp_neg_I_mul_real (r : ℝ) : ‖Complex.exp (-Complex.I * r)‖ = 1 := by
  rw [neg_mul, ←mul_neg]
  norm_cast
  apply norm_exp_I_mul_ofReal (-r)

/-! ## Linear Vanishing Bound for Schwartz Functions

If a Schwartz function on ℝ × E vanishes for t ≤ 0, then it grows at most linearly in t.
This is a key lemma for UV regularization in QFT integrals.
-/

namespace SchwartzLinearBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Linear Vanishing Bound (general version).
    If f : 𝓢(ℝ × E, ℂ) vanishes for t ≤ 0, it grows at most linearly in t for t > 0.

    This follows from the Mean Value Theorem: f(t,x) - f(0,x) = ∫₀ᵗ ∂ₜf dt,
    and since ∂ₜf is bounded (Schwartz), we get |f(t,x)| ≤ C·t.
-/
theorem schwartz_vanishing_linear_bound_general
    (f : SchwartzMap (ℝ × E) ℂ)
    (h_vanish : ∀ t x, t ≤ 0 → f (t, x) = 0) :
    ∃ C, ∀ t ≥ 0, ∀ x, ‖f (t, x)‖ ≤ C * t := by

  -- 1. Get a bound on the Fréchet derivative using Schwartz seminorms
  have h_diff : Differentiable ℝ f := f.differentiable

  -- Use the first order seminorm to bound the derivative
  let C_deriv := (SchwartzMap.seminorm ℝ 0 1).toFun f + 1

  have h_deriv_bound : ∀ y : ℝ × E, ‖iteratedFDeriv ℝ 1 f y‖ ≤ C_deriv := by
    intro y
    have h := SchwartzMap.le_seminorm ℝ 0 1 f y
    simp only [pow_zero, one_mul] at h
    calc ‖iteratedFDeriv ℝ 1 (⇑f) y‖ ≤ (SchwartzMap.seminorm ℝ 0 1) f := h
      _ ≤ (SchwartzMap.seminorm ℝ 0 1) f + 1 := by linarith
      _ = C_deriv := rfl

  -- The convex set (whole space)
  have h_convex : Convex ℝ (Set.univ : Set (ℝ × E)) := convex_univ

  -- Schwartz functions have FDeriv everywhere
  have h_hasFDeriv : ∀ y ∈ (Set.univ : Set (ℝ × E)),
      HasFDerivWithinAt f (fderiv ℝ f y) Set.univ y := by
    intro y _
    exact f.differentiableAt.hasFDerivAt.hasFDerivWithinAt

  -- Connection: ‖fderiv ℝ f y‖ = ‖iteratedFDeriv ℝ 1 f y‖
  have h_fderiv_bound : ∀ y ∈ (Set.univ : Set (ℝ × E)), ‖fderiv ℝ f y‖ ≤ C_deriv := by
    intro y _
    have h_norm_eq : ‖iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f y‖ := by
      rw [← iteratedFDerivWithin_univ, ← fderivWithin_univ]
      exact norm_iteratedFDerivWithin_one f uniqueDiffWithinAt_univ
    linarith [h_deriv_bound y]

  use C_deriv
  intro t ht x

  -- 2. The reference point: (0, x) where f vanishes
  let A : ℝ × E := (0, x)
  let B : ℝ × E := (t, x)

  -- f vanishes at A = (0, x)
  have h_zero : f A = 0 := h_vanish 0 x (le_refl 0)

  -- Handle the t = 0 case separately
  by_cases ht0 : t = 0
  · simp [ht0, h_zero, A]

  -- For t > 0, apply MVT
  have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)

  -- Apply the Mean Value Theorem
  have h_mvt := h_convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    h_hasFDeriv h_fderiv_bound (Set.mem_univ A) (Set.mem_univ B)

  -- Simplify: f A = 0, so ‖f B‖ ≤ C_deriv * ‖B - A‖
  rw [h_zero, sub_zero] at h_mvt

  -- Compute ‖B - A‖ = ‖(t, x) - (0, x)‖ = ‖(t, 0)‖ = |t| = t
  have h_dist : ‖B - A‖ = t := by
    simp only [B, A, Prod.mk_sub_mk, sub_zero]
    rw [Prod.norm_def]
    simp only [_root_.sub_self, norm_zero, max_eq_left (norm_nonneg t)]
    rw [Real.norm_eq_abs, abs_of_nonneg ht]

  rw [h_dist] at h_mvt
  exact h_mvt

end SchwartzLinearBound

/-! ### Schwartz Integrable Decay

Schwartz functions decay faster than any polynomial inverse.
This justifies integrability conditions.
-/

section SchwartzDecay
open Real

/-- **Schwartz L¹ bound**: Schwartz functions are integrable with explicit decay.
    For f ∈ 𝓢(ℝⁿ), we have ∫ |f(x)| dx < ∞.

    More precisely, for any N, there exists C such that
    |f(x)| ≤ C / (1 + |x|)^N. If N > dim(V), this implies integrability.

    **Reference**: Stein-Weiss, Chapter 1, Proposition 1.1 -/
theorem schwartz_integrable_decay {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
    (f : SchwartzMap V ℂ) (N : ℕ) (_hN : Module.finrank ℝ V < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : V, ‖f x‖ ≤ C / (1 + ‖x‖)^N := by
  use 2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f + 1
  constructor
  · positivity
  intro x
  field_simp
  calc
    ‖f x‖ * (1 + ‖x‖) ^ N = (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ 0 f x‖ := by
      simp only [norm_iteratedFDeriv_zero]
      ring
    _ ≤ 2 ^ (N, 0).1 * ((Finset.Iic (N, 0)).sup fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) f := by
      apply SchwartzMap.one_add_le_sup_seminorm_apply (by rfl) (by rfl)
    _ ≤ 2 ^ N * ((Finset.Iic (N, 0)).sup fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) f + 1 := by
      simp

end SchwartzDecay

/-! ## Double Mollifier Convergence

This section proves the double mollifier convergence theorem: for a continuous
kernel C (away from the origin), the double convolution with mollifiers converges
to the kernel value at separated points:

  ∫∫ φ_ε(x-a) C(x-y) φ_ε(y) dx dy → C(a) as ε → 0

The key insight is that the self-convolution φ ⋆ φ is itself an approximate identity,
so by associativity we reduce to a single convolution limit.
-/

section DoubleMollifierConvergence

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NoAtoms (volume : Measure E)]

open MeasureTheory Filter Convolution Set Function Topology
open scoped Pointwise BigOperators

variable {E}

/-- The self-convolution of a normalized bump function. -/
noncomputable def bumpSelfConv (φ : ContDiffBump (0 : E)) : E → ℝ :=
  (φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ.normed volume)

set_option linter.unusedSectionVars false in
/-- Self-convolution is nonnegative. -/
lemma bumpSelfConv_nonneg (φ : ContDiffBump (0 : E)) (x : E) : 0 ≤ bumpSelfConv φ x := by
  unfold bumpSelfConv convolution
  apply integral_nonneg
  intro y
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact mul_nonneg (φ.nonneg_normed _) (φ.nonneg_normed _)

set_option linter.unusedSectionVars false in
/-- Self-convolution has mass 1: ∫(φ ⋆ φ) = (∫φ)(∫φ) = 1·1 = 1. -/
lemma bumpSelfConv_integral (φ : ContDiffBump (0 : E)) :
    ∫ x, bumpSelfConv φ x = 1 := by
  unfold bumpSelfConv
  rw [integral_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)]
  · simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    have h1 := φ.integral_normed (μ := volume)
    simp only [h1]
    norm_num
  · exact φ.integrable_normed
  · exact φ.integrable_normed

set_option linter.unusedSectionVars false in
/-- Support of self-convolution is contained in ball of radius 2*rOut. -/
lemma bumpSelfConv_support_subset (φ : ContDiffBump (0 : E)) :
    support (bumpSelfConv φ) ⊆ Metric.ball 0 (2 * φ.rOut) := by
  unfold bumpSelfConv
  intro x hx
  have hsub : support (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ.normed volume) ⊆
      support (φ.normed volume) + support (φ.normed volume) :=
    support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
  have hx' := hsub hx
  rw [Set.mem_add] at hx'
  obtain ⟨y, hy, z, hz, hyz⟩ := hx'
  have hy_ball : y ∈ Metric.ball (0 : E) φ.rOut := by
    have := φ.support_normed_eq (μ := volume)
    rw [this] at hy
    exact hy
  have hz_ball : z ∈ Metric.ball (0 : E) φ.rOut := by
    have := φ.support_normed_eq (μ := volume)
    rw [this] at hz
    exact hz
  rw [Metric.mem_ball] at hy_ball hz_ball ⊢
  rw [dist_zero_right] at hy_ball hz_ball ⊢
  rw [← hyz]
  calc ‖y + z‖ ≤ ‖y‖ + ‖z‖ := norm_add_le y z
    _ < φ.rOut + φ.rOut := add_lt_add hy_ball hz_ball
    _ = 2 * φ.rOut := by ring

/-- Self-convolution support shrinks to {0} as rOut → 0. -/
lemma bumpSelfConv_support_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (φ : ι → ContDiffBump (0 : E)) (hφ : Tendsto (fun i => (φ i).rOut) l (nhds 0)) :
    Tendsto (fun i => support (bumpSelfConv (φ i))) l (𝓝 (0 : E)).smallSets := by
  rw [tendsto_smallSets_iff]
  intro s hs
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hε, hs⟩ := hs
  have h := hφ.eventually (Iio_mem_nhds (half_pos hε))
  filter_upwards [h] with i hi
  intro x hx
  apply hs
  have hsub := bumpSelfConv_support_subset (φ i)
  have hx_ball := hsub hx
  rw [Metric.mem_ball, dist_zero_right] at hx_ball ⊢
  calc ‖x‖ < 2 * (φ i).rOut := hx_ball
    _ < 2 * (ε / 2) := by
        apply mul_lt_mul_of_pos_left hi
        norm_num
    _ = ε := by ring

/-- **Main theorem: Double mollifier convergence via associativity.**

    For C continuous on {x ≠ 0}, the double mollifier integral converges:
    ∫∫ φ_ε(x-a) C(x-y) φ_ε(y) dx dy → C(a) as ε → 0

    **Proof strategy:**
    1. Recognize that ψ := φ ⋆ φ (self-convolution) is an approximate identity:
       - Nonnegative (integral of product of nonneg functions)
       - Mass 1: ∫ψ = (∫φ)² = 1
       - Shrinking support: supp(ψ) ⊆ B(0, 2·rOut)
    2. By associativity: ∫∫ φ(x-a) C(x-y) φ(y) dx dy = (ψ ⋆ C)(a)
    3. Apply single-convolution theorem: (ψ ⋆ C)(a) → C(a)
-/
theorem double_mollifier_convergence
    (C : E → ℝ)
    (hC : ContinuousOn C {x | x ≠ 0})
    (a : E) (ha : a ≠ 0)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (φ : ι → ContDiffBump (0 : E))
    (hφ : Tendsto (fun i => (φ i).rOut) l (nhds 0)) :
    Tendsto
      (fun i => ∫ x, ∫ y, (φ i).normed volume (x - a) * C (x - y) * (φ i).normed volume y)
      l (nhds (C a)) := by
  -- The self-convolution satisfies approximate identity conditions:
  -- 1. Nonnegative
  have hnonneg : ∀ᶠ i in l, ∀ x, 0 ≤ bumpSelfConv (φ i) x :=
    Eventually.of_forall (fun i => bumpSelfConv_nonneg (φ i))

  -- 2. Integral = 1
  have hintegral : ∀ᶠ i in l, ∫ x, bumpSelfConv (φ i) x = 1 :=
    Eventually.of_forall (fun i => bumpSelfConv_integral (φ i))

  -- 3. Support shrinks to 0
  have hsupport : Tendsto (fun i => support (bumpSelfConv (φ i))) l (𝓝 (0 : E)).smallSets :=
    bumpSelfConv_support_tendsto φ hφ

  -- C is continuous at a (since a ≠ 0)
  have hCa : ContinuousAt C a := hC.continuousAt (isOpen_ne.mem_nhds ha)

  -- Step 1: C is AE strongly measurable (continuous on open set)
  have hmC : AEStronglyMeasurable C volume := by
    have h_ae : ∀ᵐ (x : E) ∂volume, x ∈ {x : E | x ≠ 0} := by
      rw [ae_iff]
      simp only [mem_setOf_eq, not_not]
      have : ({x : E | x = 0} : Set E) = {0} := by ext; simp
      rw [this]
      exact measure_singleton 0
    have h_restrict : (volume : Measure E).restrict {x | x ≠ 0} = volume :=
      Measure.restrict_eq_self_of_ae_mem h_ae
    have h_meas : MeasurableSet {x : E | x ≠ 0} := isOpen_ne.measurableSet
    have h := hC.aestronglyMeasurable (μ := volume) h_meas
    rw [h_restrict] at h
    exact h

  -- Step 2: C converges to C(a) at a (since C is continuous at a)
  have hCconv : Tendsto (uncurry fun _ : ι => C) (l ×ˢ 𝓝 a) (𝓝 (C a)) := by
    have h : uncurry (fun _ : ι => C) = C ∘ Prod.snd := by
      ext ⟨i, x⟩
      simp [uncurry]
    rw [h]
    exact hCa.tendsto.comp (Filter.tendsto_snd (f := l) (g := 𝓝 a))

  -- Step 3: Apply convolution_tendsto_right with ψ = bumpSelfConv
  have h_selfconv_limit : Tendsto
      (fun i => (bumpSelfConv (φ i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C) a)
      l (𝓝 (C a)) := by
    apply convolution_tendsto_right hnonneg hintegral hsupport
    · filter_upwards with i; exact hmC
    · exact hCconv
    · exact tendsto_const_nhds

  -- Step 4: Show double integral equals (bumpSelfConv ⋆ C)(a)
  have h_eq : ∀ᶠ i in l,
      (∫ x, ∫ y, (φ i).normed volume (x - a) * C (x - y) * (φ i).normed volume y) =
      (bumpSelfConv (φ i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C) a := by
    have hr_pos : 0 < ‖a‖ / 3 := div_pos (norm_pos_iff.mpr ha) (by norm_num)
    filter_upwards [hφ (Metric.ball_mem_nhds 0 hr_pos)] with i hi
    let ψ := (φ i).normed volume

    -- 1. Identify inner integral as convolution
    have h_inner : ∀ x, ∫ y, C (x - y) * ψ y = (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C) x := by
      intro x
      rw [convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      congr 1; ext y; ring

    -- 2. Rewrite LHS using inner convolution
    conv_lhs =>
      enter [2, x]
      conv =>
        enter [2, y]
        rw [mul_assoc]
      rw [MeasureTheory.integral_const_mul]
      rw [h_inner x]

    -- 3. Show equal to (ψ ⋆ (ψ ⋆ C))(a)
    have h_outer : (∫ x, ψ (x - a) * (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C) x) =
                   (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C)) a := by
      let g := ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C
      rw [convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      rw [← MeasureTheory.integral_add_right_eq_self (fun x => ψ (x - a) * g x) a]
      simp only [add_sub_cancel_right]
      rw [← MeasureTheory.integral_neg_eq_self]
      dsimp
      congr 1; ext x
      dsimp [ψ]
      rw [(φ i).normed_neg, add_comm (-x) a, sub_eq_add_neg]

    rw [h_outer]

    -- 4. Apply associativity manually to avoid global integrability issues
    let g := ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C
    have h_assoc : (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) a =
                   (bumpSelfConv (φ i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C) a := by
       simp only [bumpSelfConv, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
       conv_rhs =>
         enter [2]
         ext t
         rw [← MeasureTheory.integral_mul_const]
       rw [MeasureTheory.integral_integral_swap]
       · -- Transformations to match LHS
         congr 1; ext v
         dsimp [g]
         rw [convolution_def]
         simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
         have h_eq : ∫ x, ψ v * ψ (x - v) * C (a - x) = ψ v * ∫ y, ψ y * C (a - v - y) := by
           rw [← MeasureTheory.integral_const_mul]
           have h_shift := @MeasureTheory.integral_sub_right_eq_self E ℝ _ _ _
             (volume : Measure E) _ _ _
             (fun y => ψ v * (ψ y * C (a - v - y))) v
           rw [← h_shift]
           congr 1
           ext x
           have : a - v - (x - v) = a - x := by abel
           simp only [this]
           ring
         rw [h_eq]
       · -- Prove integrability of F(t, v) = ψ v * ψ(t-v) * C(a-t)
         let F := fun (p : E × E) => ψ p.2 * ψ (p.1 - p.2) * C (a - p.1)
         let K_t := Metric.closedBall (0 : E) (2 * (φ i).rOut)
         let K_v := Metric.closedBall (0 : E) ((φ i).rOut)
         let K := K_t ×ˢ K_v
         have hK_compact : IsCompact K := IsCompact.prod (isCompact_closedBall 0 _) (isCompact_closedBall 0 _)

         -- Support is in K
         have h_supp_F : support F ⊆ K := by
           intro ⟨t, v⟩ h
           rw [Function.mem_support] at h
           dsimp [F] at h
           have hv : ψ v ≠ 0 := by
             intro zero
             rw [zero] at h; simp at h
           have htv : ψ (t - v) ≠ 0 := by
             intro zero
             rw [zero] at h; simp at h
           rw [← Function.mem_support] at hv htv
           have h_supp_psi : support ψ = Metric.ball 0 (φ i).rOut := by
             dsimp [ψ]
             simp only [(φ i).support_normed_eq]
           rw [h_supp_psi, Metric.mem_ball, dist_zero_right] at hv htv
           dsimp [K, K_t, K_v]
           rw [mem_prod, Metric.mem_closedBall, Metric.mem_closedBall, dist_zero_right, dist_zero_right]
           constructor
           · calc ‖t‖ = ‖(t-v) + v‖ := by abel_nf
                  _ ≤ ‖t-v‖ + ‖v‖ := norm_add_le _ _
                  _ ≤ (φ i).rOut + (φ i).rOut := add_le_add (le_of_lt htv) (le_of_lt hv)
                  _ = 2 * (φ i).rOut := by ring
           · exact le_of_lt hv

         -- Continuity on K
         have h_cont_F : ContinuousOn F K := by
            apply ContinuousOn.mul
            · apply ContinuousOn.mul
              · have h_cont_ψ : Continuous ψ := (φ i).continuous_normed
                exact Continuous.continuousOn (h_cont_ψ.comp continuous_snd)
              · have h_cont_ψ : Continuous ψ := (φ i).continuous_normed
                exact Continuous.continuousOn (h_cont_ψ.comp (continuous_fst.sub continuous_snd))
            · apply ContinuousOn.comp hC
              · exact Continuous.continuousOn (continuous_const.sub continuous_fst)
              · intro ⟨t, v⟩ htv
                dsimp [K, K_t, K_v] at htv
                simp only [mem_prod, Metric.mem_closedBall, dist_zero_right, mem_setOf_eq, sub_ne_zero] at htv ⊢
                by_contra h_ta
                rw [← h_ta] at htv
                have hr : (φ i).rOut < ‖a‖ / 3 := by
                   rw [mem_preimage, Metric.mem_ball, dist_zero_right] at hi
                   rw [Real.norm_of_nonneg (le_of_lt (φ i).rOut_pos)] at hi
                   exact hi
                have : ‖a‖ < ‖a‖ := by
                   rcases htv with ⟨ht, _⟩
                   calc ‖a‖ ≤ 2 * (φ i).rOut := ht
                        _ < 2 * (‖a‖ / 3) := mul_lt_mul_of_pos_left hr (by norm_num)
                        _ < ‖a‖ := by linarith [norm_nonneg a]
                linarith

         change Integrable F (volume.prod volume)
         rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset h_supp_F]
         exact h_cont_F.integrableOn_compact hK_compact

    rw [h_assoc]

  -- Use Tendsto.congr' with the eventually equal functions
  have h_eq' : ∀ᶠ i in l,
      (bumpSelfConv (φ i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C) a =
      (∫ x, ∫ y, (φ i).normed volume (x - a) * C (x - y) * (φ i).normed volume y) := by
    filter_upwards [h_eq] with i hi
    exact hi.symm
  exact Tendsto.congr' h_eq' h_selfconv_limit

end DoubleMollifierConvergence
