import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere

open MeasureTheory

/-! ## Local Integrability of Power-Law Decay Functions

Functions with polynomial decay are locally integrable in finite dimensions.
-/

open Set Metric in
/-- Local version of `integrable_fun_norm_addHaar`: integrability of radial functions on balls.
    If the radial part is integrable on (0, r), then the function is integrable on ball 0 r.

    Key technique: Use indicator functions to reduce to the global `integrable_fun_norm_addHaar`.
    - Define g := indicator (Iio r) f, so g(y) = f(y) for y < r, else 0
    - Then indicator (ball 0 r) (f ∘ ‖·‖) = g ∘ ‖·‖
    - Apply global lemma to g -/
lemma integrableOn_ball_of_radial {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : ℝ → F} {r : ℝ} (_hr : 0 < r)
    (hint : IntegrableOn (fun y => y ^ (Module.finrank ℝ E - 1) • f y) (Ioo 0 r) volume) :
    IntegrableOn (fun x : E => f ‖x‖) (ball (0 : E) r) μ := by
  -- Key: indicator (ball 0 r) (f ∘ ‖·‖) = (indicator (Iio r) f) ∘ ‖·‖
  have h_eq : indicator (ball (0 : E) r) (fun x : E => f ‖x‖) =
      fun x : E => indicator (Iio r) f ‖x‖ := by
    ext x
    simp only [indicator, mem_ball_zero_iff, mem_Iio]
  -- IntegrableOn ↔ Integrable of indicator
  rw [← integrable_indicator_iff measurableSet_ball, h_eq]
  -- Now apply the global lemma integrable_fun_norm_addHaar
  rw [integrable_fun_norm_addHaar μ (f := indicator (Iio r) f)]
  -- The RHS is IntegrableOn (y^(d-1) • (indicator (Iio r) f) y) (Ioi 0)
  -- Since indicator (Iio r) f = 0 on [r, ∞), this equals IntegrableOn (y^(d-1) • f y) (Ioo 0 r)
  have h_supp : ∀ y ∈ Ioi (0 : ℝ), y ^ (Module.finrank ℝ E - 1) • indicator (Iio r) f y =
      indicator (Ioo 0 r) (fun y => y ^ (Module.finrank ℝ E - 1) • f y) y := by
    intro y hy
    simp only [indicator, mem_Ioo, mem_Iio, mem_Ioi] at hy ⊢
    by_cases hyr : y < r
    · simp only [hyr, hy, and_self, ↓reduceIte]
    · simp only [hyr, hy, and_false, ↓reduceIte, smul_zero]
  rw [integrableOn_congr_fun h_supp measurableSet_Ioi]
  rw [← integrable_indicator_iff measurableSet_Ioo] at hint
  exact hint.integrableOn -- finishes the proof
  /-rw [← integrableOn_univ] at hint
  rw [MeasureTheory.integrableOn_congr_set_ae (t := Set.univ)]
  · exact hint
  · -- nah
    sorry-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open Set Metric in
/-- Integrability on balls for power-law decay functions.
    If |f(x)| ≤ C‖x‖^{-α} with α < d, then f is integrable on any ball centered at 0. -/
lemma integrableOn_ball_of_rpow_decay' (hd : 1 ≤ Module.finrank ℝ E)
    {f : E → ℝ} {C α r : ℝ}
    (_hC : 0 < C) (hα : α < Module.finrank ℝ E) (hr : 0 < r)
    (h_decay : ∀ x, |f x| ≤ C * ‖x‖ ^ (-α))
    (h_meas : AEStronglyMeasurable f volume) :
    IntegrableOn f (ball (0 : E) r) volume := by
  -- We apply integrableOn_ball_of_radial with the bound function g(y) = C * y^(-α)
  -- The radial integral becomes ∫_0^r y^(d-1) * C * y^(-α) dy = C * ∫_0^r y^(d-1-α) dy
  -- which converges when d-1-α > -1, i.e., α < d

  -- First show the bound function is radially integrable
  haveI : Nontrivial E := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    positivity
  have hint : IntegrableOn (fun y => y ^ (Module.finrank ℝ E - 1) • (C * y ^ (-α)))
      (Ioo 0 r) volume := by
    simp only [smul_eq_mul]
    -- Simplify y^(d-1) * (C * y^(-α)) = C * y^(d-1-α)
    have h_simp : ∀ y ∈ Ioo (0 : ℝ) r, (y : ℝ) ^ (Module.finrank ℝ E - 1) * (C * y ^ (-α)) = C * y ^ ((Module.finrank ℝ E : ℝ) - 1 - α) := by
      intro y hy
      have hy_pos : 0 < y := hy.1
      rw [mul_comm (y ^ _), mul_assoc]
      congr 1
      rw [← Real.rpow_natCast y (Module.finrank ℝ E - 1), ← Real.rpow_add hy_pos]
      congr 1
      simp only [Nat.cast_sub hd]
      ring
    rw [integrableOn_congr_fun h_simp measurableSet_Ioo]
    -- Now show IntegrableOn (C * y^(d-1-α)) (Ioo 0 r)
    -- First show the rpow part is integrable
    have h_rpow : IntegrableOn (fun y => y ^ ((Module.finrank ℝ E : ℝ) - 1 - α)) (Ioo 0 r) volume := by
      rw [intervalIntegral.integrableOn_Ioo_rpow_iff hr]
      linarith
    exact h_rpow.const_mul C

  -- Now use integrableOn_ball_of_radial and monotonicity
  have h_bound := integrableOn_ball_of_radial volume hr hint
  -- h_bound : IntegrableOn (fun x => C * ‖x‖^(-α)) (ball 0 r) volume

  -- Show f is dominated by the bound
  apply Integrable.mono' h_bound h_meas.restrict
  filter_upwards with x
  simp only [Real.norm_eq_abs]
  exact h_decay x


theorem foo (hdim : 1 ≤ Module.finrank ℝ E ) {f : E → ℝ} {C α : ℝ}
    (hC : 0 < C) (hα : α < Module.finrank ℝ E)
    (h_decay : ∀ x, |f x| ≤ C * ‖x‖ ^ (-α)) (h_meas : AEStronglyMeasurable f volume) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR_pos, hR⟩ := hK.isBounded.exists_pos_norm_lt
  apply IntegrableOn.mono_set (t := Metric.ball 0 R) ?_ (fun x hx ↦ mem_ball_zero_iff.mpr (hR x hx))
  apply integrableOn_ball_of_rpow_decay' hdim hC hα hR_pos h_decay h_meas

/-- Functions with polynomial decay are locally integrable.
    For d-dimensional space, if α < d and |f(x)| ≤ C‖x‖^{-α}, then f is locally integrable. -/
theorem locallyIntegrable_of_rpow_decay_real {d : ℕ} (hd : d ≥ 3)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} {α : ℝ}
    (hC : C > 0) (hα : α < d)
    (h_decay : ∀ x, |f x| ≤ C * ‖x‖ ^ (-α))
    (h_meas : AEStronglyMeasurable f volume) :
    LocallyIntegrable f volume := by
  refine foo ?_ hC ?_ h_decay h_meas
  · simp only [finrank_euclideanSpace, Fintype.card_fin]
    linarith
  · simp [hα]

/-- **Polynomial decay is integrable in 3D**: The function 1/(1+‖x‖)^4 is integrable
    over SpatialCoords = EuclideanSpace ℝ (Fin 3).

    This is a standard result: decay rate 4 > dimension 3 ensures integrability.

    **Mathematical content**: In ℝ³ with spherical coordinates,
    ∫ 1/(1+r)^4 · r² dr dΩ = 4π ∫₀^∞ r²/(1+r)^4 dr < ∞
    since the integrand decays as r⁻² for large r.

    **Used by**: `spatialNormIntegral_linear_bound` and `F_norm_bound_via_linear_vanishing`
    to show that spatial integrals of Schwartz functions with linear time vanishing
    are bounded by C·t. -/
lemma polynomial_decay_integrable_3d :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) => 1 / (1 + ‖x‖)^4) volume := by
  -- Use integrable_one_add_norm: (1 + ‖x‖)^(-r) is integrable when r > dim
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace
  have hdim_lt : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) < (4 : ℝ) := by
    rw [hdim]; norm_num
  have h_int := integrable_one_add_norm (E := EuclideanSpace ℝ (Fin 3)) (μ := volume) (r := 4) hdim_lt
  -- Convert (1 + ‖x‖)^(-4) to 1 / (1 + ‖x‖)^4
  convert h_int using 1
  ext x
  have h_pos : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
  simp only [Real.rpow_neg (le_of_lt h_pos), one_div]
  congr 1
  exact (Real.rpow_natCast (1 + ‖x‖) 4).symm
