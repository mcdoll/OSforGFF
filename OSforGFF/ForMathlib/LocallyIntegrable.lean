import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere

open MeasureTheory

/-! ## Local Integrability of Power-Law Decay Functions

Functions with polynomial decay are locally integrable in finite dimensions.
-/

section radial

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [μ.IsAddHaarMeasure]

open Set Metric in
/-- A radial function `x ↦ f ‖x‖` is integrable on a ball if and only if `fun x ↦ x ^ (d - 1) • f x` is integrable
on the interval. -/
lemma integrableOn_fun_norm_addHaar
    {f : ℝ → F} {r : ℝ} (_hr : 0 < r) :
    IntegrableOn (fun x : E => f ‖x‖) (ball (0 : E) r) μ ↔
    IntegrableOn (fun y => y ^ (Module.finrank ℝ E - 1) • f y) (Ioo 0 r) volume := by
  calc
    _ ↔ Integrable (fun x ↦ (Iio r).indicator f ‖x‖) μ := by
      rw [← integrable_indicator_iff measurableSet_ball]
      apply integrable_congr
      filter_upwards with x
      simp [indicator]
    _ ↔ IntegrableOn ((Ioo 0 r).indicator fun y ↦ y ^ (Module.finrank ℝ E - 1) • f y) (Ioi 0) volume := by
      rw [integrable_fun_norm_addHaar μ (f := indicator (Iio r) f),
        integrableOn_congr_fun _ measurableSet_Ioi]
      intro x (hx : 0 < x)
      by_cases hxr : x < r <;> simp [hxr, hx]
    _ ↔ Integrable ((Ioo 0 r).indicator fun y ↦ y ^ (Module.finrank ℝ E - 1) • f y) volume  := by
      rw [MeasureTheory.integrableOn_iff_integrable_of_support_subset]
      intro x hx
      simp only [support_indicator, mem_inter_iff, mem_Ioo, Function.mem_support, ne_eq,
        smul_eq_zero, pow_eq_zero_iff', not_or, not_and, Decidable.not_not] at hx
      refine mem_Ioi.mpr hx.1.1
    _ ↔ IntegrableOn (fun y ↦ y ^ (Module.finrank ℝ E - 1) • f y) (Ioo 0 r) volume := by
      rw [← integrable_indicator_iff measurableSet_Ioo, ← integrableOn_univ]

end radial

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F]

open Set Metric in
/-- Integrability on balls for power-law decay functions.
    If |f(x)| ≤ C‖x‖^{-α} with α < d, then f is integrable on any ball centered at 0. -/
lemma integrableOn_ball_of_rpow_decay' (hd : 1 ≤ Module.finrank ℝ E)
    {f : E → F} {C α r : ℝ}
    (_hC : 0 < C) (hα : α < Module.finrank ℝ E) (hr : 0 < r)
    (h_decay : ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ (-α))
    (h_meas : AEStronglyMeasurable f volume) :
    IntegrableOn f (ball (0 : E) r) volume := by
  haveI : Nontrivial E := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    positivity
  have hint : IntegrableOn (fun y => y ^ (Module.finrank ℝ E - 1) • (C * y ^ (-α)))
      (Ioo 0 r) volume := by
    simp only [smul_eq_mul]
    have h_rpow : IntegrableOn (fun y => y ^ ((Module.finrank ℝ E : ℝ) - 1 - α)) (Ioo 0 r) volume := by
      rw [intervalIntegral.integrableOn_Ioo_rpow_iff hr]
      linarith
    apply IntegrableOn.congr_fun (h_rpow.const_mul C) ?_ measurableSet_Ioo
    intro y ⟨hy₁, hy₂⟩
    simp only
    move_mul [C]
    rw [← Real.rpow_natCast y (Module.finrank ℝ E - 1), ← Real.rpow_add hy₁]
    congr
    norm_cast
  rw [← integrableOn_fun_norm_addHaar volume hr] at hint
  apply Integrable.mono' hint h_meas.restrict
  filter_upwards with x
  exact h_decay x


theorem foo (hdim : 1 ≤ Module.finrank ℝ E ) {f : E → F} {C α : ℝ}
    (hC : 0 < C) (hα : α < Module.finrank ℝ E)
    (h_decay : ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ (-α)) (h_meas : AEStronglyMeasurable f volume) :
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
