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
  -- IntegrableOn (indicator (Ioo 0 r) g) (Ioi 0) ← IntegrableOn g (Ioo 0 r) since Ioo 0 r ⊆ Ioi 0
  have : Integrable (indicator (Ioo 0 r) (fun y => y ^ (Module.finrank ℝ E - 1) • f y)) volume :=
    hint.integrable_indicator measurableSet_Ioo
  exact this.integrableOn

open Set Metric in
/-- Integrability on balls for power-law decay functions.
    If |f(x)| ≤ C‖x‖^{-α} with α < d, then f is integrable on any ball centered at 0. -/
lemma integrableOn_ball_of_rpow_decay {d : ℕ} (hd : d ≥ 1)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {C α r : ℝ}
    (_hC : 0 < C) (hα : α < d) (hr : 0 < r)
    (h_decay : ∀ x, |f x| ≤ C * ‖x‖ ^ (-α))
    (h_meas : AEStronglyMeasurable f volume) :
    IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin d)) r) volume := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  -- We apply integrableOn_ball_of_radial with the bound function g(y) = C * y^(-α)
  -- The radial integral becomes ∫_0^r y^(d-1) * C * y^(-α) dy = C * ∫_0^r y^(d-1-α) dy
  -- which converges when d-1-α > -1, i.e., α < d

  -- First show the bound function is radially integrable
  have hint : IntegrableOn (fun y => y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1) • (C * y ^ (-α)))
      (Ioo 0 r) volume := by
    have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
    simp only [hfinrank, smul_eq_mul]
    -- Simplify y^(d-1) * (C * y^(-α)) = C * y^(d-1-α)
    have h_simp : ∀ y ∈ Ioo (0 : ℝ) r, (y : ℝ) ^ (d - 1) * (C * y ^ (-α)) = C * y ^ ((d : ℝ) - 1 - α) := by
      intro y hy
      have hy_pos : 0 < y := hy.1
      rw [mul_comm (y ^ _), mul_assoc]
      congr 1
      rw [← Real.rpow_natCast y (d - 1), ← Real.rpow_add hy_pos]
      congr 1
      simp only [Nat.cast_sub hd]
      ring
    rw [integrableOn_congr_fun h_simp measurableSet_Ioo]
    -- Now show IntegrableOn (C * y^(d-1-α)) (Ioo 0 r)
    -- First show the rpow part is integrable
    have h_rpow : IntegrableOn (fun y => y ^ ((d : ℝ) - 1 - α)) (Ioo 0 r) volume := by
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

/-- Integrability away from the origin for bounded functions on compact sets. -/
lemma integrableOn_compact_diff_ball {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {C α δ : ℝ} {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hC : 0 < C) (hδ : 0 < δ)
    (h_decay : ∀ x, |f x| ≤ C * ‖x‖ ^ (-α))
    (h_meas : AEStronglyMeasurable f volume) :
    IntegrableOn f (K \ Metric.ball 0 δ) volume := by
  -- On K \ ball 0 δ, ‖x‖ ≥ δ > 0 so the bound C * ‖x‖^(-α) is bounded
  have h_finite : volume (K \ Metric.ball 0 δ) < ⊤ :=
    (hK.diff Metric.isOpen_ball).measure_lt_top
  by_cases hne : (K \ Metric.ball 0 δ).Nonempty
  · -- The set is nonempty
    obtain ⟨R, hR_pos, hR⟩ := hK.isBounded.exists_pos_norm_le
    -- On K \ ball 0 δ, we have δ ≤ ‖x‖ ≤ R, so ‖x‖^(-α) is bounded
    -- Use M = C * max (δ^(-α)) (R^(-α)) as bound (handles both signs of α)
    let M := C * max (δ ^ (-α)) (R ^ (-α))
    have hM_pos : 0 < M := by positivity
    have h_bound : ∀ x ∈ K \ Metric.ball 0 δ, |f x| ≤ M := by
      intro x hx
      have hx_in_K : x ∈ K := hx.1
      have hx_norm_lower : δ ≤ ‖x‖ := by
        simp only [Set.mem_diff, Metric.mem_ball, dist_zero_right, not_lt] at hx
        exact hx.2
      have hx_norm_upper : ‖x‖ ≤ R := hR x hx_in_K
      have hx_norm_pos : 0 < ‖x‖ := hδ.trans_le hx_norm_lower
      calc |f x| ≤ C * ‖x‖ ^ (-α) := h_decay x
        _ ≤ M := by
          show C * ‖x‖ ^ (-α) ≤ C * max (δ ^ (-α)) (R ^ (-α))
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
          by_cases hα_nonneg : 0 ≤ α
          · -- α ≥ 0: -α ≤ 0, so rpow is antitone, ‖x‖^(-α) ≤ δ^(-α)
            have h1 : ‖x‖ ^ (-α) ≤ δ ^ (-α) := by
              apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr hα_nonneg))
              · exact hδ
              · exact hx_norm_pos
              · exact hx_norm_lower
            exact le_max_of_le_left h1
          · -- α < 0: -α > 0, so rpow is monotone, ‖x‖^(-α) ≤ R^(-α)
            push_neg at hα_nonneg
            have h1 : ‖x‖ ^ (-α) ≤ R ^ (-α) := by
              apply Real.rpow_le_rpow (le_of_lt hx_norm_pos) hx_norm_upper
              linarith
            exact le_max_of_le_right h1
    have hM_bound : ∀ x ∈ K \ Metric.ball 0 δ, ‖f x‖ ≤ M := fun x hx => by
      rw [Real.norm_eq_abs]
      exact h_bound x hx
    have h_const : IntegrableOn (fun _ => M) (K \ Metric.ball 0 δ) volume :=
      MeasureTheory.integrableOn_const (μ := volume) (s := K \ Metric.ball 0 δ)
        (by exact ne_top_of_lt h_finite)
    have h_ae : ∀ᵐ x ∂(volume.restrict (K \ Metric.ball 0 δ)), ‖f x‖ ≤ M := by
      rw [ae_restrict_iff' (hK.diff Metric.isOpen_ball).measurableSet]
      exact ae_of_all _ hM_bound
    exact h_const.mono' h_meas.restrict h_ae
  · -- The set is empty
    rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact integrableOn_empty

/-- Functions with polynomial decay are locally integrable.
    For d-dimensional space, if α < d and |f(x)| ≤ C‖x‖^{-α}, then f is locally integrable. -/
theorem locallyIntegrable_of_rpow_decay_real {d : ℕ} (hd : d ≥ 3)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} {α : ℝ}
    (hC : C > 0) (hα : α < d)
    (h_decay : ∀ x, |f x| ≤ C * ‖x‖ ^ (-α))
    (h_meas : AEStronglyMeasurable f volume) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  -- Cover K with ball 0 1 and K \ ball 0 (1/2)
  have h_cover : K ⊆ (K ∩ Metric.ball 0 1) ∪ (K \ Metric.ball 0 (1/2)) := by
    intro x hx
    by_cases hxb : x ∈ Metric.ball 0 1
    · exact Or.inl ⟨hx, hxb⟩
    · simp only [Metric.mem_ball, dist_zero_right, not_lt] at hxb
      right
      constructor
      · exact hx
      · simp only [Metric.mem_ball, dist_zero_right, not_lt]
        linarith
  apply IntegrableOn.mono_set _ h_cover
  apply IntegrableOn.union
  · -- IntegrableOn f (K ∩ ball 0 1)
    apply IntegrableOn.mono_set _ Set.inter_subset_right
    exact integrableOn_ball_of_rpow_decay (by omega : d ≥ 1) hC hα (by norm_num : (0:ℝ) < 1)
      h_decay h_meas
  · -- IntegrableOn f (K \ ball 0 (1/2))
    exact integrableOn_compact_diff_ball hK hC (by norm_num : (0:ℝ) < 1/2) h_decay h_meas

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
