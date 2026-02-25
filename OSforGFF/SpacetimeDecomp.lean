/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import OSforGFF.Basic
--import OSforGFF.SchwartzProdIntegrable

/-!
# Spacetime Decomposition

This file provides the measure-preserving decomposition of SpaceTime into
time and spatial components: SpaceTime ≃ᵐ ℝ × SpatialCoords.

## Main Definitions

* `piLpMeasurableEquiv` - MeasurableEquiv between PiLp and underlying pi type
* `spacetimeDecomp` - The measurable equivalence SpaceTime ≃ᵐ ℝ × SpatialCoords

## Main Results

* `spacetimeDecomp_measurePreserving` - The decomposition preserves Lebesgue measure
* `spacetimeDecomp_apply` - Explicit formula: spacetimeDecomp k = (k 0, spatialPart k)
* `spacetime_norm_sq_decompose` - Norm decomposition: ‖k‖² = k₀² + ‖k_sp‖²
-/

open MeasureTheory MeasureSpace FiniteDimensional Real

/-! ### Integral Decomposition for SpaceTime

We establish that integrals over SpaceTime can be decomposed into
iterated integrals over ℝ (time component) and SpatialCoords (spatial components).
This uses `MeasurableEquiv.piFinSuccAbove` and `measurePreserving_piFinSuccAbove`.

-/

/-- MeasurableEquiv between PiLp and the underlying pi type. -/
def piLpMeasurableEquiv (n : ℕ) : PiLp 2 (fun _ : Fin n => ℝ) ≃ᵐ (Fin n → ℝ) where
  toEquiv := WithLp.equiv 2 _
  measurable_toFun := WithLp.measurable_ofLp 2 _
  measurable_invFun := WithLp.measurable_toLp 2 _

/-- The measurable equivalence from SpaceTime to ℝ × SpatialCoords.
    Composes three measure-preserving maps:
    1. piLpMeasurableEquiv : EuclideanSpace ℝ (Fin 4) → (Fin 4 → ℝ)
    2. piFinSuccAbove 0 : (Fin 4 → ℝ) → ℝ × (Fin 3 → ℝ)
    3. id × piLpMeasurableEquiv.symm : ℝ × (Fin 3 → ℝ) → ℝ × SpatialCoords -/
def spacetimeDecomp : SpaceTime ≃ᵐ ℝ × SpatialCoords :=
  (piLpMeasurableEquiv STDimension).trans
  ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
    (piLpMeasurableEquiv (STDimension - 1)).symm))

/-- Measure preservation for piLpMeasurableEquiv. -/
lemma piLpMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (piLpMeasurableEquiv n)
      (volume : Measure (PiLp 2 (fun _ : Fin n => ℝ))) volume := by
  simp only [piLpMeasurableEquiv, MeasurableEquiv.coe_mk]
  exact PiLp.volume_preserving_ofLp (ι := Fin n)

/-- The spacetime decomposition preserves measure. -/
theorem spacetimeDecomp_measurePreserving :
    MeasurePreserving spacetimeDecomp (volume : Measure SpaceTime) volume := by
  unfold spacetimeDecomp
  -- Step 1: PiLp → (Fin 4 → ℝ) is measure-preserving
  have h1 : MeasurePreserving (piLpMeasurableEquiv STDimension)
      (volume : Measure SpaceTime) volume :=
    piLpMeasurableEquiv_measurePreserving STDimension
  -- Step 2: piFinSuccAbove 0 is measure-preserving
  have h2 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)
      (volume : Measure (Fin STDimension → ℝ)) volume :=
    measurePreserving_piFinSuccAbove (fun _ => volume) 0
  -- Step 3: id × piLpMeasurableEquiv.symm is measure-preserving
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (piLpMeasurableEquiv (STDimension - 1)).symm)
      (volume : Measure (ℝ × (Fin (STDimension - 1) → ℝ))) volume := by
    apply MeasurePreserving.prod
    · exact MeasurePreserving.id volume
    · simp only [piLpMeasurableEquiv, MeasurableEquiv.symm_mk]
      exact PiLp.volume_preserving_toLp (ι := Fin (STDimension - 1))
  exact h1.trans (h2.trans h3)

/-- Spacetime decomposition maps k to (k 0, spatialPart k). -/
theorem spacetimeDecomp_apply (k : SpaceTime) :
    spacetimeDecomp k = (k 0, spatialPart k) := rfl
