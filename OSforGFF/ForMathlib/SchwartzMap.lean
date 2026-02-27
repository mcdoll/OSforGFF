import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

open scoped SchwartzMap


namespace SchwartzMap

noncomputable section translate

variable {𝕜 E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

variable (𝕜) in
/-- Translating the argument as a continuous linear map on Schwartz space. -/
def compSubConstCLM (a : E) : 𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  compCLMOfAntilipschitz (g := fun x ↦ x - a) (K := 1) 𝕜 (by fun_prop)
    (fun _ _ ↦ by simp [edist_dist, dist_eq_norm])

@[simp]
theorem compSubConstCLM_apply (f : 𝓢(E, F)) (a x : E) :
    f.compSubConstCLM 𝕜 a x = f (x - a) := rfl

@[simp]
theorem compSubConstCLM_zero : compSubConstCLM 𝕜 (0 : E) (F := F) = ContinuousLinearMap.id _ _ := by
  ext f x
  simp

@[simp]
theorem compSubConstCLM_comp (f : 𝓢(E, F)) (a b : E) :
    (f.compSubConstCLM 𝕜 a).compSubConstCLM 𝕜 b = f.compSubConstCLM 𝕜 (a + b) := by
  ext x
  simp only [compSubConstCLM_apply]
  congr 1
  exact (sub_add_eq_sub_sub_swap x a b).symm

end translate

noncomputable
section Postcomp

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedSpace 𝕜 H]

/-- Postcomposition with a continuous linear map is a continuous linear map on Schwartz
functions. -/
def postcompCLM (L : F →L[𝕜] G) : 𝓢(E, F) →L[𝕜] 𝓢(E, G) := by
  refine mkCLM (fun f ↦ L ∘ f) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
    (fun f ↦ (L.restrictScalars ℝ).contDiff.comp (f.smooth ⊤)) ?_
  intro ⟨k, n⟩
  use {⟨k, n⟩}, ‖L‖, by positivity
  intro f x
  simp only [Finset.sup_singleton, schwartzSeminormFamily_apply]
  calc
    _ = ‖x‖ ^ k * ‖(L.restrictScalars ℝ).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n f x)‖ := by
      congr
      exact (L.restrictScalars ℝ).iteratedFDeriv_comp_left f.smooth'.contDiffAt (mod_cast le_top)
    _ ≤ ‖x‖ ^ k * (‖L‖ * ‖iteratedFDeriv ℝ n f x‖) := by
      gcongr
      apply (L.restrictScalars ℝ).norm_compContinuousMultilinearMap_le
    _ = ‖L‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by ring
    _ ≤ ‖L‖ * (SchwartzMap.seminorm 𝕜 k n) f := by
      grw [le_seminorm 𝕜 k n f x]

@[simp]
theorem postcompCLM_apply (L : F →L[𝕜] G) (f : 𝓢(E, F)) (x : E) : f.postcompCLM L x = L (f x) :=
  rfl

@[simp]
theorem postcompCLM_postcompCLM (L₁ : F →L[𝕜] G) (L₂ : G →L[𝕜] H) (f : 𝓢(E, F)) :
  (f.postcompCLM L₁).postcompCLM L₂ = f.postcompCLM (L₂ ∘L L₁) := rfl

end Postcomp
