import Mathlib.Analysis.Distribution.SchwartzSpace.Basic


noncomputable section translate

open scoped SchwartzMap


namespace SchwartzMap

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

end SchwartzMap

end translate
