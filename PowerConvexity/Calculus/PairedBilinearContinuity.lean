import PowerConvexity.Calculus.LeviDefiningStabilization

/-! # Continuity of the paired real bilinear form -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_pairedBilinearForm (I : E →L[ℝ] E) :
    Continuous (fun H : E →L[ℝ] E →L[ℝ] ℝ => pairedBilinearForm I H) := by
  letI : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toAddCommGroup
  letI : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
  letI : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
  unfold pairedBilinearForm
  exact continuous_id.add (continuous_const.clm_comp (continuous_id.clm_comp continuous_const))

end PowerConvexity
