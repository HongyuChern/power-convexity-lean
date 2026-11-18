import PowerConvexity.Calculus.ActualHolderLoadSpaceTwo
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import CHS.Calculus.ClosureRegularity

/-! # A linear ambient representative of continuous closure data

Zero outside the closure is used only to select one ambient function. Interior
Fréchet derivatives are independent of that choice. Uniform convergence of
closure data gives uniform convergence of these actual representatives.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (U : Set E) [CompactSpace (closure U)]

def actualClosureExtensionTwo (f : C(closure U,F)) : E → F := by
  classical
  exact fun x => if hx : x ∈ closure U then f ⟨x,hx⟩ else 0

@[simp] theorem actualClosureExtensionTwo_apply (f : C(closure U,F))
    {x : E} (hx : x ∈ closure U) : actualClosureExtensionTwo U f x=f ⟨x,hx⟩ := by
  simp only [actualClosureExtensionTwo,dif_pos hx]

@[simp] theorem actualClosureExtensionTwo_zero :
    actualClosureExtensionTwo U (0 : C(closure U,F))=0 := by
  funext x
  simp only [actualClosureExtensionTwo,ContinuousMap.zero_apply,Pi.zero_apply,dite_eq_ite,ite_self]

@[simp] theorem actualClosureExtensionTwo_add (f g : C(closure U,F)) :
    actualClosureExtensionTwo U (f+g)=actualClosureExtensionTwo U f+actualClosureExtensionTwo U g := by
  funext x
  by_cases hx : x ∈ closure U
  · simp only [actualClosureExtensionTwo,dif_pos hx,ContinuousMap.add_apply,Pi.add_apply]
  · simp only [actualClosureExtensionTwo,dif_neg hx,Pi.add_apply,add_zero]

@[simp] theorem actualClosureExtensionTwo_smul (c : ℝ) (f : C(closure U,F)) :
    actualClosureExtensionTwo U (c • f)=c • actualClosureExtensionTwo U f := by
  funext x
  by_cases hx : x ∈ closure U
  · simp only [actualClosureExtensionTwo,dif_pos hx,ContinuousMap.smul_apply,Pi.smul_apply]
  · simp only [actualClosureExtensionTwo,dif_neg hx,Pi.smul_apply,smul_zero]

theorem actualClosureExtensionTwo_continuousOn (f : C(closure U,F)) :
    ContinuousOn (actualClosureExtensionTwo U f) (closure U) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : (closure U).domRestrict (actualClosureExtensionTwo U f)=f := by
    funext x
    exact actualClosureExtensionTwo_apply U f x.property
  rw [he]
  exact f.continuous

theorem actualClosureExtensionTwo_tendstoUniformly
    {ι : Type*} {l : Filter ι} {f : ι → C(closure U,F)} {g : C(closure U,F)}
    (hfg : Tendsto f l (𝓝 g)) :
    TendstoUniformly (fun n => actualClosureExtensionTwo U (f n))
      (actualClosureExtensionTwo U g) l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  filter_upwards [Metric.tendsto_nhds.mp hfg epsilon hepsilon] with n hn
  intro x
  by_cases hx : x ∈ closure U
  · simp only [actualClosureExtensionTwo_apply U _ hx]
    exact (ContinuousMap.dist_apply_le_dist (f := g) (g := f n) ⟨x,hx⟩).trans_lt (by simpa only [dist_comm] using hn)
  · simpa only [actualClosureExtensionTwo,dif_neg hx,dist_self] using hepsilon

end PowerConvexity
