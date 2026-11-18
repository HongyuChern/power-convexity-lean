import PowerConvexity.Analysis.ActualRegularDomainGraphFour

/-! # Genuine inward graph coordinates from an unnormalized regular defining function -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_inward_defining_normalization {U : Set E} {x : E} {f : E → ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hf0 : f x=0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ y : E in 𝓝 x, y ∈ U ↔ f y < 0) :
    ∃ N : E, ‖N‖=1 ∧ ∃ g : E → ℝ, ContDiffAt ℝ 3 g 0 ∧ g 0=0 ∧
      (∀ v : E, fderiv ℝ g 0 v=inner ℝ N v) ∧
      ∀ᶠ y : E in 𝓝 0, x+y ∈ U ↔ 0 < g y := by
  let v := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hDv (w : E) : fderiv ℝ f x w=inner ℝ v w := InnerProductSpace.toDual_symm_apply.symm
  have hv : v ≠ 0 := by
    intro hz
    apply hDf
    ext w
    rw [hDv,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  let d := ‖v‖
  have hd : 0 < d := norm_pos_iff.mpr hv
  let N := (-d⁻¹) • v
  have hN : ‖N‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (inv_pos.mpr hd)]
    exact inv_mul_cancel₀ hd.ne'
  let g : E → ℝ := fun y => (-d⁻¹)*f (x+y)
  have htranslate : HasFDerivAt (fun y : E => x+y) (ContinuousLinearMap.id ℝ E) 0 :=
    (hasFDerivAt_id (𝕜 := ℝ) (0 : E)).const_add x
  have hfAt : ContDiffAt ℝ 3 f (x+(0 : E)) := by simpa only [add_zero] using hf
  have hfc : ContDiffAt ℝ 3 (fun y : E => f (x+y)) 0 := hfAt.comp 0 (by fun_prop)
  have hfd : HasFDerivAt (fun y : E => f (x+y)) (fderiv ℝ f x) 0 := by
    have hh := (hfAt.differentiableAt (by norm_num)).hasFDerivAt.comp 0 htranslate
    simpa only [Function.comp_def,add_zero,ContinuousLinearMap.comp_id] using hh
  have hgd : HasFDerivAt g ((-d⁻¹) • fderiv ℝ f x) 0 := hfd.const_smul (-d⁻¹)
  have ht : Tendsto (fun y : E => x+y) (𝓝 0) (𝓝 x) := by
    simpa only [add_zero] using htranslate.continuousAt.tendsto
  refine ⟨N,hN,g,contDiffAt_const.mul hfc,by simp only [g,add_zero,hf0,mul_zero],?_,?_⟩
  · intro w
    rw [hgd.fderiv]
    simp only [_root_.smul_apply,smul_eq_mul,N,real_inner_smul_left,hDv]
  · filter_upwards [ht.eventually hdef] with y hy
    apply hy.trans
    constructor
    · intro hneg
      exact mul_pos_of_neg_of_neg (neg_neg_of_pos (inv_pos.mpr hd)) hneg
    · intro hpos
      by_contra hn
      have hnonneg : 0 ≤ f (x+y) := le_of_not_gt hn
      have hnonpos : g y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_pos.mpr hd).le) hnonneg
      exact not_lt_of_ge hnonpos hpos

open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F4" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_inward_defining_graph_four {U : Set F4} {x : F4} {f : F4 → ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hf0 : f x=0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ y : F4 in 𝓝 x, y ∈ U ↔ f y < 0) :
    ∃ N : F4, ‖N‖=1 ∧ ∃ rho : F4 → ℝ, ContDiffAt ℝ 3 rho 0 ∧ rho 0=0 ∧ fderiv ℝ rho 0=0 ∧
      (∀ y : F4, ∀ t : ℝ, rho (y+t • N)=rho y) ∧
      ∃ R > 0, R ≤ 1 ∧ ∀ z ∈ closedBall (0 : F4) R,
        x+actualGraphShearFour N rho z ∈ U ↔ 0 < inner ℝ N z := by
  obtain ⟨N,hN,g,hg,hg0,hDg,hgdef⟩ := actual_inward_defining_normalization hf hf0 hDf hdef
  obtain ⟨rho,hrho,hrho0,hD0,hinv,R,hR,hR1,hmap⟩ := actual_regular_domain_graph_four
    (U := (fun y : F4 => x+y) ⁻¹' U) hN hg hg0 hDg hgdef
  exact ⟨N,hN,rho,hrho,hrho0,hD0,hinv,R,hR,hR1,hmap⟩

end PowerConvexity
