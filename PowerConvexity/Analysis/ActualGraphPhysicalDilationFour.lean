import PowerConvexity.Analysis.ActualGraphShearFour

/-! # Genuine physical dilation of the actual boundary graph -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualPhysicalGraphHeightFour (rho : E → ℝ) (R : ℝ) (z : E) : ℝ :=
  R⁻¹*rho (R • z)

theorem actual_physical_graph_conjugation_four {R : ℝ} (hR : R ≠ 0)
    (N : E) (rho : E → ℝ) (z : E) :
    R • actualGraphShearFour N (actualPhysicalGraphHeightFour rho R) z =
      actualGraphShearFour N rho (R • z) := by
  have he : R*(R⁻¹*rho (R • z))=rho (R • z) := by field_simp
  simp only [actualGraphShearFour,actualPhysicalGraphHeightFour,smul_add,smul_smul,he]

theorem actual_physical_graph_regularity_four {rho : E → ℝ} {R : ℝ}
    (hrho : ContDiffAt ℝ 3 rho 0) (hrho0 : rho 0=0) (hD0 : fderiv ℝ rho 0=0) :
    ContDiffAt ℝ 3 (actualPhysicalGraphHeightFour rho R) 0 ∧
      actualPhysicalGraphHeightFour rho R 0=0 ∧
      fderiv ℝ (actualPhysicalGraphHeightFour rho R) 0=0 := by
  have hc : ContDiffAt ℝ 3 (fun z : E => rho (R • z)) 0 := by
    have houter : ContDiffAt ℝ 3 rho (R • (0 : E)) := by simpa only [smul_zero] using hrho
    exact houter.comp 0 (contDiffAt_id.const_smul R)
  have hs : HasFDerivAt (fun z : E => R • z) (R • ContinuousLinearMap.id ℝ E) 0 :=
    (hasFDerivAt_id (𝕜 := ℝ) (0 : E)).const_smul R
  have hd : HasFDerivAt (fun z : E => rho (R • z)) (0 : E →L[ℝ] ℝ) 0 := by
    have hdouter : HasFDerivAt rho (0 : E →L[ℝ] ℝ) (R • (0 : E)) := by
      simpa only [smul_zero,hD0] using (hrho.differentiableAt (by norm_num)).hasFDerivAt
    simpa only [ContinuousLinearMap.zero_comp,Function.comp_def] using hdouter.comp 0 hs
  refine ⟨contDiffAt_const.mul hc,by simp only [actualPhysicalGraphHeightFour,smul_zero,hrho0,mul_zero],?_⟩
  have he : (R⁻¹ • fun z : E => rho (R • z))=actualPhysicalGraphHeightFour rho R := by
    funext z
    rfl
  have hh := (hd.const_smul R⁻¹).fderiv
  rw [he] at hh
  simpa only [smul_zero] using hh

theorem actual_physical_graph_normal_invariance_four {N : E} {rho : E → ℝ}
    (hinv : ∀ y : E, ∀ t : ℝ, rho (y+t • N)=rho y) (R : ℝ) (z : E) (t : ℝ) :
    actualPhysicalGraphHeightFour rho R (z+t • N)=actualPhysicalGraphHeightFour rho R z := by
  simp only [actualPhysicalGraphHeightFour,smul_add,smul_smul,hinv]

theorem actual_physical_graph_domain_four {U : Set E} {x N : E} {rho : E → ℝ}
    {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S)
    (hmap : ∀ z ∈ closedBall (0 : E) S,
      x+actualGraphShearFour N rho z ∈ U ↔ 0 < inner ℝ N z) :
    ∀ z ∈ closedBall (0 : E) 1,
      x+R • actualGraphShearFour N (actualPhysicalGraphHeightFour rho R) z ∈ U ↔
        0 < inner ℝ N z := by
  intro z hz
  have hz1 : ‖z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hz
  have hzR : R • z ∈ closedBall (0 : E) S := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    exact (mul_le_mul_of_nonneg_left hz1 hR.le).trans (by simpa only [mul_one] using hRS)
  rw [actual_physical_graph_conjugation_four hR.ne']
  exact (hmap _ hzR).trans (by rw [inner_smul_right]; exact mul_pos_iff_of_pos_left hR)

theorem actual_physical_graph_zero_boundary_four {x N : E} {rho u : E → ℝ}
    {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S)
    (hu : ∀ z ∈ closedBall (0 : E) (S/2), inner ℝ N z=0 →
      u (x+actualGraphShearFour N rho z)=0) :
    ∀ z ∈ closedBall (0 : E) (1/2), inner ℝ N z=0 →
      u (x+R • actualGraphShearFour N (actualPhysicalGraphHeightFour rho R) z)=0 := by
  intro z hz hNz
  have hz1 : ‖z‖ ≤ 1/2 := by simpa only [mem_closedBall,dist_zero_right] using hz
  have hzR : R • z ∈ closedBall (0 : E) (S/2) := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    have hh := mul_le_mul_of_nonneg_left hz1 hR.le
    linarith
  rw [actual_physical_graph_conjugation_four hR.ne']
  apply hu _ hzR
  simp only [inner_smul_right,hNz,mul_zero]

end PowerConvexity
