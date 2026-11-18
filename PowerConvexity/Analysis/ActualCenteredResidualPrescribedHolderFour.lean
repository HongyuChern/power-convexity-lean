import PowerConvexity.Analysis.ActualCenteredScalarCoeffFour
import PowerConvexity.Analysis.ActualUniformClassicalPrescribedHolderFour

/-! # Actual residual Schauder control with continuous Holder source and unchanged exponent -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_centered_residual_prescribed_holder_four {lam Lambda Ka Kf F B alpha : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf)
    (hF : 0 ≤ F) (hB : 0 ≤ B) (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∃ delta > 0, delta ≤ (1/8 : ℝ) ∧ ∃ M ≥ 0, ∀ U : Set E, IsOpen U → ∀ A : EllipticCoeff (2+2) U,
    lam ≤ A.lam → A.Λ ≤ Lambda → (∀ x ∈ U, (A.a x).PosDef) →
    (∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) U) →
    (∀ x ∈ U, ∀ j, (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1))=0) →
    ∀ c : E, ∀ r b : ℝ, 0 < r → 0 < b → MapsTo (fun z : E => c+r • z) (ball (0 : E) 2) U →
    ∀ f u q : E → ℝ, ContinuousOn f U → ContDiffOn ℝ 2 u U → IsQuadraticPolynomial q →
    (∀ x ∈ U, (∑ i, ∑ j, A.a x i j*euclideanHessian u x i j) = -f x) →
    (∀ x ∈ ball (0 : E) 2, ∀ y ∈ ball (0 : E) 2,
      ‖actualMatrixOperatorTwo (A.a (c+r • x))-actualMatrixOperatorTwo (A.a (c+r • y))‖ ≤ Ka*‖x-y‖^alpha) →
    (∀ x ∈ ball (0 : E) 2, ∀ y ∈ ball (0 : E) 2,
      |b⁻¹*(f (c+r • x)-quadraticScalarSourceTwo A.a q (c+r • x))-
        b⁻¹*(f (c+r • y)-quadraticScalarSourceTwo A.a q (c+r • y))| ≤ Kf*‖x-y‖^alpha) →
    (∀ x ∈ ball (0 : E) 2, |b⁻¹*(f (c+r • x)-quadraticScalarSourceTwo A.a q (c+r • x))| ≤ F) →
    (∀ x ∈ ball (0 : E) 2, |actualCenteredResidualFour c r b u q x| ≤ B) →
    ‖fderiv ℝ u c-fderiv ℝ q c‖ ≤ (b*r)*M ∧
      ‖realHessian u c-realHessian q c‖ ≤ b*M ∧
      ∀ z ∈ ball (0 : E) delta, ∀ w ∈ ball (0 : E) delta,
        ‖realHessian u (c+r • z)-realHessian u (c+r • w)‖ ≤ b*M*‖z-w‖^alpha := by
  obtain ⟨delta,hd,hd8,M,hM,hcenter⟩ :=
    actual_uniform_classical_prescribed_holder_four hlam hLambda hKa hKf hF hB halpha halpha1
  refine ⟨delta,hd,hd8,M,hM,?_⟩
  intro U hU A hlo hhi hpos hreg hdiv c r b hr hb hmap f u q hf hu hq hpde hhold hfhold hfb hub
  let A' := actualCenteredScalarCoeffFour c hr A hmap
  let g : E → ℝ := fun z => b⁻¹*(f (c+r • z)-quadraticScalarSourceTwo A.a q (c+r • z))
  let v := actualCenteredResidualFour c r b u q
  have ht (n : ℕ∞ω) : ContDiffOn ℝ n (fun z : E => c+r • z) (ball (0 : E) 2) := by fun_prop
  have hg : ContinuousOn g (ball (0 : E) 2) :=
    continuousOn_const.mul ((hf.sub (actual_quadratic_scalar_source_contDiffOn_four hreg hq).continuousOn).comp
      (ht 1).continuousOn hmap)
  have hv : ContDiffOn ℝ 2 v (ball (0 : E) 2) :=
    contDiffOn_const.mul ((hu.sub (IsQuadraticPolynomial_contDiff hq 2).contDiffOn).comp (ht 2) hmap)
  have hD := hcenter A' hlo hhi (fun z hz => hpos _ (hmap hz))
    (actual_centered_scalar_coeff_regular_four c hr A hmap hreg)
    (actual_centered_scalar_coeff_divergence_four hU c hr A hmap hreg hdiv) hhold
    g v hg hfhold hfb hv hub (fun z hz =>
      actual_centered_residual_equation_four hU c hr hu hq hpde z (hmap hz))
  have hc : c ∈ U := by simpa only [smul_zero,add_zero] using hmap (mem_ball_self (by norm_num : (0 : ℝ) < 2))
  have huc : ContDiffAt ℝ 2 u c := hu.contDiffAt (hU.mem_nhds hc)
  have hqc : ContDiffAt ℝ 2 q c := (IsQuadraticPolynomial_contDiff hq 2).contDiffAt
  have heD : fderiv ℝ v 0=(b⁻¹*r⁻¹) • (fderiv ℝ u c-fderiv ℝ q c) := by
    simpa only [smul_zero,add_zero] using actual_centered_residual_fderiv_four c hr
      (z := (0 : E)) (by simpa only [smul_zero,add_zero] using huc.differentiableAt (by norm_num))
      (by simpa only [smul_zero,add_zero] using hqc.differentiableAt (by norm_num))
  have heH : realHessian v 0=b⁻¹ • (realHessian u c-realHessian q c) := by
    simpa only [smul_zero,add_zero] using actual_centered_residual_hessian_four c hr
      (z := (0 : E)) (by simpa only [smul_zero,add_zero] using huc)
      (by simpa only [smul_zero,add_zero] using hqc)
  have hd0 := (hD.1 0 (mem_ball_self hd)).2.1
  have hh0 := (hD.1 0 (mem_ball_self hd)).2.2
  rw [heD,norm_smul,Real.norm_eq_abs,abs_of_pos (mul_pos (inv_pos.mpr hb) (inv_pos.mpr hr))] at hd0
  rw [heH,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hb)] at hh0
  refine ⟨?_,?_,?_⟩
  · have he : (b*r)*((b⁻¹*r⁻¹)*‖fderiv ℝ u c-fderiv ℝ q c‖)=‖fderiv ℝ u c-fderiv ℝ q c‖ := by field_simp
    simpa only [he] using mul_le_mul_of_nonneg_left hd0 (mul_pos hb hr).le
  · have he : b*(b⁻¹*‖realHessian u c-realHessian q c‖)=‖realHessian u c-realHessian q c‖ := by field_simp
    simpa only [he] using mul_le_mul_of_nonneg_left hh0 hb.le

  · intro z hz w hw
    have hsub : ball (0 : E) delta ⊆ ball (0 : E) 2 := ball_subset_ball (by linarith)
    have hHz := actual_centered_residual_hessian_four (b := b) c hr
      (hu.contDiffAt (hU.mem_nhds (hmap (hsub hz))))
      (IsQuadraticPolynomial_contDiff hq 2).contDiffAt
    have hHw := actual_centered_residual_hessian_four (b := b) c hr
      (hu.contDiffAt (hU.mem_nhds (hmap (hsub hw))))
      (IsQuadraticPolynomial_contDiff hq 2).contDiffAt
    have hh := hD.2 z hz w hw
    change ‖realHessian (actualCenteredResidualFour c r b u q) z-
      realHessian (actualCenteredResidualFour c r b u q) w‖ ≤ M*‖z-w‖^alpha at hh
    rw [hHz,hHw] at hh
    rw [← _root_.smul_sub (b⁻¹ : ℝ)
      (realHessian u (c+r • z)-realHessian q (c+r • z))
      (realHessian u (c+r • w)-realHessian q (c+r • w))] at hh
    have he : (realHessian u (c+r • z)-realHessian q (c+r • z))-
        (realHessian u (c+r • w)-realHessian q (c+r • w))=
        realHessian u (c+r • z)-realHessian u (c+r • w) := by
      rw [quadratic_realHessian_from_jet_zero hq (c+r • z),
        quadratic_realHessian_from_jet_zero hq (c+r • w)]
      abel
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hb)] at hh
    have hs := mul_le_mul_of_nonneg_left hh hb.le
    have hcanc : b*(b⁻¹*‖realHessian u (c+r • z)-realHessian u (c+r • w)‖)=
        ‖realHessian u (c+r • z)-realHessian u (c+r • w)‖ := by field_simp
    simpa only [hcanc,mul_assoc] using hs

end PowerConvexity
