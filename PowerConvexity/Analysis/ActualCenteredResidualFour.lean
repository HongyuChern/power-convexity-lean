import PowerConvexity.Analysis.ActualAffineEllipticCoeffFour
import PowerConvexity.Analysis.ActualFlatResidualHolderFour

/-! # Exact actual residual jets and equation at a translated physical centre -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualCenteredResidualFour (c : E) (r b : ℝ) (u q : E → ℝ) (z : E) : ℝ :=
  b⁻¹*(r^2)⁻¹*(u (c+r • z)-q (c+r • z))

theorem actual_realHessian_translate_four {u : E → ℝ} (c x : E)
    (hu : ContDiffAt ℝ 2 u (c+x)) :
    realHessian (fun z => u (c+z)) x=realHessian u (c+x) := by
  ext v w
  simpa only [ContinuousLinearMap.id_apply] using
    realHessian_comp_affine (ContinuousLinearMap.id ℝ E) c hu v w

theorem actual_centered_residual_hessian_four {u q : E → ℝ} (c : E)
    {r b : ℝ} (hr : 0 < r) {z : E} (hu : ContDiffAt ℝ 2 u (c+r • z))
    (hq : ContDiffAt ℝ 2 q (c+r • z)) :
    realHessian (actualCenteredResidualFour c r b u q) z=
      b⁻¹ • (realHessian u (c+r • z)-realHessian q (c+r • z)) := by
  have ht : ContDiffAt ℝ 2 (fun x : E => c+x) (r • z) := by fun_prop
  have huT : ContDiffAt ℝ 2 (fun x => u (c+x)) (r • z) := hu.comp _ ht
  have hqT : ContDiffAt ℝ 2 (fun x => q (c+x)) (r • z) := hq.comp _ ht
  have hh := actual_normalized_residual_hessian_four (b := b) hr huT hqT
  rw [actual_realHessian_translate_four c _ hu,actual_realHessian_translate_four c _ hq] at hh
  exact hh

theorem actual_centered_residual_fderiv_four {u q : E → ℝ} (c : E)
    {r b : ℝ} (hr : 0 < r) {z : E} (hu : DifferentiableAt ℝ u (c+r • z))
    (hq : DifferentiableAt ℝ q (c+r • z)) :
    fderiv ℝ (actualCenteredResidualFour c r b u q) z=
      (b⁻¹*r⁻¹) • (fderiv ℝ u (c+r • z)-fderiv ℝ q (c+r • z)) := by
  have hT : HasFDerivAt (fun x : E => c+r • x) (r • ContinuousLinearMap.id ℝ E) z :=
    ((hasFDerivAt_id z).const_smul r).const_add c
  have hd := ((hu.hasFDerivAt.sub hq.hasFDerivAt).comp z hT).const_smul (b⁻¹*(r^2)⁻¹)
  change HasFDerivAt (actualCenteredResidualFour c r b u q)
    ((b⁻¹*(r^2)⁻¹) • ((fderiv ℝ u (c+r • z)-fderiv ℝ q (c+r • z)).comp
      (r • ContinuousLinearMap.id ℝ E))) z at hd
  rw [hd.fderiv]
  ext v
  simp only [_root_.smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    map_smul,smul_eq_mul]
  field_simp
  <;> ring

theorem actual_centered_residual_equation_four {U : Set E} (hU : IsOpen U)
    {A : E → Mat} {f u q : E → ℝ} (c : E) {r b : ℝ} (hr : 0 < r)
    (hu : ContDiffOn ℝ 2 u U) (hq : IsQuadraticPolynomial q)
    (heq : ∀ x ∈ U, (∑ i, ∑ j, A x i j*euclideanHessian u x i j) = -f x) :
    ∀ z, c+r • z ∈ U →
      (∑ i, ∑ j, A (c+r • z) i j*euclideanHessian (actualCenteredResidualFour c r b u q) z i j) =
        -(b⁻¹*(f (c+r • z)-quadraticScalarSourceTwo A q (c+r • z))) := by
  intro z hz
  have hH := actual_centered_residual_hessian_four (b := b) c hr
    (hu.contDiffAt (hU.mem_nhds hz)) (IsQuadraticPolynomial_contDiff hq 2).contDiffAt
  have he (i j : Fin (2+2)) : A (c+r • z) i j*
      euclideanHessian (actualCenteredResidualFour c r b u q) z i j =
      b⁻¹*(A (c+r • z) i j*euclideanHessian u (c+r • z) i j-
        A (c+r • z) i j*euclideanHessian q (c+r • z) i j) := by
    simp only [euclideanHessian,hH,_root_.smul_apply,_root_.sub_apply,smul_eq_mul]
    ring
  simp_rw [he]
  simp only [← Finset.mul_sum,Finset.sum_sub_distrib]
  rw [heq _ hz]
  simp only [quadraticScalarSourceTwo]
  ring

theorem actual_quadratic_residual_source_holder_four {U : Set E} {A : E → Mat} {f q : E → ℝ}
    (hq : IsQuadraticPolynomial q) {Ka Kf M alpha : ℝ} (hM : 0 ≤ M)
    (hH : ‖realHessian q 0‖ ≤ M)
    (hA : ∀ x ∈ U, ∀ y ∈ U,
      ‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (A y)‖ ≤ Ka*‖x-y‖^alpha)
    (hf : ∀ x ∈ U, ∀ y ∈ U, |f x-f y| ≤ Kf*‖x-y‖^alpha) :
    ∀ x ∈ U, ∀ y ∈ U,
      |(f x-quadraticScalarSourceTwo A q x)-(f y-quadraticScalarSourceTwo A q y)| ≤
      (Kf+16*Ka*M)*‖x-y‖^alpha := by
  intro x hx y hy
  have hqf := actual_quadratic_source_holder_four hq hM hH hA x hx y hy
  rw [show (f x-quadraticScalarSourceTwo A q x)-(f y-quadraticScalarSourceTwo A q y)=
      (f x-f y)-(quadraticScalarSourceTwo A q x-quadraticScalarSourceTwo A q y) by ring]
  exact (abs_sub _ _).trans ((add_le_add (hf x hx y hy) hqf).trans_eq (by ring))

theorem actual_quadratic_residual_source_growth_four {U : Set E} {A : E → Mat} {f q : E → ℝ}
    (hq : IsQuadraticPolynomial q) {Ka Kf M alpha : ℝ} (hM : 0 ≤ M)
    (hH : ‖realHessian q 0‖ ≤ M)
    (hA : ∀ x ∈ U, ∀ y ∈ U,
      ‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (A y)‖ ≤ Ka*‖x-y‖^alpha)
    (hf : ∀ x ∈ U, ∀ y ∈ U, |f x-f y| ≤ Kf*‖x-y‖^alpha)
    {c : E} (hc : c ∈ U)
    (heq : (∑ i, ∑ j, A c i j*euclideanHessian q c i j) = -f c) :
    ∀ x ∈ U, |f x-quadraticScalarSourceTwo A q x| ≤ (Kf+16*Ka*M)*‖x-c‖^alpha := by
  have hz : f c-quadraticScalarSourceTwo A q c=0 := by
    simp only [quadraticScalarSourceTwo,heq,neg_neg,sub_self]
  intro x hx
  simpa only [hz,sub_zero] using actual_quadratic_residual_source_holder_four hq hM hH hA hf x hx c hc

end PowerConvexity
