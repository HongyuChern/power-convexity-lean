import PowerConvexity.Analysis.ActualSmoothScalarFluxTwo
import PowerConvexity.Analysis.ActualCofactorQuadraticResidualTwo
import PowerConvexity.Calculus.ActualCofactorBarrierLowerTwo
import PowerConvexity.Calculus.StrictPshDirichlet

/-! # The actual strict subsolution supplies the weak boundary barrier

The displayed source is the actual scalar divergence-form source. Its L2
membership and domination of the prescribed load are both established.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_scalar_source_neg_cofactor_barrier_two
    {U : Set E} (A : EllipticCoeff (2+2) U) {v w : E → ℝ} {c k : ℝ}
    {x : E} (hA : A.a x = c⁻¹ • complexCofactorCoeff v x) :
    quadraticScalarSourceTwo A.a (fun y => (-k)*w y) x =
      k*c⁻¹*(∑ i, ∑ j, complexCofactorCoeff v x i j*euclideanHessian w x i j) := by
  have he (i j : Fin (2+2)) :
      A.a x i j*euclideanHessian (fun y => (-k)*w y) x i j =
        (-k*c⁻¹)*(complexCofactorCoeff v x i j*euclideanHessian w x i j) := by
    rw [hA]
    simp only [Matrix.smul_apply,smul_eq_mul,euclideanHessian,realHessian_const_mul,
      ContinuousLinearMap.smul_apply]
    ring
  dsimp only [quadraticScalarSourceTwo]
  simp_rw [he,← Finset.mul_sum]
  ring

theorem actual_strictPsh_cofactor_boundary_barrier_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure U, (complexHessian realDirections imagDirections w x).PosDef)
    (hwb : ∀ x ∈ frontier U, w x = 0)
    {v : E → ℝ} (hv : ContDiffOn ℝ 4 v U)
    (hvp : ∀ x ∈ U, (complexHessian realDirections imagDirections v x).PosDef)
    (hdet : ∀ x ∈ U, 1 ≤ (complexHessian realDirections imagDirections v x).det.re)
    {c : ℝ} (hc : 0 < c) (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff v x)
    {f : E → ℝ} (hf : ContinuousOn f (closure U)) :
    ∃ p g : E → ℝ, ContDiff ℝ 2 p ∧ (∀ x ∈ U, 0 < p x) ∧
      (∀ x ∈ frontier U, p x = 0) ∧ MemLp g 2 (volume.restrict U) ∧
      ActualScalarWeakEquationTwo A g p ∧ ∀ x ∈ U, |f x| ≤ g x := by
  obtain ⟨eps,heps,hmargin⟩ := actual_uniform_cofactor_barrier_contraction_lower_two hK hw hwp
  obtain ⟨F,hF⟩ := hK.exists_bound_of_continuousOn hf
  let M : ℝ := max F 0+1
  have hM : 0 < M := by dsimp only [M]; linarith [le_max_right F 0]
  have hFM : F ≤ M := by dsimp only [M]; linarith [le_max_left F 0]
  let k : ℝ := c*M/eps
  have hk : 0 < k := div_pos (mul_pos hc hM) heps
  have hke : k*c⁻¹*eps = M := by dsimp only [k]; field_simp [hc.ne',heps.ne']
  let p : E → ℝ := fun y => (-k)*w y
  have hp : ContDiff ℝ 2 p := contDiff_const.mul hw
  have hneg : ∀ x ∈ U, w x < 0 := strictPshDirichlet_negative hU hK
    hw.continuous.continuousOn hw.contDiffOn hwb realDirections imagDirections
    (fun x hx => hwp x (subset_closure hx))
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hv hvp hA
  refine ⟨p,quadraticScalarSourceTwo A.a p,hp,?_,?_,
    actual_smooth_scalar_source_memLp_two hK A hp,
    actual_smooth_divergenceFree_scalar_weak_two hU hK A hreg hdiv hp,?_⟩
  · intro x hx
    exact mul_pos_of_neg_of_neg (by linarith : -k < 0) (hneg x hx)
  · intro x hx
    dsimp only [p]
    rw [hwb x hx,mul_zero]
  · intro x hx
    rw [show quadraticScalarSourceTwo A.a p x = _ from
      actual_scalar_source_neg_cofactor_barrier_two A (k := k) (hA x hx)]
    have hh := mul_le_mul_of_nonneg_left (hmargin v hvp hdet x hx)
      (mul_nonneg hk.le (inv_nonneg.mpr hc.le))
    have hlow : M ≤ k*c⁻¹*(∑ i, ∑ j, complexCofactorCoeff v x i j*euclideanHessian w x i j) := by
      have htw : k*c⁻¹*(2*eps) = 2*M := by
        calc
          k*c⁻¹*(2*eps) = 2*(k*c⁻¹*eps) := by ring
          _ = 2*M := by rw [hke]
      rw [htw] at hh
      linarith
    have hfx : |f x| ≤ F := by simpa only [Real.norm_eq_abs] using hF x (subset_closure hx)
    exact hfx.trans (hFM.trans hlow)

end PowerConvexity
