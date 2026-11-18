import PowerConvexity.Analysis.ActualScalarClassicalFluxTwo

/-! # Distributional flux equations on every actual H01 test

The smooth-test divergence identity is promoted to the actual scalar weak
formulation using the already proved density and Poincare estimates.  This
requires no classical derivative of the flux or its coefficient matrix.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_scalar_weak_of_weak_flux_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U) {p f : E → ℝ}
    (pw : MemW1pWitness 2 p U)
    (hgrad : pw.weakGrad =ᵐ[volume.restrict U] smoothGradField p)
    (hf : MemLp f 2 (volume.restrict U))
    {F : E → E}
    (hflux : ∀ x ∈ U, matMulE (A.a x) (smoothGradField p x) = F x)
    (hdiv : HasWeakDiv (fun x => -f x) F U) :
    ActualScalarWeakEquationTwo A f p := by
  obtain ⟨C,hC,hP⟩ := zeroTrace_poincare_L2_witness_bound (by norm_num : 2 ≤ 2+2) hU hUb
  refine ⟨pw.memW1p,?_⟩
  refine bilinFormOfCoeff_eq_of_isSmoothTestOn hU A (fun phi => ∫ x in U, f x*phi x)
    ?_ ?_ (‖hf.toLp f‖*C) ?_ pw ?_
  · intro u v hu hv
    simp only [mul_add]
    exact integral_add (hf.integrable_mul hu.1.1) (hf.integrable_mul hv.1.1)
  · intro c u hu
    have he : (fun x => f x*(c*u x)) = (fun x => c*(f x*u x)) := by
      funext x; ring
    rw [he,integral_const_mul]
  · intro v hv hw
    have hh := (scalar_L2_integral_mul_bound hf hw.memLp).trans
      (mul_le_mul_of_nonneg_left (hP v hv hw) (norm_nonneg (hf.toLp f)))
    simpa only [norm_gradLpOfWitness_eq,mul_assoc] using hh
  · intro phi hp
    have he : bilinFormOfCoeff A pw (smoothTestWitness hU hp) =
        ∫ x in U, ∑ i, F x i*fderiv ℝ phi x (EuclideanSpace.single i 1) := by
      unfold bilinFormOfCoeff bilinFormIntegrandOfCoeff
      apply integral_congr_ae
      filter_upwards [hgrad,ae_restrict_mem hU.measurableSet] with x hx hxU
      rw [hx,hflux x hxU]
      simp only [smoothTestWitness,smoothGradField,PiLp.inner_apply,
        PiLp.toLp_apply,Real.inner_apply]
    rw [he,hdiv phi hp.1 hp.2.1 hp.2.2]
    simp only [neg_mul,integral_neg,neg_neg]

theorem actual_scalar_weak_flux_ball_two
    {c : E} {r : ℝ} (A : EllipticCoeff (2+2) (ball c r))
    {p f : E → ℝ} (hp : ContDiff ℝ 1 p)
    (hf : MemLp f 2 (volume.restrict (ball c r)))
    {F : E → E}
    (hflux : ∀ x ∈ ball c r, matMulE (A.a x) (smoothGradField p x) = F x)
    (hdiv : HasWeakDiv (fun x => -f x) F (ball c r)) :
    ActualScalarWeakEquationTwo A f p := by
  exact actual_scalar_weak_of_weak_flux_two isOpen_ball isBounded_ball A
    (classicalBallWitness hp c r) (Filter.Eventually.of_forall (fun _ => rfl))
    hf hflux hdiv

end PowerConvexity
