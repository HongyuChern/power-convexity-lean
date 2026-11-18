import PowerConvexity.Analysis.ActualScalarWeakLinearOperationsTwo
import PowerConvexity.Analysis.LocalClassicalWeakDerivatives

/-! # Actual signed classical flux and subtraction of actual source terms.
The smooth-test integration by parts is extended to every H01 test, using
the actual scalar L2 functional and its proved Poincare bound. The ball
corollary constructs the Sobolev witness from classical regularity.
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

theorem actual_scalar_weak_of_classical_flux_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U) {p f : E → ℝ}
    (pw : MemW1pWitness 2 p U)
    (hgrad : pw.weakGrad =ᵐ[volume.restrict U] smoothGradField p)
    (hf : MemLp f 2 (volume.restrict U))
    {F : E → E} (hF : ∀ i : Fin (2+2), ContDiffOn ℝ 1 (fun x => F x i) U)
    (hflux : ∀ x ∈ U, matMulE (A.a x) (smoothGradField p x) = F x)
    (hdiv : ∀ x ∈ U, -classicalDivergence F x = f x) :
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
    rw [he,hasWeakDiv_classical_of_contDiffOn hU hF phi hp.1 hp.2.1 hp.2.2,
      ← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [← neg_mul,hdiv x hx]

theorem actual_scalar_classical_flux_ball_two
    {c : E} {r : ℝ} (A : EllipticCoeff (2+2) (ball c r))
    {p f : E → ℝ} (hp : ContDiff ℝ 1 p)
    (hf : MemLp f 2 (volume.restrict (ball c r)))
    {F : E → E} (hF : ∀ i : Fin (2+2), ContDiffOn ℝ 1 (fun x => F x i) (ball c r))
    (hflux : ∀ x ∈ ball c r, matMulE (A.a x) (smoothGradField p x) = F x)
    (hdiv : ∀ x ∈ ball c r, -classicalDivergence F x = f x) :
    ActualScalarWeakEquationTwo A f p := by
  exact actual_scalar_weak_of_classical_flux_two isOpen_ball isBounded_ball A
    (classicalBallWitness hp c r) (Filter.Eventually.of_forall (fun _ => rfl))
    hf hF hflux hdiv

theorem actual_scalar_weak_sub_two {U : Set E} (hU : IsOpen U)
    {A : EllipticCoeff (2+2) U} {f g u v : E → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A f u) (hv : ActualScalarWeakEquationTwo A g v) :
    ActualScalarWeakEquationTwo A (fun x => f x-g x) (fun x => u x-v x) := by
  have hm := actual_scalar_weak_smul_two hU hv (-1)
  have hg' : MemLp (fun x => (-1)*g x) 2 (volume.restrict U) := hg.const_mul (-1)
  have ha := actual_scalar_weak_add_two hU hf hg' hu hm
  simpa only [neg_one_mul,sub_eq_add_neg] using ha

end PowerConvexity
