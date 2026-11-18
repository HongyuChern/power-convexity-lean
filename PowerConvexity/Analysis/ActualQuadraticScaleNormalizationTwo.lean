import PowerConvexity.Analysis.ActualScalarWeakScalingTwo
import PowerConvexity.Analysis.ActualQuadraticScalarSourceTwo

/-! # Exact quadratic-scale normalization of actual weak residuals.
The real four-dimensional volume factor, normalized L2 norm and actual
nonhomogeneous source are proved explicitly for every positive scale.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_four_ball_volume_scaling_two {c : E} {R : ℝ} (hR : 0 < R) :
    (volume (ball c R)).toReal = R^4*(volume (ball (0 : E) 1)).toReal := by
  have hh := actual_integral_comp_affine_unitBall_two (x₀ := c) hR (fun _ => (1 : ℝ))
  have he : (volume (ball (0 : E) 1)).toReal = (R^4)⁻¹*(volume (ball c R)).toReal := by
    simpa [AmbientSpace,Measure.real] using hh
  rw [he]
  field_simp

theorem actual_quadratic_scale_L2_identity_two {c : E} {R a : ℝ}
    (hR : 0 < R) (ha : 0 < a) (u : E → ℝ)
    (hw : MemLp (fun z => a⁻¹*(R^2)⁻¹*u (c+R • z)) 2 (volume.restrict (ball (0 : E) 1))) :
    ‖hw.toLp (fun z => a⁻¹*(R^2)⁻¹*u (c+R • z))‖^2 =
      (a^2*R^8)⁻¹*(∫ x in ball c R, (u x)^2) := by
  rw [actual_scalar_L2_norm_squared_two hw]
  have he : (fun z => (a⁻¹*(R^2)⁻¹*u (c+R • z))^2) =
      fun z => (a⁻¹*(R^2)⁻¹)^2*(u (c+R • z))^2 := by
    funext z;ring
  rw [he,integral_const_mul,actual_integral_comp_affine_unitBall_two hR (fun x => (u x)^2)]
  norm_num [AmbientSpace]
  field_simp

theorem actual_quadratic_scale_L2_bound_two {c : E} {R a : ℝ}
    (hR : 0 < R) (ha : 0 < a) (u : E → ℝ)
    (hw : MemLp (fun z => a⁻¹*(R^2)⁻¹*u (c+R • z)) 2 (volume.restrict (ball (0 : E) 1)))
    (he : (∫ x in ball c R, (u x)^2) ≤ a^2*R^8) :
    ‖hw.toLp (fun z => a⁻¹*(R^2)⁻¹*u (c+R • z))‖ ≤ 1 := by
  have hn := actual_quadratic_scale_L2_identity_two hR ha u hw
  have hp : 0 < a^2*R^8 := by positivity
  have hb : (a^2*R^8)⁻¹*(∫ x in ball c R, (u x)^2) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left he (inv_pos.mpr hp).le).trans_eq (inv_mul_cancel₀ hp.ne')
  nlinarith [norm_nonneg (hw.toLp (fun z => a⁻¹*(R^2)⁻¹*u (c+R • z)))]

theorem actual_normalized_quadratic_residual_equation_two
    {c : E} {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    {V : Set E} (hV : IsOpen V) (hclosed : closedBall c R ⊆ V)
    (A : EllipticCoeff (2+2) (ball c R))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) V)
    (hdiv : ∀ x ∈ ball c R, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0)
    {u f q : E → ℝ} (hf : MemLp f 2 (volume.restrict (ball c R)))
    (hu : ActualScalarWeakEquationTwo A f u) (hq : IsQuadraticPolynomial q) :
    ActualScalarWeakEquationTwo (rescaleCoeffToUnitBall hR A)
      (fun z => a⁻¹*(f (c+R • z)+∑ i, ∑ j,
        A.a (c+R • z) i j*euclideanHessian q (c+R • z) i j))
      (fun z => a⁻¹*(R^2)⁻¹*(u (c+R • z)-q (c+R • z))) := by
  have hr := actual_divergenceFree_quadratic_residual_two hV hclosed A hA hdiv hf hu hq
  have hs := actual_scalar_weak_smul_two isOpen_ball
    (actual_scalar_weak_rescale_to_unitBall_two hR A hr) (a⁻¹*(R^2)⁻¹)
  apply actual_scalar_weak_source_congr_ae_two (hu := hs)
  exact Filter.Eventually.of_forall (fun z => by field_simp)

end PowerConvexity
