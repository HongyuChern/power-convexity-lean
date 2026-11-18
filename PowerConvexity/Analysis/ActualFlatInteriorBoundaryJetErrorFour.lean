import PowerConvexity.Analysis.ActualFlatInteriorBallGeometryFour
import PowerConvexity.Analysis.ActualBoundaryResidualScalingBoundsFour
import PowerConvexity.Analysis.ActualUniformCenteredResidualJetsFour

/-! # Actual interior derivatives approach the boundary quadratic at the distance scale -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_interior_boundary_jet_error_four {lam Lambda alpha gamma Ka Kf F B M T : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hgamma : 0 < gamma) (hga : gamma ≤ alpha) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf)
    (hM : 0 ≤ M) (hT : 0 ≤ T) :
    ∃ C ≥ 0, ∀ N : E, ‖N‖=1 →
    ∀ D : ActualFlatClosedLinearInputFour N lam Lambda alpha Ka Kf F B,
    ∀ x ∈ actualFlatUpperBallFour N (1/4 : ℝ), ∀ R > 0,
    ∀ q : E → ℝ, IsQuadraticPolynomial q → ‖realHessian q 0‖ ≤ T →
    (let c := actualFlatBoundaryFootFour N x;
      (∑ i, ∑ j, D.coeff.a c i j*euclideanHessian q c i j) = -D.source c) →
    (∀ z : E, 0 ≤ inner ℝ N z → ‖z-actualFlatBoundaryFootFour N x‖ < R/2 →
      |D.solution z-q z| ≤ M*‖z-actualFlatBoundaryFootFour N x‖^2*
        ‖z-actualFlatBoundaryFootFour N x‖^gamma) →
    6*(inner ℝ N x/4) < R/2 →
    ‖fderiv ℝ D.solution x-fderiv ℝ q x‖ ≤ ((inner ℝ N x/4)^gamma*(inner ℝ N x/4))*C ∧
      ‖realHessian D.solution x-realHessian q x‖ ≤ (inner ℝ N x/4)^gamma*C := by
  let K := Kf+16*Ka*T
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  obtain ⟨C,hC,hestimate⟩ := actual_uniform_centered_residual_jets_four hlam hLambda hKa hK
    (show 0 ≤ K*(6 : ℝ)^alpha by positivity)
    (show 0 ≤ 36*(6 : ℝ)^gamma*M by positivity) halpha
  refine ⟨C,hC,?_⟩
  intro N hN D x hx R hR q hq hqH heq herr hsmall
  let c := actualFlatBoundaryFootFour N x
  let r := inner ℝ N x/4
  obtain ⟨hr,hr1,hc,hdist,hmap,hnear⟩ := actual_flat_interior_ball_geometry_four hN hx
  have hinc : actualFlatUpperBallFour N 1 ⊆ actualFlatClosedUpperBallFour N 1 := by
    intro z hz
    exact ⟨ball_subset_closedBall hz.1,show 0 ≤ inner ℝ N z from le_of_lt hz.2⟩
  have hmapC : MapsTo (fun z : E => x+r • z) (ball (0 : E) 2) (actualFlatClosedUpperBallFour N 1) :=
    fun z hz => hinc (hmap hz)
  have hcC : c ∈ actualFlatClosedUpperBallFour N 1 := by
    refine ⟨?_,?_⟩
    · simpa only [mem_closedBall,dist_zero_right] using hc.2.trans (by norm_num : (1/2 : ℝ) ≤ 1)
    · change 0 ≤ inner ℝ N c; exact le_of_eq hc.1.symm
  have hpow : (r^gamma)⁻¹*r^alpha ≤ 1 := actual_boundary_scale_exponent_bound_four hr hr1 hga
  have hAhold := actual_affine_holder_comp_four x hr hmapC D.holder
  have hqhold := actual_quadratic_residual_source_holder_four hq hT hqH D.holder D.source_holder
  have hfhold := actual_centered_scaled_source_holder_four x hr (Real.rpow_pos_of_pos hr gamma)
    hmapC hqhold
  have hfgrowth := actual_quadratic_residual_source_growth_four hq hT hqH D.holder D.source_holder hcC heq
  apply hestimate (actualFlatUpperBallFour N 1) (actualFlatUpperBallFour_isOpen N 1)
    D.coeff D.lower D.upper D.positive D.regular D.divergence x r (r^gamma) hr
    (Real.rpow_pos_of_pos hr gamma) hmap D.source D.solution q D.source_regular
    D.solution_regular hq D.equation
  · intro z hz w hw
    have hKaR : Ka*r^alpha ≤ Ka :=
      (mul_le_mul_of_nonneg_left (Real.rpow_le_one hr.le hr1 halpha.le) hKa).trans_eq (mul_one Ka)
    exact (hAhold z hz w hw).trans (mul_le_mul_of_nonneg_right hKaR
      (Real.rpow_nonneg (norm_nonneg _) alpha))
  · intro z hz w hw
    have hfac : (r^gamma)⁻¹*K*r^alpha ≤ K := by
      calc
        _ = K*((r^gamma)⁻¹*r^alpha) := by ring
        _ ≤ K*1 := mul_le_mul_of_nonneg_left hpow hK
        _ = K := mul_one K
    exact (hfhold z hz w hw).trans (mul_le_mul_of_nonneg_right hfac
      (Real.rpow_nonneg (norm_nonneg _) alpha))
  · intro z hz
    rw [abs_mul,abs_of_pos (inv_pos.mpr (Real.rpow_pos_of_pos hr gamma))]
    exact (mul_le_mul_of_nonneg_left (hfgrowth _ (hmapC hz))
      (inv_pos.mpr (Real.rpow_pos_of_pos hr gamma)).le).trans
      (actual_boundary_scaled_source_growth_four hr hr1 halpha.le hga hK (norm_nonneg _) (hnear z hz))
  · exact actual_boundary_actual_residual_bound_four hr hgamma.le hM hsmall herr
      (fun z hz => show 0 ≤ inner ℝ N (x+r • z) from le_of_lt (hmap hz).2) hnear

end PowerConvexity
