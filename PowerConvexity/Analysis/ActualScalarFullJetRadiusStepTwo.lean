import PowerConvexity.Analysis.ActualScalarRadiusStepTwo
import PowerConvexity.Analysis.ActualQuadraticJetL2BoundTwo

/-! # A normalized actual quadratic step with all polynomial jets controlled.
The value and first derivative are bounded using the actual L2 polynomial
norm. The original weak solution still has no assumed classical jets.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_scalar_normalized_fullJet_step_below_radius_two {L R : ℝ} (hL : 0 ≤ L) (hR : 0 < R) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/32 : ℝ) ∧ r ≤ R ∧ ∃ delta > 0, delta ≤ 1 ∧
      ∀ A : EllipticCoeff (2+2) (ball (0 : E) 1), (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      (∀ᵐ x ∂volume.restrict (ball (0 : E) 1), ∀ z : E,
        ‖z-matMulE (A.a x) z‖ ≤ delta*‖z‖) →
      ∀ f u : E → ℝ, ∀ hf : MemLp f 2 (volume.restrict (ball (0 : E) 1)),
      ‖hf.toLp f‖ ≤ delta → ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : E) 1), ‖uw.memLp.toLp u‖ ≤ 1 →
      ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace = 0) ∧
        |q 0| ≤ M ∧ ‖fderiv ℝ q 0‖ ≤ M ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        (∫ x in ball (0 : E) r, (u x-q x)^2) ≤ r^8/4 ∧
        ∃ ww : MemW1pWitness 2
          (fun z => 2*(r^2)⁻¹*(u (r • z)-q (r • z))) (ball (0 : E) 1),
          ‖ww.memLp.toLp (fun z => 2*(r^2)⁻¹*(u (r • z)-q (r • z)))‖ ≤ 1 := by
  obtain ⟨M,hM,r,hr,hrb,hrR,delta,hd,hd1,hstep⟩ := actual_scalar_normalized_quadratic_step_below_radius_two hL hR
  obtain ⟨C,hC,hjet⟩ := actual_quadratic_ball_L2_jet_bound_two hr
  refine ⟨M+2*C,by positivity,r,hr,hrb,hrR,delta,hd,hd1,?_⟩
  intro A hlam hAL hA f u hf hfn hu uw hun
  obtain ⟨q,hq,hqt,hqH,herr,ww,hwn⟩ := hstep A hlam hAL hA f u hf hfn hu uw hun
  have hr1 : r ≤ (1 : ℝ) := by linarith
  have hsub : ball (0 : E) r ⊆ ball (0 : E) 1 := ball_subset_ball hr1
  have hur : MemLp u 2 (volume.restrict (ball (0 : E) r)) :=
    uw.memLp.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hurn : ‖hur.toLp u‖ ≤ 1 :=
    (actual_scalar_L2_restrict_norm_le_two hsub uw.memLp hur).trans hun
  have hqr := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff hq 1).continuous (0 : E) r
  have hdr : MemLp (fun x => u x-q x) 2 (volume.restrict (ball (0 : E) r)) := hur.sub hqr
  have hdn : ‖hdr.toLp (fun x => u x-q x)‖ ≤ 1 := by
    have he := actual_scalar_L2_norm_squared_two (u := fun x => u x-q x) hdr
    have hr8 : r^8 ≤ 1 := pow_le_one₀ hr.le hr1
    nlinarith [norm_nonneg (hdr.toLp (fun x => u x-q x))]
  have hqn : ‖hqr.toLp q‖ ≤ 2 := by
    have hh := actual_scalar_L2_triangle_difference_two hur hqr hdr
    linarith
  obtain ⟨hq0,hq1,hq2⟩ := hjet q hq hqr
  have hcq : C*‖hqr.toLp q‖ ≤ 2*C := by
    nlinarith [mul_le_mul_of_nonneg_left hqn hC.le]
  exact ⟨q,hq,hqt,by linarith [hq0.trans hcq],by linarith [hq1.trans hcq],
    (fun x => (hqH x).trans (by linarith)),herr,ww,hwn⟩

end PowerConvexity
