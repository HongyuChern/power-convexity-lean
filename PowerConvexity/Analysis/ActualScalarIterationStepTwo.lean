import PowerConvexity.Analysis.ActualHalfEllipticQuadraticImprovementTwo
import PowerConvexity.Analysis.ActualQuadraticScaleNormalizationTwo

/-! # An actual L2-normalized quadratic improvement with fixed amplitude one half.
All constants and the spatial scale precede the coefficient and solution.
The next normalized residual has a constructed Sobolev witness and L2 norm
at most one. This is a single actual step, not yet an iteration theorem.
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

theorem actual_scalar_normalized_quadratic_step_two {L : ℝ} (hL : 0 ≤ L) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/32 : ℝ) ∧ ∃ delta > 0, delta ≤ 1 ∧
      ∀ A : EllipticCoeff (2+2) (ball (0 : E) 1), (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      (∀ᵐ x ∂volume.restrict (ball (0 : E) 1), ∀ z : E,
        ‖z-matMulE (A.a x) z‖ ≤ delta*‖z‖) →
      ∀ f u : E → ℝ, ∀ hf : MemLp f 2 (volume.restrict (ball (0 : E) 1)),
      ‖hf.toLp f‖ ≤ delta → ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : E) 1), ‖uw.memLp.toLp u‖ ≤ 1 →
      ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace = 0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        (∫ x in ball (0 : E) r, (u x-q x)^2) ≤ r^8/4 ∧
        ∃ ww : MemW1pWitness 2
          (fun z => 2*(r^2)⁻¹*(u (r • z)-q (r • z))) (ball (0 : E) 1),
          ‖ww.memLp.toLp (fun z => 2*(r^2)⁻¹*(u (r • z)-q (r • z)))‖ ≤ 1 := by
  let V := (volume (ball (0 : E) 1)).toReal
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_ball_pos volume (0 : E) (by norm_num : (0 : ℝ)<1)).ne' measure_ball_lt_top.ne
  let eta := 1/(2*Real.sqrt V)
  have heta : 0 < eta := by dsimp only [eta];positivity
  obtain ⟨M,hM,happ⟩ := actual_halfElliptic_L2_quadratic_improvement_two hL
  obtain ⟨r,hr,hrb,delta,hd,hd1,hstep⟩ := happ eta heta
  refine ⟨M,hM,r,hr,hrb,delta,hd,hd1,?_⟩
  intro A hlam hAL hA f u hf hfn hu uw hun
  obtain ⟨q,hq,hqt,hqH,herr⟩ := hstep A hlam hAL hA f u hf hfn hu uw hun
  have hscale : eta^2*r^4*(volume (ball (0 : E) r)).toReal = r^8/4 := by
    rw [actual_four_ball_volume_scaling_two hr]
    change (1/(2*Real.sqrt V))^2*r^4*(r^4*V) = r^8/4
    rw [div_pow,mul_pow,Real.sq_sqrt hV.le]
    field_simp
    <;> ring
  rw [hscale] at herr
  refine ⟨q,hq,hqt,hqH,herr,?_⟩
  have hr1 : r ≤ (1 : ℝ) := by linarith
  let ur := uw.restrict isOpen_ball (ball_subset_ball hr1)
  let qw := classicalBallWitness (IsQuadraticPolynomial_contDiff hq 1) (0 : E) r
  obtain ⟨dw,hD⟩ := actual_gradLp_difference_witness_two ur qw
  let wr := (dw.rescaleToUnitBall hr).smul (2*(r^2)⁻¹)
  have he : (fun z => (2*(r^2)⁻¹)*rescaleToUnitBall (x₀ := (0 : E)) (R := r)
      (fun y => u y-q y) z) =ᵐ[volume.restrict (ball (0 : E) 1)]
      (fun z => 2*(r^2)⁻¹*(u (r • z)-q (r • z))) := by
    exact Filter.Eventually.of_forall (fun z => by simp only [rescaleToUnitBall,zero_add])
  let ww := MemW1pWitness.ofAeEq he wr
  refine ⟨ww,?_⟩
  have hmem : MemLp (fun z => (1/2 : ℝ)⁻¹*(r^2)⁻¹*
      ((fun y => u y-q y) ((0 : E)+r • z))) 2 (volume.restrict (ball (0 : E) 1)) := by
    simpa only [one_div,inv_inv,zero_add] using ww.memLp
  have hn := actual_quadratic_scale_L2_bound_two hr (by norm_num : (0 : ℝ)<1/2)
    (fun y => u y-q y) hmem (by nlinarith only [herr])
  simpa only [one_div,inv_inv,zero_add] using hn

end PowerConvexity
