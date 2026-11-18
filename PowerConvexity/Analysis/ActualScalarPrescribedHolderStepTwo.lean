import PowerConvexity.Analysis.ActualInteriorPrescribedHolderImprovementTwo
import PowerConvexity.Analysis.ActualQuadraticJetL2BoundTwo
import PowerConvexity.Analysis.ActualQuadraticScaleNormalizationTwo

/-! # Actual normalized interior step with amplitude r^alpha

The residual has a constructed Sobolev witness and uses the same weak solution.
All value, derivative and Hessian bounds belong to the single actual polynomial.
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

theorem actual_scalar_prescribed_holder_normalized_step_two {L R alpha : ℝ}
    (hL : 0 ≤ L) (hR : 0 < R) (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/32 : ℝ) ∧ r ≤ R ∧ r^alpha ≤ (1/2 : ℝ) ∧ ∃ delta > 0, delta ≤ 1 ∧
      ∀ A : EllipticCoeff (2+2) (ball (0 : E) 1), (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      (∀ᵐ x ∂volume.restrict (ball (0 : E) 1), ∀ z : E,
        ‖z-matMulE (A.a x) z‖ ≤ delta*‖z‖) →
      ∀ f u : E → ℝ, ∀ hf : MemLp f 2 (volume.restrict (ball (0 : E) 1)),
      ‖hf.toLp f‖ ≤ delta → ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : E) 1), ‖uw.memLp.toLp u‖ ≤ 1 →
      ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace = 0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        (∫ x in ball (0 : E) r, (u x-q x)^2) ≤ (r^alpha)^2*r^8 ∧
        ∃ ww : MemW1pWitness 2
          (fun z => (r^alpha)⁻¹*(r^2)⁻¹*(u (r • z)-q (r • z))) (ball (0 : E) 1),
          ‖ww.memLp.toLp (fun z => (r^alpha)⁻¹*(r^2)⁻¹*(u (r • z)-q (r • z)))‖ ≤ 1 := by
  let V := (volume (ball (0 : E) 1)).toReal
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_ball_pos volume (0 : E) (by norm_num : (0 : ℝ)<1)).ne' measure_ball_lt_top.ne
  let eta := 1/Real.sqrt V
  have heta : 0 < eta := by dsimp only [eta];positivity
  obtain ⟨M,hM,happ⟩ := actual_halfElliptic_L2_prescribed_holder_improvement_two hL
  obtain ⟨r,hr,hrb,hrR,hralpha,delta,hd,hd1,hstep⟩ := happ alpha halpha halpha1 eta heta R hR
  have htheta : 0 < r^alpha := Real.rpow_pos_of_pos hr alpha
  refine ⟨M,hM,r,hr,hrb,hrR,hralpha,delta,hd,hd1,?_⟩
  intro A hlam hAL hA f u hf hfn hu uw hun
  obtain ⟨q,hq,hqt,hqH,herr⟩ := hstep A hlam hAL hA f u hf hfn hu uw hun
  have hscale : eta^2*(r^alpha)^2*r^4*(volume (ball (0 : E) r)).toReal = (r^alpha)^2*r^8 := by
    rw [actual_four_ball_volume_scaling_two hr]
    change (1/Real.sqrt V)^2*(r^alpha)^2*r^4*(r^4*V) = (r^alpha)^2*r^8
    rw [div_pow,Real.sq_sqrt hV.le]
    field_simp
    <;> ring
  rw [hscale] at herr
  refine ⟨q,hq,hqt,hqH,herr,?_⟩
  have hr1 : r ≤ (1 : ℝ) := by linarith
  let ur := uw.restrict isOpen_ball (ball_subset_ball hr1)
  let qw := classicalBallWitness (IsQuadraticPolynomial_contDiff hq 1) (0 : E) r
  obtain ⟨dw,hD⟩ := actual_gradLp_difference_witness_two ur qw
  let wr := (dw.rescaleToUnitBall hr).smul ((r^alpha)⁻¹*(r^2)⁻¹)
  have he : (fun z => ((r^alpha)⁻¹*(r^2)⁻¹)*rescaleToUnitBall (x₀ := (0 : E)) (R := r)
      (fun y => u y-q y) z) =ᵐ[volume.restrict (ball (0 : E) 1)]
      (fun z => (r^alpha)⁻¹*(r^2)⁻¹*(u (r • z)-q (r • z))) := by
    exact Filter.Eventually.of_forall (fun z => by simp only [rescaleToUnitBall,zero_add])
  let ww := MemW1pWitness.ofAeEq he wr
  refine ⟨ww,?_⟩
  have hmem : MemLp (fun z => (r^alpha)⁻¹*(r^2)⁻¹*
      ((fun y => u y-q y) ((0 : E)+r • z))) 2 (volume.restrict (ball (0 : E) 1)) := by
    simpa only [zero_add] using ww.memLp
  have hn := actual_quadratic_scale_L2_bound_two hr htheta
    (fun y => u y-q y) hmem herr
  simpa only [zero_add] using hn


theorem actual_scalar_prescribed_holder_fullJet_step_two {L R alpha : ℝ}
    (hL : 0 ≤ L) (hR : 0 < R) (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/32 : ℝ) ∧ r ≤ R ∧ r^alpha ≤ (1/2 : ℝ) ∧ ∃ delta > 0, delta ≤ 1 ∧
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
        (∫ x in ball (0 : E) r, (u x-q x)^2) ≤ (r^alpha)^2*r^8 ∧
        ∃ ww : MemW1pWitness 2
          (fun z => (r^alpha)⁻¹*(r^2)⁻¹*(u (r • z)-q (r • z))) (ball (0 : E) 1),
          ‖ww.memLp.toLp (fun z => (r^alpha)⁻¹*(r^2)⁻¹*(u (r • z)-q (r • z)))‖ ≤ 1 := by
  obtain ⟨M,hM,r,hr,hrb,hrR,hralpha,delta,hd,hd1,hstep⟩ :=
    actual_scalar_prescribed_holder_normalized_step_two hL hR halpha halpha1
  have htheta : 0 < r^alpha := Real.rpow_pos_of_pos hr alpha
  obtain ⟨C,hC,hjet⟩ := actual_quadratic_ball_L2_jet_bound_two hr
  refine ⟨M+2*C,by positivity,r,hr,hrb,hrR,hralpha,delta,hd,hd1,?_⟩
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
    have htheta1 : (r^alpha)^2 ≤ 1 := by nlinarith
    have hmul : (r^alpha)^2*r^8 ≤ 1 := mul_le_one₀ htheta1 (pow_nonneg hr.le 8) hr8
    have herr1 := herr.trans hmul
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
