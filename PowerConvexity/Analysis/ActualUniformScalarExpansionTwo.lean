import PowerConvexity.Analysis.ActualUniformPullbackL2Two
import PowerConvexity.Analysis.ActualUniformScalarSourceTwo

/-! # Uniform local quadratic approximation of the actual weak solution

All radii, contraction factors and error amplitudes precede the centre and its
normalizing map. The source bounds here are genuine bounds on the same open
set; they can be obtained by restricting a C1 source to an interior ball.
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
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_local_scalar_quadratic_expansion_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U)
    (hpos : ∀ x ∈ U, (A.a x).PosDef)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U)
    (hdiv : ∀ y ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun z => A.a z i j) y (EuclideanSpace.single i 1)) = 0)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hfC : ContDiffOn ℝ 1 f U)
    {K F : ℝ} (hK : 0 ≤ K) (hF : 0 ≤ F)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, |f x-f y| ≤ K*‖x-y‖)
    (hbound : ∀ x ∈ U, |f x| ≤ F)
    (hu : ActualScalarWeakEquationTwo A f u) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ delta > 0, closedBall x₀ delta ⊆ U ∧ ∃ r > 0, r ≤ 1 ∧
      ∃ C ≥ 0, ∃ theta > 0, theta ≤ (1/32 : ℝ) ∧
      ∀ x ∈ ball x₀ delta, ∃ G : E ≃L[ℝ] E,
        actualLinearCongruenceMatrixTwo G (A.a x) = 1 ∧
        closedBall (G.symm x) (2*r) ⊆ G ⁻¹' U ∧
        ‖G.toContinuousLinearMap‖ ≤ Real.sqrt A.Λ ∧
        ‖G.symm.toContinuousLinearMap‖ ≤ (Real.sqrt A.lam)⁻¹ ∧
        ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
          (∀ z, (realBlockHessian realDirections imagDirections p z).trace = -(r^2*f x)) ∧
          ∀ n : ℕ,
            (∫ z in ball (0 : E) (theta^n), (u (G (G.symm x+r • z))-p z)^2) ≤
              C*((1/2 : ℝ)^n)^2*(theta^n)^8 := by
  have hL : 0 ≤ actualUniformNormalizedUpperTwo A :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1/2) (le_max_left _ _)
  obtain ⟨M,hM,theta,htheta,hthetab,epsilon,hepsilon,hepsilon1,happrox⟩ :=
    actual_scalar_general_source_quadratic_expansion_two hL
  let eta := min epsilon (1/2 : ℝ)
  have heta : 0 < eta := lt_min hepsilon (by norm_num)
  obtain ⟨delta,hd,hdelta,r,hr,hr1,hballs⟩ :=
    actual_common_normalized_weak_unit_balls_two hU hUb A hreg hdiv hx₀ heta (min_le_right _ _)
  let uw := MemW1p.someWitness hu.1
  obtain ⟨N,hN,hNorm⟩ := actual_affine_linear_pullback_L2_uniform_two uw.memLp hr
    (Real.sqrt A.lam)⁻¹
  let D := Real.sqrt A.Λ
  let K₀ := K*D*r^3
  let F₀ := r^2*F
  let S₀ := N+(F₀/8)*Real.sqrt (volume (ball (0 : E) 1)).toReal+
    (K₀+F₀*epsilon)/epsilon+1
  let Q := 2+50*M^2*(volume (ball (0 : E) 1)).toReal
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀,D]; positivity
  have hF₀ : 0 ≤ F₀ := by dsimp [F₀]; positivity
  have hS₀ : 0 ≤ S₀ := by dsimp [S₀]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨delta,hd,hdelta,r,hr,hr1,S₀^2*Q,mul_nonneg (sq_nonneg _) hQ,
    theta,htheta,hthetab,?_⟩
  intro x hx
  have hxU := hdelta (ball_subset_closedBall hx)
  obtain ⟨G,hfreeze⟩ := actual_positive_frozen_normalization_two (hpos x hxU)
  obtain ⟨hclosed,hball⟩ := hballs x hx G hfreeze
  obtain ⟨B,hBl,hBL,hBa,hB0,hBr,hBd,hBdev,hBw⟩ := hball f u hf hu
  obtain ⟨hGn,hHn⟩ := actual_all_frozen_normalizations_uniform_two hU A
    (fun i j => (hreg i j).continuousOn) x hxU G hfreeze
  obtain ⟨hfm,hfb,hgrowth⟩ := actual_affine_scalar_source_uniform_two hfC hK hF
    (Real.sqrt_nonneg A.Λ) hLip hbound G x hr hGn hclosed
  let v : E → ℝ := fun z => u (G (G.symm x+r • z))
  let g : E → ℝ := fun z => r^2*f (G (G.symm x+r • z))
  let vw := MemW1p.someWitness hBw.1
  have hNbound : ‖vw.memLp.toLp v‖ ≤ N := hNorm G (G.symm x) hHn
    (ball_subset_closedBall.trans
      ((closedBall_subset_closedBall (by linarith : r ≤ 2*r)).trans hclosed)) vw.memLp
  have hdev : ∀ z ∈ ball (0 : E) 1, ∀ w : E,
      ‖w-matMulE (B.a z) w‖ ≤ (epsilon*‖z‖)*‖w‖ := by
    intro z hz w
    exact (hBdev z hz w).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg z)) (norm_nonneg w))
  obtain ⟨S,hS,hSbound,p,hp,htrace,hp0,hp1,hp2,herror⟩ :=
    happrox B (by rw [hBl]) hBL (ball (0 : E) 2) isOpen_ball
      (closedBall_subset_ball (by norm_num)) hBr hBd hdev
      g v (r^2*f x) K₀ N hK₀ hfm hgrowth hBw vw hNbound
  have hSS : S ≤ S₀ := by
    apply hSbound.trans
    dsimp [S₀]
    gcongr
  have hSsq : S^2 ≤ S₀^2 := (sq_le_sq₀ hS.le hS₀).mpr hSS
  refine ⟨G,hfreeze,hclosed,hGn,hHn,p,hp,htrace,?_⟩
  intro n
  exact (herror n).trans (by
    change S^2*Q*((1/2 : ℝ)^n)^2*(theta^n)^8 ≤ S₀^2*Q*((1/2 : ℝ)^n)^2*(theta^n)^8
    gcongr)

end PowerConvexity
