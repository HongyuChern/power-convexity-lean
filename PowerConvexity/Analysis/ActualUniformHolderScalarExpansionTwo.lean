import PowerConvexity.Analysis.ActualUniformHolderFrozenBallsTwo
import PowerConvexity.Analysis.ActualUniformHolderScalarSourceTwo
import PowerConvexity.Analysis.ActualFamilyPullbackL2Two
import PowerConvexity.Analysis.ActualScalarHolderGeneralExpansionTwo

/-! # Actual quadratic approximation uniform over Holder coefficient families

Every constant is selected before the domain, coefficient, source, solution,
centre and normalizing map. No quantitative coefficient C1 bound occurs.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_holder_local_scalar_quadratic_expansion_two
    {rho lam Lambda Ka Kf F N₀ alpha : ℝ}
    (hrho : 0 < rho) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (hN₀ : 0 ≤ N₀)
    (halpha : 0 < alpha) :
    ∃ r > 0, r ≤ 1 ∧ ∃ C ≥ 0, ∃ theta > 0, theta ≤ (1/32 : ℝ) ∧
      ∀ x₀ : E, ∀ U : Set E,
      IsOpen U → Bornology.IsBounded U → closedBall x₀ rho ⊆ U →
      ∀ A : EllipticCoeff (2+2) U, lam ≤ A.lam → A.Λ ≤ Lambda →
      (∀ x ∈ U, (A.a x).PosDef) →
      (∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U) →
      (∀ y ∈ U, ∀ j,
        (∑ i, fderiv ℝ (fun z => A.a z i j) y (EuclideanSpace.single i 1)) = 0) →
      (∀ x ∈ closedBall x₀ rho, ∀ y ∈ closedBall x₀ rho,
        ‖actualMatrixOperatorTwo (A.a x)-actualMatrixOperatorTwo (A.a y)‖ ≤
          Ka*‖x-y‖^alpha) →
      ∀ f u : E → ℝ, MemLp f 2 (volume.restrict U) → ContDiffOn ℝ 1 f U →
      (∀ x ∈ U, ∀ y ∈ U, |f x-f y| ≤ Kf*‖x-y‖^alpha) →
      (∀ x ∈ U, |f x| ≤ F) → ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u U, ‖uw.memLp.toLp u‖ ≤ N₀ →
      ∀ x ∈ ball x₀ (rho/4), ∃ G : E ≃L[ℝ] E,
        actualLinearCongruenceMatrixTwo G (A.a x) = 1 ∧
        closedBall (G.symm x) (2*r) ⊆ G ⁻¹' U ∧
        ‖G.toContinuousLinearMap‖ ≤ Real.sqrt Lambda ∧
        ‖G.symm.toContinuousLinearMap‖ ≤ (Real.sqrt lam)⁻¹ ∧
        ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
          (∀ z, (realBlockHessian realDirections imagDirections p z).trace = -(r^2*f x)) ∧
          ∀ n : ℕ,
            (∫ z in ball (0 : E) (theta^n), (u (G (G.symm x+r • z))-p z)^2) ≤
              C*((1/2 : ℝ)^n)^2*(theta^n)^8 := by
  let L := max (1/2 : ℝ) (Lambda*(max 1 (Real.sqrt lam)⁻¹)^2)
  have hL : 0 ≤ L := le_trans (by norm_num : (0 : ℝ) ≤ 1/2) (le_max_left _ _)
  obtain ⟨M,hM,theta,htheta,hthetab,hthetaalpha,epsilon,hepsilon,hepsilon1,happrox⟩ :=
    actual_scalar_holder_general_source_quadratic_expansion_two hL halpha
  let eta := min epsilon (1/2 : ℝ)
  have heta : 0 < eta := lt_min hepsilon (by norm_num)
  obtain ⟨r,hr,hr1,hballs⟩ := actual_uniform_holder_frozen_weak_balls_two hrho
    hlam hLambda hKa halpha heta (min_le_right _ _)
  obtain ⟨N,hN,hNorm⟩ := actual_family_affine_linear_pullback_L2_two hr hN₀
    (Real.sqrt lam)⁻¹
  let D := Real.sqrt Lambda
  let K₀ := r^2*Kf*(D*r)^alpha
  let F₀ := r^2*F
  let S₀ := N+(F₀/8)*Real.sqrt (volume (ball (0 : E) 1)).toReal+
    (K₀+F₀*epsilon)/epsilon+1
  let Q := 2+50*M^2*(volume (ball (0 : E) 1)).toReal
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀,D]; positivity
  have hF₀ : 0 ≤ F₀ := by dsimp [F₀]; positivity
  have hS₀ : 0 ≤ S₀ := by dsimp [S₀]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨r,hr,hr1,S₀^2*Q,mul_nonneg (sq_nonneg _) hQ,theta,htheta,hthetab,?_⟩
  intro x₀ U hU hUb hclosed A hlo hhi hpos hreg hdiv hhold f u hf hfC hLip hbound hu uw hun x hx
  have hxU : x ∈ U := hclosed
    ((closedBall_subset_closedBall (by linarith : rho/4 ≤ rho)) (ball_subset_closedBall hx))
  obtain ⟨G,hfreeze⟩ := actual_positive_frozen_normalization_two (hpos x hxU)
  obtain ⟨hGn,hHn,hcb,hball⟩ := hballs x₀ U hU hUb hclosed A hlo hhi hreg hdiv hhold x hx G hfreeze
  obtain ⟨B,hBl,hBL,hBa,hB0,hBr,hBd,hBdev,hBw⟩ := hball f u hf hu
  obtain ⟨hfm,hfb,hgrowth⟩ := actual_affine_holder_scalar_source_uniform_two hfC halpha hKf hF
    (Real.sqrt_nonneg Lambda) hLip hbound G x hr hGn hcb
  let v : E → ℝ := fun z => u (G (G.symm x+r • z))
  let g : E → ℝ := fun z => r^2*f (G (G.symm x+r • z))
  let vw := MemW1p.someWitness hBw.1
  have hNbound : ‖vw.memLp.toLp v‖ ≤ N := hNorm U u uw.memLp hun G (G.symm x) hHn
    (ball_subset_closedBall.trans
      ((closedBall_subset_closedBall (by linarith : r ≤ 2*r)).trans hcb)) vw.memLp
  have hdev : ∀ z ∈ ball (0 : E) 1, ∀ w : E,
      ‖w-matMulE (B.a z) w‖ ≤ (epsilon*‖z‖^alpha)*‖w‖ := by
    intro z hz w
    exact (hBdev z hz w).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (Real.rpow_nonneg (norm_nonneg z) alpha)) (norm_nonneg w))
  obtain ⟨S,hS,hSbound,p,hp,htrace,hp0,hp1,hp2,herror⟩ :=
    happrox B (by rw [hBl]) hBL (ball (0 : E) 2) isOpen_ball
      (closedBall_subset_ball (by norm_num)) hBr hBd hdev
      g v (r^2*f x) K₀ N hK₀ hfm hgrowth hBw vw hNbound
  have hSS : S ≤ S₀ := by
    apply hSbound.trans
    dsimp [S₀]
    gcongr
  have hSsq : S^2 ≤ S₀^2 := (sq_le_sq₀ hS.le hS₀).mpr hSS
  refine ⟨G,hfreeze,hcb,hGn,hHn,p,hp,htrace,?_⟩
  intro n
  exact (herror n).trans (by
    change S^2*Q*((1/2 : ℝ)^n)^2*(theta^n)^8 ≤ S₀^2*Q*((1/2 : ℝ)^n)^2*(theta^n)^8
    gcongr)

end PowerConvexity
