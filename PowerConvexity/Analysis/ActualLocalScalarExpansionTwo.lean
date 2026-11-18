import PowerConvexity.Analysis.ActualFrozenUnitBallTwo
import PowerConvexity.Analysis.ActualScalarGeneralSourceExpansionTwo

/-! # Actual local quadratic approximation without a near-identity premise

The original coefficient is normalized at the requested physical point.
The smallness threshold is chosen after the transformed ellipticity constant
and before the physical radius.  The source is the actual `r^2` pullback.
This is an L2 approximation theorem; it is not yet a classical representative
or a boundary regularity theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_C1_scalar_ball_source_growth_two {f : E → ℝ}
    (hf : ContDiffOn ℝ 1 f (ball (0 : E) 2)) :
    MemLp f 2 (volume.restrict (ball (0 : E) 1)) ∧
      ∃ K ≥ 0, ∀ z ∈ ball (0 : E) 1, |f z-f 0| ≤ K*‖z‖ := by
  have hclosed : closedBall (0 : E) 1 ⊆ ball (0 : E) 2 :=
    closedBall_subset_ball (by norm_num)
  have hfcl := hf.mono hclosed
  refine ⟨continuousOn_memLp_two_of_subset_compact measurableSet_ball
    (isCompact_closedBall (0 : E) 1) ball_subset_closedBall hfcl.continuousOn,?_⟩
  obtain ⟨K,hK⟩ := hfcl.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : E) 1) (isCompact_closedBall (0 : E) 1)
  refine ⟨K,K.coe_nonneg,?_⟩
  intro z hz
  simpa only [Real.dist_eq,dist_zero_right] using
    hK.dist_le_mul z (ball_subset_closedBall hz) 0 (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1))

theorem actual_local_scalar_quadratic_expansion_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hpos : (A.a x₀).PosDef)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) U)
    (hdiv : ∀ x ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hfC : ContDiffOn ℝ 1 f U) (hu : ActualScalarWeakEquationTwo A f u) :
    ∃ G : E ≃L[ℝ] E,
      (actualLinearPullbackCoeffTwo G A).a (G.symm x₀) = 1 ∧
      ∃ R > 0, R ≤ 1 ∧
      closedBall (G.symm x₀) (2*R) ⊆ G ⁻¹' U ∧
      ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
      (∀ z, (realBlockHessian realDirections imagDirections p z).trace = -(R^2*f x₀)) ∧
      ∃ C ≥ 0, ∃ theta > 0, theta ≤ (1/32 : ℝ) ∧
        ∀ n : ℕ,
          (∫ z in ball (0 : E) (theta^n),
            (u (G (G.symm x₀+R • z))-p z)^2) ≤
              C*((1/2 : ℝ)^n)^2*(theta^n)^8 := by
  obtain ⟨G,L,hL,hLeq,hscale⟩ :=
    actual_normalized_physical_unit_ball_two hU hUb A hx₀ hpos hreg hdiv hf hu
  obtain ⟨M,hM,theta,htheta,hthetab,epsilon,hepsilon,hepsilon1,happrox⟩ :=
    actual_scalar_general_source_quadratic_expansion_two hL
  let eta := min epsilon (1/2 : ℝ)
  have heta : 0 < eta := lt_min hepsilon (by norm_num)
  obtain ⟨R,hR,hR1,hclosed,B,hBlam,hBL,hBa,hBzero,hBreg,hBdiv,hBdev,hBweak⟩ :=
    hscale eta heta (min_le_right _ _)
  let F : E → ℝ := fun z => R^2*f (G (G.symm x₀+R • z))
  let v : E → ℝ := fun z => u (G (G.symm x₀+R • z))
  have hT : ContDiff ℝ 1 (fun z : E => G (G.symm x₀+R • z)) :=
    by fun_prop
  have hmaps : MapsTo (fun z => G (G.symm x₀+R • z)) (ball (0 : E) 2) U := by
    intro z hz
    apply hclosed
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos hR]
    have hz2 : ‖z‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hz
    nlinarith
  have hFC : ContDiffOn ℝ 1 F (ball (0 : E) 2) :=
    contDiffOn_const.mul (hfC.comp hT.contDiffOn hmaps)
  obtain ⟨hF,K,hK,hgrowth⟩ := actual_C1_scalar_ball_source_growth_two hFC
  have hF0 : F 0 = R^2*f x₀ := by
    simp only [F,smul_zero,add_zero,G.apply_symm_apply]
  have hdev : ∀ z ∈ ball (0 : E) 1, ∀ w : E,
      ‖w-matMulE (B.a z) w‖ ≤ (epsilon*‖z‖)*‖w‖ := by
    intro z hz w
    exact (hBdev z hz w).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg z)) (norm_nonneg w))
  let vw := MemW1p.someWitness hBweak.1
  obtain ⟨S,hS,hSbound,p,hp,htrace,hp0,hp1,hp2,herror⟩ :=
    happrox B (by rw [hBlam]) (by rw [hBL]) (ball (0 : E) 2) isOpen_ball
      (closedBall_subset_ball (by norm_num)) hBreg hBdiv hdev
      F v (F 0) K ‖vw.memLp.toLp v‖ hK hF hgrowth hBweak vw le_rfl
  have hfreeze : (actualLinearPullbackCoeffTwo G A).a (G.symm x₀) = 1 := by
    simpa only [hBa,smul_zero,add_zero] using hBzero
  refine ⟨G,hfreeze,R,hR,hR1,hclosed,p,hp,?_,
    S^2*(2+50*M^2*(volume (ball (0 : E) 1)).toReal),by positivity,
    theta,htheta,hthetab,?_⟩
  · simpa only [hF0] using htrace
  · intro n
    exact (herror n).trans_eq (by ring)

end PowerConvexity
