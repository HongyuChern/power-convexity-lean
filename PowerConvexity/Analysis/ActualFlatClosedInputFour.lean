import PowerConvexity.Analysis.ActualEllipticClosureFour
import PowerConvexity.Analysis.ActualAffineScalarBoundsFour

/-! # Unfrozen actual flat-boundary data and its boundary normalizers -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

structure ActualFlatClosedLinearInputFour (N : E) (lam Lambda alpha Ka Kf F B : ℝ) where
  coeff : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1)
  source : E → ℝ
  solution : E → ℝ
  lower : lam ≤ coeff.lam
  upper : coeff.Λ ≤ Lambda
  positive : ∀ x ∈ actualFlatUpperBallFour N 1, (coeff.a x).PosDef
  regular : ∀ i j, ContDiffOn ℝ 1 (fun x => coeff.a x i j) (actualFlatUpperBallFour N 1)
  continuous : ∀ i j, ContinuousOn (fun x => coeff.a x i j) (actualFlatClosedUpperBallFour N 1)
  divergence : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ j,
    (∑ i, fderiv ℝ (fun y => coeff.a y i j) x (EuclideanSpace.single i 1))=0
  holder : ∀ x ∈ actualFlatClosedUpperBallFour N 1, ∀ y ∈ actualFlatClosedUpperBallFour N 1,
    ‖actualMatrixOperatorTwo (coeff.a x)-actualMatrixOperatorTwo (coeff.a y)‖ ≤ Ka*‖x-y‖^alpha
  source_regular : ContDiffOn ℝ 1 source (actualFlatUpperBallFour N 1)
  source_holder : ∀ x ∈ actualFlatClosedUpperBallFour N 1, ∀ y ∈ actualFlatClosedUpperBallFour N 1,
    |source x-source y| ≤ Kf*‖x-y‖^alpha
  source_bound : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |source x| ≤ F
  solution_regular : ContDiffOn ℝ 2 solution (actualFlatUpperBallFour N 1)
  solution_continuous : ContinuousOn solution (actualFlatClosedUpperBallFour N 1)
  solution_zero : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → solution x=0
  solution_bound : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |solution x| ≤ B
  equation : ∀ x ∈ actualFlatUpperBallFour N 1,
    (∑ i, ∑ j, coeff.a x i j*euclideanHessian solution x i j) = -source x

theorem actual_flat_closed_input_normalizer_four {N c : E} (hN : ‖N‖=1)
    {lam Lambda alpha Ka Kf F B : ℝ} (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (D : ActualFlatClosedLinearInputFour N lam Lambda alpha Ka Kf F B)
    (hc : inner ℝ N c=0) (hcn : ‖c‖ ≤ (1/2 : ℝ)) :
    ∃ G : E ≃L[ℝ] E, actualLinearCongruenceMatrixTwo G (D.coeff.a c)=1 ∧
      ‖G.toContinuousLinearMap‖ ≤ max 1 (Real.sqrt Lambda) ∧
      ‖G.symm.toContinuousLinearMap‖ ≤ max 1 ((Real.sqrt lam)⁻¹) ∧
      ∃ k > 0, ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v := by
  have hcl : c ∈ closure (actualFlatUpperBallFour N 1) :=
    actual_flat_boundary_point_mem_closure_four hN hc (hcn.trans_lt (by norm_num))
  have hcont (i j : Fin (2+2)) : ContinuousOn (fun x => D.coeff.a x i j)
      (closure (actualFlatUpperBallFour N 1)) :=
    (D.continuous i j).mono (actualFlatUpperBallFour_closure_subset N 1)
  have hpos := actual_positive_elliptic_coefficient_on_closure_four
    (actualFlatUpperBallFour_isOpen N 1) D.coeff hcont D.positive c hcl
  have hb := actual_elliptic_bounds_on_closure_four (actualFlatUpperBallFour_isOpen N 1)
    D.coeff hcont c hcl
  obtain ⟨G,hG,hGn,hInv,k,hk,hn⟩ := actual_normal_preserving_frozen_bounds_four hpos hN hlam hLambda
    (fun v => (mul_le_mul_of_nonneg_right D.lower (sq_nonneg ‖v‖)).trans (hb v).1)
    (fun v => (hb v).2.trans (mul_le_mul_of_nonneg_right D.upper (sq_nonneg ‖v‖)))
  exact ⟨G,hG,hGn.trans (le_max_right _ _),hInv.trans (le_max_right _ _),k,hk,hn⟩

theorem actual_affine_normalized_uniform_ellipticity_four {U V : Set E} (c : E)
    (G : E ≃L[ℝ] E) {r lam Lambda M L : ℝ} (hr : 0 < r)
    (A : EllipticCoeff (2+2) U) (hmap : MapsTo (fun z : E => c+G (r • z)) V U)
    (hlo : lam ≤ A.lam) (hhi : A.Λ ≤ Lambda) (hM : 1 ≤ M) (hL : 1 ≤ L)
    (hG : ‖G.toContinuousLinearMap‖ ≤ M) (hInv : ‖G.symm.toContinuousLinearMap‖ ≤ L) :
    lam/M^2 ≤ (actualAffineNormalizedCoeffFour c G hr A hmap).lam ∧
      (actualAffineNormalizedCoeffFour c G hr A hmap).Λ ≤ Lambda*L^2 := by
  have hMG : max 1 ‖G.toContinuousLinearMap‖ ≤ M := max_le hM hG
  have hLI : max 1 ‖G.symm.toContinuousLinearMap‖ ≤ L := max_le hL hInv
  have hMGp : 0 < max 1 ‖G.toContinuousLinearMap‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hLIp : 0 ≤ max 1 ‖G.symm.toContinuousLinearMap‖ := le_trans zero_le_one (le_max_left _ _)
  constructor
  · rw [actualAffineNormalizedCoeffFour_lam]
    exact div_le_div₀ A.hlam.le hlo (sq_pos_of_pos hMGp)
      (pow_le_pow_left₀ hMGp.le hMG 2)
  · rw [actualAffineNormalizedCoeffFour_Lambda]
    exact mul_le_mul hhi (pow_le_pow_left₀ hLIp hLI 2) (sq_nonneg _)
      ((A.hlam.le.trans A.hΛ).trans hhi)

end PowerConvexity
