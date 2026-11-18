import PowerConvexity.Algebra.QuantitativeComplexNormalizationTwo
import PowerConvexity.Calculus.PoissonIntegralHessianBoundsFour

/-! # Actual real-map bounds for determinant-one complex normalization.
The operator and inverse bounds are for the actual real linear maps used
by the complex-Hessian affine covariance theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped ComplexOrder BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem blockComplexCoordinates_norm_le_two_four (x : E) (i : Fin 2) :
    ‖blockComplexCoordinates x i‖ ≤ 2*‖x‖ := by
  have ha := PiLp.norm_apply_le x (finSumFinEquiv (Sum.inl i))
  have hb := PiLp.norm_apply_le x (finSumFinEquiv (Sum.inr i))
  have hc := Complex.norm_le_abs_re_add_abs_im (blockComplexCoordinates x i)
  change ‖blockComplexCoordinates x i‖ ≤
    |x (finSumFinEquiv (Sum.inl i))|+|x (finSumFinEquiv (Sum.inr i))| at hc
  simp only [Real.norm_eq_abs] at ha hb
  linarith only [ha,hb,hc]

theorem complexMatrixRealMap_pointwise_bound_two {G : W} {K : ℝ}
    (hK : 0 ≤ K) (hG : ∀ i j, ‖G i j‖ ≤ K) (x : E) :
    ‖complexMatrixRealMap G x‖ ≤ 8*K*‖x‖ := by
  have hz (i : Fin 2) : ‖blockComplexCoordinates (complexMatrixRealMap G x) i‖ ≤ 4*K*‖x‖ := by
    rw [blockComplexCoordinates_complexMatrixRealMap]
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    calc
      _ ≤ ‖G i 0*blockComplexCoordinates x 0‖+‖G i 1*blockComplexCoordinates x 1‖ := norm_add_le _ _
      _ = ‖G i 0‖*‖blockComplexCoordinates x 0‖+‖G i 1‖*‖blockComplexCoordinates x 1‖ := by
        rw [norm_mul,norm_mul]
      _ ≤ K*(2*‖x‖)+K*(2*‖x‖) := add_le_add
        (mul_le_mul (hG i 0) (blockComplexCoordinates_norm_le_two_four x 0) (norm_nonneg _) hK)
        (mul_le_mul (hG i 1) (blockComplexCoordinates_norm_le_two_four x 1) (norm_nonneg _) hK)
      _ = 4*K*‖x‖ := by ring
  have hc (k : Fin (2+2)) : |complexMatrixRealMap G x k| ≤ 4*K*‖x‖ := by
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective k
    cases i with
    | inl i => exact (Complex.abs_re_le_norm (blockComplexCoordinates (complexMatrixRealMap G x) i)).trans (hz i)
    | inr i => exact (Complex.abs_im_le_norm (blockComplexCoordinates (complexMatrixRealMap G x) i)).trans (hz i)
  have hs : ‖complexMatrixRealMap G x‖^2 ≤ 4*(4*K*‖x‖)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin (2+2), (4*K*‖x‖)^2 := by
        apply Finset.sum_le_sum
        intro k _
        have hh := abs_le.mp (hc k)
        nlinarith only [mul_nonneg (sub_nonneg.mpr hh.2)
          (by linarith only [hh.1] : 0 ≤ 4*K*‖x‖+complexMatrixRealMap G x k)]
      _ = _ := by simp
  have hb : 0 ≤ 8*K*‖x‖ := by positivity
  nlinarith only [hs,hb,norm_nonneg (complexMatrixRealMap G x)]

theorem complexMatrixRealMap_operator_bound_two {G : W} {K : ℝ}
    (hK : 0 ≤ K) (hG : ∀ i j, ‖G i j‖ ≤ K) : ‖complexMatrixRealMap G‖ ≤ 8*K :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (complexMatrixRealMap_pointwise_bound_two hK hG)

theorem exists_uniform_real_complex_normalizer_two {C : W} (hC : C.PosDef)
    (hdet : C.det = 1) (hlower : (C-(1/2 : ℂ) • (1 : W)).PosSemidef) :
    ∃ G : W, G.transpose*C*G.map star = 1 ∧ Complex.normSq G.det = 1 ∧
      ‖complexMatrixRealMap G‖ ≤ 16 ∧ ‖complexMatrixRealMap G⁻¹‖ ≤ 16 ∧
      Function.LeftInverse (complexMatrixRealMap G⁻¹) (complexMatrixRealMap G) ∧
      Function.RightInverse (complexMatrixRealMap G⁻¹) (complexMatrixRealMap G) := by
  obtain ⟨G,hG,hGd,hGe,hGie⟩ := exists_uniform_complex_normalizer_two hC hdet hlower
  have hGu := isUnit_det_of_normSq_eq_one hGd
  refine ⟨G,hG,hGd,?_,?_,?_,?_⟩
  · simpa only [show (8:ℝ)*2 = 16 by norm_num] using complexMatrixRealMap_operator_bound_two (by norm_num : (0:ℝ) ≤ 2) hGe
  · simpa only [show (8:ℝ)*2 = 16 by norm_num] using complexMatrixRealMap_operator_bound_two (by norm_num : (0:ℝ) ≤ 2) hGie
  · intro x
    rw [← complexMatrixRealMap_mul,Matrix.nonsing_inv_mul _ hGu,complexMatrixRealMap_one]
  · intro x
    rw [← complexMatrixRealMap_mul,Matrix.mul_nonsing_inv _ hGu,complexMatrixRealMap_one]

end PowerConvexity
