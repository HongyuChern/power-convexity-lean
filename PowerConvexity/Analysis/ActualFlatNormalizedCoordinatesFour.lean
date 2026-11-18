import PowerConvexity.Analysis.ActualNormalPreservingNormalizationFour
import PowerConvexity.Analysis.ActualFlatPhysicalNormalizationFour
import PowerConvexity.Analysis.ActualAffineCoefficientRegularityTwo

/-! # The same actual normalized coefficient on a physical half-ball -/
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

theorem actual_normal_preserving_halfspace_four {N : E} (G : E ≃L[ℝ] E)
    {k : ℝ} (hk : 0 < k) (hN : ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v) (x : E) :
    (0 < inner ℝ N (G x) ↔ 0 < inner ℝ N x) ∧
      (0 ≤ inner ℝ N (G x) ↔ 0 ≤ inner ℝ N x) ∧
      (inner ℝ N (G x)=0 ↔ inner ℝ N x=0) := by
  rw [hN]
  exact ⟨mul_pos_iff_of_pos_left hk,mul_nonneg_iff_of_pos_left hk,
    by simp only [mul_eq_zero,hk.ne',false_or]⟩

theorem actual_normal_preserving_physical_maps_four {N : E} (G : E ≃L[ℝ] E)
    {k r M : ℝ} (hk : 0 < k) (hr : 0 < r) (hM : 0 < M)
    (hN : ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v)
    (hG : ‖G.toContinuousLinearMap‖ ≤ M) (hsmall : r*M ≤ 1) :
    MapsTo (fun z : E => G (r • z)) (actualFlatUpperBallFour N 1) (actualFlatUpperBallFour N 1) ∧
    MapsTo (fun z : E => G (r • z)) (actualFlatClosedUpperBallFour N 1)
      (actualFlatClosedUpperBallFour N 1) := by
  have hnorm (z : E) : ‖G (r • z)‖ ≤ (r*M)*‖z‖ := by
    have hh := (G.toContinuousLinearMap.le_opNorm (r • z)).trans
      (mul_le_mul_of_nonneg_right hG (norm_nonneg _))
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hh
    exact hh.trans_eq (by ring)
  constructor
  · intro z hz
    refine ⟨?_,?_⟩
    · rw [mem_ball,dist_zero_right]
      have hzN : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz.1
      exact (hnorm z).trans_lt ((mul_lt_mul_of_pos_left hzN (mul_pos hr hM)).trans_le
        (by simpa only [mul_one] using hsmall))
    · change 0 < inner ℝ N (G (r • z))
      rw [hN,inner_smul_right]
      exact mul_pos hk (mul_pos hr hz.2)
  · intro z hz
    refine ⟨?_,?_⟩
    · rw [mem_closedBall,dist_zero_right]
      have hzN : ‖z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hz.1
      exact (hnorm z).trans ((mul_le_mul_of_nonneg_left hzN (mul_nonneg hr.le hM.le)).trans
        (by simpa only [mul_one] using hsmall))
    · change 0 ≤ inner ℝ N (G (r • z))
      rw [hN,inner_smul_right]
      exact mul_nonneg hk.le (mul_nonneg hr.le hz.2)

def actualFlatNormalizedCoeffFour {N : E} (G : E ≃L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    (hmap : MapsTo (fun z : E => G (r • z)) (actualFlatUpperBallFour N 1)
      (actualFlatUpperBallFour N 1)) : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1) :=
  (actualComposedLinearCoeffFour (actualScalarDilationEquivFour r hr.ne')
    (actualLinearPullbackCoeffTwo G A)).restrict hmap

@[simp] theorem actualFlatNormalizedCoeffFour_a {N : E} (G : E ≃L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    (hmap : MapsTo (fun z : E => G (r • z)) (actualFlatUpperBallFour N 1)
      (actualFlatUpperBallFour N 1)) (x : E) :
    (actualFlatNormalizedCoeffFour G hr A hmap).a x=
      actualLinearCongruenceMatrixTwo G (A.a (G (r • x))) := rfl

theorem actual_flat_normalized_coeff_frozen_four {N : E} (G : E ≃L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    (hmap : MapsTo (fun z : E => G (r • z)) (actualFlatUpperBallFour N 1)
      (actualFlatUpperBallFour N 1))
    (hfrozen : actualLinearCongruenceMatrixTwo G (A.a 0)=1) :
    (actualFlatNormalizedCoeffFour G hr A hmap).a 0=1 := by
  simpa only [actualFlatNormalizedCoeffFour_a,smul_zero,map_zero] using hfrozen

theorem actual_flat_normalized_coeff_regular_four {N : E} (G : E ≃L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    (hmap : MapsTo (fun z : E => G (r • z)) (actualFlatUpperBallFour N 1)
      (actualFlatUpperBallFour N 1)) {n : ℕ∞ω}
    (hA : ∀ i j, ContDiffOn ℝ n (fun x => A.a x i j) (actualFlatUpperBallFour N 1)) :
    ∀ i j, ContDiffOn ℝ n (fun x => (actualFlatNormalizedCoeffFour G hr A hmap).a x i j)
      (actualFlatUpperBallFour N 1) := by
  intro i j
  simp only [actualFlatNormalizedCoeffFour_a]
  exact (actual_linear_congruence_contDiffOn_two G hA i j).comp
    (contDiffOn_id.const_smul r) (fun x hx => hmap hx)

theorem actual_flat_normalized_coeff_divergence_four {N : E} (G : E ≃L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    (hmap : MapsTo (fun z : E => G (r • z)) (actualFlatUpperBallFour N 1)
      (actualFlatUpperBallFour N 1))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) (actualFlatUpperBallFour N 1))
    (hdiv : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1))=0) :
    ∀ x ∈ actualFlatUpperBallFour N 1, ∀ j,
      (∑ i, fderiv ℝ (fun y => (actualFlatNormalizedCoeffFour G hr A hmap).a y i j) x
        (EuclideanSpace.single i 1))=0 := by
  have hU := actualFlatUpperBallFour_isOpen N 1
  have hpre : IsOpen (G ⁻¹' actualFlatUpperBallFour N 1) := hU.preimage G.continuous
  have hlin := actual_linear_congruence_contDiffOn_two G hA
  have hraw (z : E) (hz : z ∈ G ⁻¹' actualFlatUpperBallFour N 1) (j : Fin (2+2)) :
      (∑ i, fderiv ℝ (fun y => actualLinearCongruenceMatrixTwo G (A.a (G y)) i j) z
        (EuclideanSpace.single i 1))=0 := by
    rw [actual_linear_congruence_column_divergence_two G
      (fun i k => ((hA i k).contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))]
    simp only [hdiv (G z) hz,mul_zero,Finset.sum_const_zero]
  intro x hx j
  have hm : r • x ∈ G ⁻¹' actualFlatUpperBallFour N 1 := hmap hx
  have hd (i : Fin (2+2)) : DifferentiableAt ℝ
      (fun y => actualLinearCongruenceMatrixTwo G (A.a (G y)) i j) (r • x) :=
    ((hlin i j).contDiffAt (hpre.mem_nhds hm)).differentiableAt (by norm_num)
  simp only [actualFlatNormalizedCoeffFour_a]
  simp_rw [actual_scalar_comp_fderiv_at_four r (hd _)]
  rw [← Finset.mul_sum,hraw _ hm j,mul_zero]

end PowerConvexity
