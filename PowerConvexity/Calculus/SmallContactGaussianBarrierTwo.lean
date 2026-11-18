import PowerConvexity.Calculus.SmallContactTraceBarrierTwo
import PowerConvexity.Calculus.GaussianBarrier

/-! # Actual normalized Gaussian bump for contact growth.
All derivatives and traces are those of the actual scalar barrier.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "J" => Fin 2 ⊕ Fin 2

def normalizedContactGaussianTwo (k r : ℝ) (c z : E) : ℝ :=
  (r^2/(2*k))*Real.exp k*annularBarrier (k/r^2) r c z

def bumpedLowerParaboloidTwo (a k r : ℝ) (c y z : E) : ℝ :=
  -translatedBallPotential (a/2) 0 y z+a*normalizedContactGaussianTwo k r c z

theorem normalizedContactGaussianTwo_contDiff (k r : ℝ) (c : E) (n : ℕ∞ω) :
    ContDiff ℝ n (normalizedContactGaussianTwo k r c) :=
  contDiff_const.mul (annularBarrier_contDiff _ _ _)

theorem bumpedLowerParaboloidTwo_contDiff (a k r : ℝ) (c y : E) (n : ℕ∞ω) :
    ContDiff ℝ n (bumpedLowerParaboloidTwo a k r c y) :=
  (translatedBallPotential_contDiff (a/2) 0 y n).neg.add
    (contDiff_const.mul (normalizedContactGaussianTwo_contDiff k r c n))

theorem bumpedLowerParaboloidTwo_realHessian
    {k r : ℝ} (hk : k ≠ 0) (hr : r ≠ 0) (a : ℝ) (c y x v w : E) :
    realHessian (bumpedLowerParaboloidTwo a k r c y) x v w =
      a*((Real.exp k*radialGaussian (k/r^2) c x)*
        ((2*k/r^2)*inner ℝ (x-c) v*inner ℝ (x-c) w-inner ℝ v w)-inner ℝ v w) := by
  have hq := (translatedBallPotential_contDiff (a/2) 0 y 2).contDiffAt (x := x)
  have hb := (normalizedContactGaussianTwo_contDiff k r c 2).contDiffAt (x := x)
  unfold bumpedLowerParaboloidTwo
  rw [realHessian_add hq.neg (contDiffAt_const.mul hb),realHessian_neg,
    realHessian_const_mul]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,translatedBallPotential_realHessian]
  unfold normalizedContactGaussianTwo
  rw [realHessian_const_mul,realHessian_annularBarrier]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,realRankOneForm,realInnerForm,
    innerSL_apply_apply,smul_eq_mul]
  change - (2*(a/2)*inner ℝ v w)+
    a*(((r^2/(2*k))*Real.exp k)*
      ((4*(k/r^2)^2*radialGaussian (k/r^2) c x)*
        (inner ℝ (x-c) v*inner ℝ (x-c) w)-
        (2*(k/r^2)*radialGaussian (k/r^2) c x)*inner ℝ v w)) = _
  field_simp
  <;> ring

theorem block_inner_square_sum_two (v : E) :
    (∑ i : J, (inner ℝ v (Sum.elim realDirections imagDirections i))^2) = ‖v‖^2 := by
  simp only [blockDirection_eq_single,EuclideanSpace.inner_single_right,
    conj_trivial,one_mul]
  calc
    _ = ∑ i : Fin (2+2), (v i)^2 :=
      Equiv.sum_comp finSumFinEquiv (fun i : Fin (2+2) => (v i)^2)
    _ = ‖v‖^2 := (EuclideanSpace.real_norm_sq_eq v).symm

theorem bumpedLowerParaboloidTwo_trace
    {k r : ℝ} (hk : k ≠ 0) (hr : r ≠ 0) (a : ℝ) (c y x : E) :
    (realBlockHessian realDirections imagDirections (bumpedLowerParaboloidTwo a k r c y) x).trace =
      a*((Real.exp k*radialGaussian (k/r^2) c x)*((2*k/r^2)*‖x-c‖^2-4)-4) := by
  have hunit (i : J) : inner ℝ (Sum.elim realDirections imagDirections i)
      (Sum.elim realDirections imagDirections i) = 1 := by
    rw [real_inner_self_eq_norm_sq,blockDirection_eq_single]
    simp
  simp only [Matrix.trace,Matrix.diag_apply,realBlockHessian,
    bumpedLowerParaboloidTwo_realHessian hk hr,hunit]
  simp_rw [show ∀ i : J,
      (2*k/r^2)*inner ℝ (x-c) (Sum.elim realDirections imagDirections i)*
        inner ℝ (x-c) (Sum.elim realDirections imagDirections i) =
          (2*k/r^2)*(inner ℝ (x-c) (Sum.elim realDirections imagDirections i))^2 by
    intro i; ring]
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_sum,Fintype.card_fin,nsmul_eq_mul,block_inner_square_sum_two]
  norm_num

end PowerConvexity
