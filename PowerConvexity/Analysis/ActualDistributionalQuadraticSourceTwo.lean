import PowerConvexity.Analysis.ActualC2CofactorWeakDivergenceTwo
import PowerConvexity.Analysis.ActualScalarWeakFluxTwo
import PowerConvexity.Analysis.ActualWeakQuadraticSourcesTwo

/-! # Actual quadratic sources for continuous weakly divergence-free matrices

The coefficient matrix is differentiated only in the distributional sense.
A column identity is tested against a genuine directional derivative of the
quadratic times the compact test, and then promoted to every H01 test.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6

theorem actual_smooth_gradient_flux_hasWeakDiv_two
    {U : Set E} (hU : IsOpen U) {a : E → Mat}
    (ha : ∀ i j, ContinuousOn (fun x => a x i j) U)
    (hdiv : ∀ j, HasWeakDiv (fun _ => 0)
      (fun x => WithLp.toLp 2 (fun i => a x i j)) U)
    {p : E → ℝ} (hp : ContDiff ℝ (⊤ : ℕ∞) p) :
    HasWeakDiv (fun x => ∑ i, ∑ j, a x i j*euclideanHessian p x i j)
      (fun x => matMulE (a x) (smoothGradField p x)) U := by
  intro phi hphi hpc hps
  let e : Fin (2+2) → E := fun i => EuclideanSpace.single i 1
  let pd : Fin (2+2) → E → ℝ := fun j x => fderiv ℝ p x (e j)
  let fd : Fin (2+2) → E → ℝ := fun i x => fderiv ℝ phi x (e i)
  have hp2 : ContDiff ℝ 2 p := hp.of_le (WithTop.coe_le_coe.mpr le_top)
  have hpd (j : Fin (2+2)) : ContDiff ℝ (⊤ : ℕ∞) (pd j) :=
    (hp.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hfd (i : Fin (2+2)) : Continuous (fd i) :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfdc (i : Fin (2+2)) : HasCompactSupport (fd i) := hpc.fderiv_apply (𝕜 := ℝ) (e i)
  have hfds (i : Fin (2+2)) : tsupport (fd i) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ (e i)).trans hps
  have hH (i j : Fin (2+2)) : Continuous (fun x => euclideanHessian p x i j) := by
    exact (((hp2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const
  have hL (i j : Fin (2+2)) : IntegrableOn (fun x => a x i j*pd j x*fd i x) U volume :=
    (local_continuous_mul_test_integrable hU ((ha i j).mul (hpd j).continuous.continuousOn)
      (hfd i) (hfdc i) (hfds i)).integrableOn
  have hR (i j : Fin (2+2)) : IntegrableOn
      (fun x => a x i j*euclideanHessian p x i j*phi x) U volume :=
    (local_continuous_mul_test_integrable hU ((ha i j).mul (hH i j).continuousOn)
      hphi.continuous hpc hps).integrableOn
  have hcol (j : Fin (2+2)) :
      (∑ i, ∫ x in U, a x i j*pd j x*fd i x)=
        -(∑ i, ∫ x in U, a x i j*euclideanHessian p x i j*phi x) := by
    have htest := hdiv j (fun x => pd j x*phi x) ((hpd j).mul hphi) hpc.mul_left
      ((tsupport_smul_subset_right (pd j) phi).trans hps)
    have hd (x : E) (i : Fin (2+2)) :
        fderiv ℝ (fun y => pd j y*phi y) x (e i)=
          pd j x*fd i x+phi x*euclideanHessian p x i j := by
      rw [fderiv_fun_mul ((hpd j).differentiable (by simp) x)
        (hphi.differentiable (by simp) x)]
      simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
      change pd j x*fd i x+phi x*fderiv ℝ (fun y => fderiv ℝ p y (e j)) x (e i)=_
      rw [actual_directional_gradient_derivative_entry_four hp2.contDiffAt]
    change (∫ x in U, ∑ i, a x i j*fderiv ℝ (fun y => pd j y*phi y) x (e i))=
      -∫ x in U, (0 : ℝ)*(pd j x*phi x) at htest
    have he : (fun x => ∑ i, a x i j*fderiv ℝ (fun y => pd j y*phi y) x (e i))=
        (fun x => (∑ i, a x i j*pd j x*fd i x)+
          ∑ i, a x i j*euclideanHessian p x i j*phi x) := by
      funext x
      simp only [hd,mul_add,Finset.sum_add_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    rw [he,integral_add (integrable_finsetSum _ (fun i _ => hL i j))
      (integrable_finsetSum _ (fun i _ => hR i j)),
      integral_finsetSum _ (fun i _ => hL i j),
      integral_finsetSum _ (fun i _ => hR i j)] at htest
    simp only [zero_mul,integral_zero,neg_zero] at htest
    linarith
  change (∫ x in U, ∑ i, (∑ j, a x i j*pd j x)*fd i x)=
    -(∫ x in U, (∑ i, ∑ j, a x i j*euclideanHessian p x i j)*phi x)
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hL i j)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hR i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hL _ j),
    integral_finsetSum _ (fun j _ => hR _ j)]
  rw [Finset.sum_comm,Finset.sum_comm (f := fun i j => ∫ x in U,
    a x i j*euclideanHessian p x i j*phi x)]
  simp_rw [hcol]
  rw [Finset.sum_neg_distrib]

theorem actual_distributional_divergenceFree_quadratic_source_two
    {c : E} {r : ℝ} (A : EllipticCoeff (2+2) (ball c r))
    (hA : ∀ i j, ContinuousOn (fun x => A.a x i j) (closedBall c r))
    (hdiv : ∀ j, HasWeakDiv (fun _ => 0)
      (fun x => WithLp.toLp 2 (fun i => A.a x i j)) (ball c r))
    {q : E → ℝ} (hq : IsQuadraticPolynomial q) :
    ActualScalarWeakEquationTwo A (quadraticScalarSourceTwo A.a q) q := by
  apply actual_scalar_weak_flux_ball_two A (IsQuadraticPolynomial_contDiff hq 1)
    (actual_quadratic_source_memLp_two hA hq)
    (F := fun x => matMulE (A.a x) (smoothGradField q x)) (fun _ _ => rfl)
  simpa only [quadraticScalarSourceTwo,neg_neg] using
    actual_smooth_gradient_flux_hasWeakDiv_two isOpen_ball
      (fun i j => (hA i j).mono ball_subset_closedBall) hdiv
      (IsQuadraticPolynomial_contDiff hq (⊤ : ℕ∞))

theorem actual_weak_quadratic_sources_of_distributional_divergence_two
    {c : E} {r : ℝ} (A : EllipticCoeff (2+2) (ball c r))
    (hA : ∀ i j, ContinuousOn (fun x => A.a x i j) (closedBall c r))
    (hdiv : ∀ j, HasWeakDiv (fun _ => 0)
      (fun x => WithLp.toLp 2 (fun i => A.a x i j)) (ball c r)) :
    ActualWeakQuadraticSourcesTwo A := by
  intro q hq
  exact actual_distributional_divergenceFree_quadratic_source_two A hA hdiv hq

end PowerConvexity
