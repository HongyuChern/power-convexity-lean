import PowerConvexity.Analysis.ActualC1WeakDivergenceTestsTwo

/-! # Genuine local C2 nondivergence equations are actual weak equations

Continuity and distributional zero column divergence replace coefficient C1.
The compact C1 product tests and actual local Sobolev witness are constructed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6

theorem actual_C2_gradient_flux_hasWeakDiv_two
    {V : Set E} (hV : IsOpen V) {c : E} {r : ℝ}
    (hclosed : closedBall c r ⊆ V) {a : E → Mat}
    (ha : ∀ i j, ContinuousOn (fun x => a x i j) (closedBall c r))
    (hdiv : ∀ j, HasWeakDiv (fun _ => 0)
      (fun x => WithLp.toLp 2 (fun i => a x i j)) (ball c r))
    {p : E → ℝ} (hp : ContDiffOn ℝ 2 p V) :
    HasWeakDiv (fun x => ∑ i, ∑ j, a x i j*euclideanHessian p x i j)
      (fun x => matMulE (a x) (smoothGradField p x)) (ball c r) := by
  intro phi hphi hpc hps
  let e : Fin (2+2) → E := fun i => EuclideanSpace.single i 1
  let pd : Fin (2+2) → E → ℝ := fun j x => fderiv ℝ p x (e j)
  let fd : Fin (2+2) → E → ℝ := fun i x => fderiv ℝ phi x (e i)
  have hsub : ball c r ⊆ V := ball_subset_closedBall.trans hclosed
  have hpd (j : Fin (2+2)) : ContDiffOn ℝ 1 (pd j) V :=
    (hp.fderiv_of_isOpen hV (m := 1) (by norm_num)).clm_apply contDiffOn_const
  have hfd (i : Fin (2+2)) : Continuous (fd i) :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfdc (i : Fin (2+2)) : HasCompactSupport (fd i) := hpc.fderiv_apply (𝕜 := ℝ) (e i)
  have hfds (i : Fin (2+2)) : tsupport (fd i) ⊆ ball c r :=
    (tsupport_fderiv_apply_subset ℝ (e i)).trans hps
  have hH (i j : Fin (2+2)) : ContinuousOn (fun x => euclideanHessian p x i j) V :=
    (((hp.fderiv_of_isOpen hV (m := 1) (by norm_num)).fderiv_of_isOpen hV
      (m := 0) (by norm_num)).continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hL (i j : Fin (2+2)) : IntegrableOn (fun x => a x i j*pd j x*fd i x) (ball c r) volume :=
    (local_continuous_mul_test_integrable isOpen_ball (((ha i j).mono ball_subset_closedBall).mul ((hpd j).continuousOn.mono hsub))
      (hfd i) (hfdc i) (hfds i)).integrableOn
  have hR (i j : Fin (2+2)) : IntegrableOn
      (fun x => a x i j*euclideanHessian p x i j*phi x) (ball c r) volume :=
    (local_continuous_mul_test_integrable isOpen_ball (((ha i j).mono ball_subset_closedBall).mul ((hH i j).mono hsub))
      hphi.continuous hpc hps).integrableOn
  have hcol (j : Fin (2+2)) :
      (∑ i, ∫ x in ball c r, a x i j*pd j x*fd i x)=
        -(∑ i, ∫ x in ball c r, a x i j*euclideanHessian p x i j*phi x) := by
    have htC : ContDiff ℝ 1 (fun x => phi x*pd j x) :=
      contDiff_mul_of_tsupport_subset hV
        (hphi.of_le (WithTop.coe_le_coe.mpr le_top)) (hpd j) (hps.trans hsub)
    have htest := actual_hasWeakDiv_zero_compact_C1_test_two
      (F := fun x => WithLp.toLp 2 (fun i => a x i j))
      (fun i => ha i j) (hdiv j) htC hpc.mul_right
      ((tsupport_smul_subset_left phi (pd j)).trans hps)
    have hd (x : E) (hx : x ∈ ball c r) (i : Fin (2+2)) :
        fderiv ℝ (fun y => phi y*pd j y) x (e i)=
          pd j x*fd i x+phi x*euclideanHessian p x i j := by
      rw [fderiv_fun_mul (hphi.differentiable (by simp) x)
        (((hpd j).contDiffAt (hV.mem_nhds (hsub hx))).differentiableAt (by norm_num))]
      simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
      change phi x*fderiv ℝ (fun y => fderiv ℝ p y (e j)) x (e i)+pd j x*fd i x=_
      rw [actual_directional_gradient_derivative_entry_four (hp.contDiffAt (hV.mem_nhds (hsub hx)))]
      ring
    change (∫ x in ball c r, ∑ i,
      a x i j*fderiv ℝ (fun y => phi y*pd j y) x (e i))=0 at htest
    have he : (∫ x in ball c r, ∑ i,
        a x i j*fderiv ℝ (fun y => phi y*pd j y) x (e i))=
        (∫ x in ball c r, (∑ i, a x i j*pd j x*fd i x)+
          ∑ i, a x i j*euclideanHessian p x i j*phi x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      simp only [hd x hx,mul_add,Finset.sum_add_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    rw [he,integral_add (integrable_finsetSum _ (fun i _ => hL i j))
      (integrable_finsetSum _ (fun i _ => hR i j)),
      integral_finsetSum _ (fun i _ => hL i j),
      integral_finsetSum _ (fun i _ => hR i j)] at htest
    linarith
  change (∫ x in ball c r, ∑ i, (∑ j, a x i j*pd j x)*fd i x)=
    -(∫ x in ball c r, (∑ i, ∑ j, a x i j*euclideanHessian p x i j)*phi x)
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hL i j)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hR i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hL _ j),
    integral_finsetSum _ (fun j _ => hR _ j)]
  rw [Finset.sum_comm,Finset.sum_comm (f := fun i j => ∫ x in ball c r,
    a x i j*euclideanHessian p x i j*phi x)]
  simp_rw [hcol]
  rw [Finset.sum_neg_distrib]

theorem actual_C2_distributional_scalar_equation_two
    {V : Set E} (hV : IsOpen V) {c : E} {r : ℝ}
    (hclosed : closedBall c r ⊆ V)
    (A : EllipticCoeff (2+2) (ball c r))
    (hA : ∀ i j, ContinuousOn (fun x => A.a x i j) (closedBall c r))
    (hdiv : ∀ j, HasWeakDiv (fun _ => 0)
      (fun x => WithLp.toLp 2 (fun i => A.a x i j)) (ball c r))
    {p : E → ℝ} (hp : ContDiffOn ℝ 2 p V) :
    ActualScalarWeakEquationTwo A (quadraticScalarSourceTwo A.a p) p := by
  have hH (i j : Fin (2+2)) : ContinuousOn (fun x => euclideanHessian p x i j) V :=
    (((hp.fderiv_of_isOpen hV (m := 1) (by norm_num)).fderiv_of_isOpen hV
      (m := 0) (by norm_num)).continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hf : MemLp (quadraticScalarSourceTwo A.a p) 2 (volume.restrict (ball c r)) := by
    apply continuousOn_memLp_two_of_subset_compact measurableSet_ball
      (isCompact_closedBall c r) ball_subset_closedBall
    apply ContinuousOn.neg
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact (hA i j).mul ((hH i j).mono hclosed)
  let pw := actualC2LocalBallWitnessTwo hV hclosed (hp.of_le (by norm_num))
  apply actual_scalar_weak_of_weak_flux_two isOpen_ball isBounded_ball A pw
    (Filter.Eventually.of_forall (fun _ => rfl)) hf
    (F := fun x => matMulE (A.a x) (smoothGradField p x)) (fun _ _ => rfl)
  simpa only [quadraticScalarSourceTwo,neg_neg] using
    actual_C2_gradient_flux_hasWeakDiv_two hV hclosed hA hdiv hp

end PowerConvexity
