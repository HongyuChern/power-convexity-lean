import PowerConvexity.Analysis.ActualWeakDivergenceDirectionalTwo
import PowerConvexity.Analysis.ActualC2SecantFluxTwo
import PowerConvexity.Analysis.ActualLocalClassicalWeakTwo

/-! # A genuine weak derivative of a C2 solution with C1 divergence-free coefficients

The coefficient derivative is retained in the actual source.  The argument
does not assume a third derivative of the solution being differentiated.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6

theorem actual_hasWeakDiv_sub_continuous_two
    {U : Set E} (hU : IsOpen U) {F G : E → E} {f g : E → ℝ}
    (hF : ∀ i, ContinuousOn (fun x => F x i) U)
    (hG : ∀ i, ContinuousOn (fun x => G x i) U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hdivF : HasWeakDiv f F U) (hdivG : HasWeakDiv g G U) :
    HasWeakDiv (fun x => f x-g x) (fun x => F x-G x) U := by
  intro phi hp hpc hps
  have hFi (i : Fin (2+2)) : IntegrableOn
      (fun x => F x i*fderiv ℝ phi x (EuclideanSpace.single i 1)) U volume :=
    (local_continuous_mul_test_integrable hU (hF i)
      ((hp.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hpc.fderiv_apply (𝕜 := ℝ) _) ((tsupport_fderiv_apply_subset ℝ _).trans hps)).integrableOn
  have hGi (i : Fin (2+2)) : IntegrableOn
      (fun x => G x i*fderiv ℝ phi x (EuclideanSpace.single i 1)) U volume :=
    (local_continuous_mul_test_integrable hU (hG i)
      ((hp.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hpc.fderiv_apply (𝕜 := ℝ) _) ((tsupport_fderiv_apply_subset ℝ _).trans hps)).integrableOn
  have hfi : IntegrableOn (fun x => f x*phi x) U volume :=
    (local_continuous_mul_test_integrable hU hf hp.continuous hpc hps).integrableOn
  have hgi : IntegrableOn (fun x => g x*phi x) U volume :=
    (local_continuous_mul_test_integrable hU hg hp.continuous hpc hps).integrableOn
  change (∫ x in U, ∑ i, (F x i-G x i)*fderiv ℝ phi x (EuclideanSpace.single i 1))=
    -(∫ x in U, (f x-g x)*phi x)
  simp only [sub_mul,Finset.sum_sub_distrib]
  rw [integral_sub (integrable_finsetSum _ (fun i _ => hFi i))
    (integrable_finsetSum _ (fun i _ => hGi i)),integral_sub hfi hgi,
    hdivF phi hp hpc hps,hdivG phi hp hpc hps]
  ring

theorem actual_C1_coefficient_C2_flux_directional_identity_two
    {V : Set E} (hV : IsOpen V) {p : E → ℝ} (hp : ContDiffOn ℝ 2 p V)
    {a : E → Mat} (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) V)
    {x : E} (hx : x ∈ V) (v : E) :
    WithLp.toLp 2 (fun i => fderiv ℝ
      (fun y => matMulE (a y) (smoothGradField p y) i) x v)-
      matMulE (fun i j => fderiv ℝ (fun y => a y i j) x v) (smoothGradField p x)=
      matMulE (a x) (smoothGradField (fun y => fderiv ℝ p y v) x) := by
  ext i
  let e : Fin (2+2) → E := fun j => EuclideanSpace.single j 1
  have hp2 := hp.contDiffAt (hV.mem_nhds hx)
  have hpD (j : Fin (2+2)) : DifferentiableAt ℝ (fun y => fderiv ℝ p y (e j)) x :=
    ((hp2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hprod := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (((ha i j).contDiffAt (hV.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt.mul
      (hpD j).hasFDerivAt)
  simp only [Pi.mul_apply] at hprod
  change fderiv ℝ (fun y => ∑ j, a y i j*fderiv ℝ p y (e j)) x v-
      (∑ j, fderiv ℝ (fun y => a y i j) x v*fderiv ℝ p x (e j))=
      ∑ j, a x i j*fderiv ℝ (fun y => fderiv ℝ p y v) x (e j)
  rw [hprod.fderiv]
  simp only [_root_.sum_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul,
    Finset.sum_add_distrib]
  have hc (j : Fin (2+2)) : fderiv ℝ (fun y => fderiv ℝ p y (e j)) x v=
      fderiv ℝ (fun y => fderiv ℝ p y v) x (e j) :=
    actual_C2_directional_derivative_commute_two hp2 (e j) v
  simp only [hc]
  have hm : (∑ j, fderiv ℝ p x (e j)*fderiv ℝ (fun y => a y i j) x v)=
      ∑ j, fderiv ℝ (fun y => a y i j) x v*fderiv ℝ p x (e j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hm]
  ring

theorem actual_C1_coefficient_C2_directional_hasWeakDiv_two
    {V : Set E} (hV : IsOpen V) {p f : E → ℝ}
    (hp : ContDiffOn ℝ 2 p V) (hf : ContDiffOn ℝ 1 f V)
    {c : E} {r : ℝ} (hclosed : closedBall c r ⊆ V)
    {a : E → Mat} (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) V)
    (hcol : ∀ j, HasWeakDiv (fun _ => 0)
      (fun x => WithLp.toLp 2 (fun i => a x i j)) (ball c r))
    (hflux : HasWeakDiv f (fun x => matMulE (a x) (smoothGradField p x)) (ball c r))
    (v : E) :
    HasWeakDiv
      (fun x => fderiv ℝ f x v-
        ∑ i, ∑ j, fderiv ℝ (fun y => a y i j) x v*euclideanHessian p x i j)
      (fun x => matMulE (a x) (smoothGradField (fun y => fderiv ℝ p y v) x))
      (ball c r) := by
  let F : E → E := fun x => matMulE (a x) (smoothGradField p x)
  let da : E → Mat := fun x i j => fderiv ℝ (fun y => a y i j) x v
  let DF : E → E := fun x => WithLp.toLp 2 (fun i => fderiv ℝ (fun y => F y i) x v)
  let G : E → E := fun x => matMulE (da x) (smoothGradField p x)
  let g : E → ℝ := fun x => ∑ i, ∑ j, da x i j*euclideanHessian p x i j
  have hsub : ball c r ⊆ V := ball_subset_closedBall.trans hclosed
  have hF (i : Fin (2+2)) : ContDiffOn ℝ 1 (fun x => F x i) V := by
    change ContDiffOn ℝ 1 (fun x => ∑ j, a x i j*fderiv ℝ p x (EuclideanSpace.single j 1)) V
    apply ContDiffOn.sum
    intro j _
    exact (ha i j).mul ((hp.fderiv_of_isOpen hV (m := 1) (by norm_num)).clm_apply contDiffOn_const)
  have hda (i j : Fin (2+2)) : ContinuousOn (fun x => da x i j) V :=
    ((ha i j).fderiv_of_isOpen hV (m := 0) (by norm_num)).continuousOn.clm_apply continuousOn_const
  have hdacol (j : Fin (2+2)) : HasWeakDiv (fun _ => 0)
      (fun x => WithLp.toLp 2 (fun i => da x i j)) (ball c r) := by
    exact actual_hasWeakDiv_zero_directional_two isOpen_ball (fun i => (ha i j).mono hsub) (hcol j) v
  have hdivDF := actual_hasWeakDiv_directional_two isOpen_ball
    (fun i => (hF i).mono hsub) (hf.mono hsub) hflux v
  have hdivG : HasWeakDiv g G (ball c r) :=
    actual_C2_gradient_flux_hasWeakDiv_two hV hclosed (fun i j => (hda i j).mono hclosed) hdacol hp
  have hDFc (i : Fin (2+2)) : ContinuousOn (fun x => DF x i) (ball c r) :=
    (((hF i).fderiv_of_isOpen hV (m := 0) (by norm_num)).continuousOn.clm_apply continuousOn_const).mono hsub
  have hGc (i : Fin (2+2)) : ContinuousOn (fun x => G x i) (ball c r) := by
    change ContinuousOn (fun x => ∑ j, da x i j*fderiv ℝ p x (EuclideanSpace.single j 1)) (ball c r)
    apply continuousOn_finset_sum
    intro j _
    exact ((hda i j).mul
      (((hp.fderiv_of_isOpen hV (m := 1) (by norm_num)).continuousOn).clm_apply continuousOn_const)).mono hsub
  have hfc : ContinuousOn (fun x => fderiv ℝ f x v) (ball c r) :=
    ((hf.fderiv_of_isOpen hV (m := 0) (by norm_num)).continuousOn.clm_apply continuousOn_const).mono hsub
  have hH (i j : Fin (2+2)) : ContinuousOn (fun x => euclideanHessian p x i j) V :=
    (((hp.fderiv_of_isOpen hV (m := 1) (by norm_num)).fderiv_of_isOpen hV
      (m := 0) (by norm_num)).continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hgc : ContinuousOn g (ball c r) := by
    apply continuousOn_finset_sum
    intro i _
    apply continuousOn_finset_sum
    intro j _
    exact ((hda i j).mul (hH i j)).mono hsub
  have hdifference := actual_hasWeakDiv_sub_continuous_two isOpen_ball hDFc hGc hfc hgc hdivDF hdivG
  apply actual_hasWeakDiv_congr_on_two isOpen_ball hdifference
  · intro x hx
    exact actual_C1_coefficient_C2_flux_directional_identity_two hV hp ha (hsub hx) v
  · intro x hx
    rfl

theorem actual_C1_coefficient_C2_directional_weak_two
    {V : Set E} (hV : IsOpen V) {p f : E → ℝ}
    (hp : ContDiffOn ℝ 2 p V) (hf : ContDiffOn ℝ 1 f V)
    {c : E} {r : ℝ} (hclosed : closedBall c r ⊆ V)
    (A : EllipticCoeff (2+2) (ball c r))
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) V)
    (hcol : ∀ j, HasWeakDiv (fun _ => 0)
      (fun x => WithLp.toLp 2 (fun i => A.a x i j)) (ball c r))
    (hflux : HasWeakDiv f (fun x => matMulE (A.a x) (smoothGradField p x)) (ball c r))
    (v : E) :
    ActualScalarWeakEquationTwo A
      (fun x => -(fderiv ℝ f x v)+
        ∑ i, ∑ j, fderiv ℝ (fun y => A.a y i j) x v*euclideanHessian p x i j)
      (fun x => fderiv ℝ p x v) := by
  let q : E → ℝ := fun x => fderiv ℝ p x v
  let g : E → ℝ := fun x => -(fderiv ℝ f x v)+
    ∑ i, ∑ j, fderiv ℝ (fun y => A.a y i j) x v*euclideanHessian p x i j
  have hq : ContDiffOn ℝ 1 q V :=
    (hp.fderiv_of_isOpen hV (m := 1) (by norm_num)).clm_apply contDiffOn_const
  have hgc : ContinuousOn g V := by
    apply ContinuousOn.add
    · exact ((hf.fderiv_of_isOpen hV (m := 0) (by norm_num)).continuousOn.clm_apply continuousOn_const).neg
    · apply continuousOn_finset_sum
      intro i _
      apply continuousOn_finset_sum
      intro j _
      exact (((ha i j).fderiv_of_isOpen hV (m := 0) (by norm_num)).continuousOn.clm_apply continuousOn_const).mul
        ((((hp.fderiv_of_isOpen hV (m := 1) (by norm_num)).fderiv_of_isOpen hV
          (m := 0) (by norm_num)).continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const)
  have hg := continuousOn_memLp_two_of_subset_compact measurableSet_ball
    (isCompact_closedBall c r) ball_subset_closedBall (hgc.mono hclosed)
  have hdiv := actual_C1_coefficient_C2_directional_hasWeakDiv_two hV hp hf hclosed ha hcol hflux v
  have hdivg : HasWeakDiv (fun x => -g x)
      (fun x => matMulE (A.a x) (smoothGradField q x)) (ball c r) := by
    apply actual_hasWeakDiv_congr_on_two isOpen_ball hdiv (fun _ _ => rfl)
    intro x hx
    dsimp [g]
    ring
  exact actual_scalar_weak_of_weak_flux_two isOpen_ball isBounded_ball A
    (actualLocalClassicalBallWitnessTwo hV hq hclosed)
    (Filter.Eventually.of_forall (fun _ => rfl)) hg (fun _ _ => rfl) hdivg

end PowerConvexity
