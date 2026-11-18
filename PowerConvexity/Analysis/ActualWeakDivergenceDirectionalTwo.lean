import PowerConvexity.Analysis.ActualC2HessianTestTransferFour

/-! # Differentiating a genuine weak divergence with C1 flux

The flux and source have only one classical derivative.  The new divergence
identity follows by moving the direction derivative onto a compact smooth
test, using the original weak identity, and moving it back onto the source.
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
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6

theorem actual_local_C1_directional_test_integral_two
    {U : Set E} (hU : IsOpen U) {f phi : E → ℝ}
    (hf : ContDiffOn ℝ 1 f U) (v : E)
    (hp : ContDiff ℝ (⊤ : ℕ∞) phi) (hpc : HasCompactSupport phi)
    (hps : tsupport phi ⊆ U) :
    (∫ x in U, f x*fderiv ℝ phi x v)=
      -(∫ x in U, fderiv ℝ f x v*phi x) := by
  have hdc : ContinuousOn (fun x => fderiv ℝ f x v) U :=
    ((hf.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn).clm_apply continuousOn_const
  have hpcd : HasCompactSupport (fun x => fderiv ℝ phi x v) := hpc.fderiv_apply (𝕜 := ℝ) v
  have hpsd : tsupport (fun x => fderiv ℝ phi x v) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ v).trans hps
  have hpdc : Continuous (fun x => fderiv ℝ phi x v) :=
    (hp.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 := local_continuous_mul_test_integrable hU hdc hp.continuous hpc hps
  have h2 := local_continuous_mul_test_integrable hU hf.continuousOn hpdc hpcd hpsd
  have h3 := local_continuous_mul_test_integrable hU hf.continuousOn hp.continuous hpc hps
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
      (fun x hx => (hf.contDiffAt (hU.mem_nhds (hps hx))).differentiableAt (by norm_num))
      (fun x _ => hp.differentiable (by simp) x)
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hps h)),mul_zero]
  · intro x hx
    have hz : fderiv ℝ phi x v = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ phi y v) (fun h => hx (hpsd h))
    rw [hz,mul_zero]

theorem actual_C2_directional_derivative_commute_two
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ u y v) x w=
      fderiv ℝ (fun y => fderiv ℝ u y w) x v := by
  have hd := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he (a b : E) : fderiv ℝ (fun y => fderiv ℝ u y a) x b=realHessian u x b a := by
    rw [(hd.hasFDerivAt.clm_apply (hasFDerivAt_const a x)).fderiv]
    simp only [realHessian,_root_.add_apply,ContinuousLinearMap.comp_zero,
      _root_.zero_apply,ContinuousLinearMap.flip_apply,zero_add]
  rw [he v w,he w v,realHessian_symm hu]

theorem actual_hasWeakDiv_directional_two
    {U : Set E} (hU : IsOpen U) {F : E → E} {f : E → ℝ}
    (hF : ∀ i : Fin (2+2), ContDiffOn ℝ 1 (fun x => F x i) U)
    (hf : ContDiffOn ℝ 1 f U) (hdiv : HasWeakDiv f F U) (v : E) :
    HasWeakDiv (fun x => fderiv ℝ f x v)
      (fun x => WithLp.toLp 2 (fun i => fderiv ℝ (fun y => F y i) x v)) U := by
  intro phi hp hpc hps
  let e : Fin (2+2) → E := fun i => EuclideanSpace.single i 1
  let pd : Fin (2+2) → E → ℝ := fun i x => fderiv ℝ phi x (e i)
  let chi : E → ℝ := fun x => fderiv ℝ phi x v
  have hp2 : ContDiff ℝ 2 phi := hp.of_le (WithTop.coe_le_coe.mpr le_top)
  have hpd (i : Fin (2+2)) : ContDiff ℝ (⊤ : ℕ∞) (pd i) :=
    (hp.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hchi : ContDiff ℝ (⊤ : ℕ∞) chi :=
    (hp.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hchic : HasCompactSupport chi := hpc.fderiv_apply (𝕜 := ℝ) v
  have hchis : tsupport chi ⊆ U := (tsupport_fderiv_apply_subset ℝ v).trans hps
  have hcomm (x : E) (i : Fin (2+2)) :
      fderiv ℝ (pd i) x v=fderiv ℝ chi x (e i) :=
    actual_C2_directional_derivative_commute_two hp2.contDiffAt (e i) v
  have hleft (i : Fin (2+2)) : IntegrableOn
      (fun x => fderiv ℝ (fun y => F y i) x v*pd i x) U volume := by
    exact (local_continuous_mul_test_integrable hU
      (((hF i).fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn.clm_apply continuousOn_const)
      (hpd i).continuous (hpc.fderiv_apply (𝕜 := ℝ) (e i))
      ((tsupport_fderiv_apply_subset ℝ (e i)).trans hps)).integrableOn
  have hright (i : Fin (2+2)) : IntegrableOn
      (fun x => F x i*fderiv ℝ chi x (e i)) U volume := by
    exact (local_continuous_mul_test_integrable hU (hF i).continuousOn
      ((hchi.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hchic.fderiv_apply (𝕜 := ℝ) (e i))
      ((tsupport_fderiv_apply_subset ℝ (e i)).trans hchis)).integrableOn
  have he (i : Fin (2+2)) :
      (∫ x in U, fderiv ℝ (fun y => F y i) x v*pd i x)=
        -(∫ x in U, F x i*fderiv ℝ chi x (e i)) := by
    have h := actual_local_C1_directional_test_integral_two hU (hF i) v (hpd i)
      (hpc.fderiv_apply (𝕜 := ℝ) (e i)) ((tsupport_fderiv_apply_subset ℝ (e i)).trans hps)
    simp only [hcomm] at h
    linarith
  change (∫ x in U, ∑ i, fderiv ℝ (fun y => F y i) x v*pd i x)=
    -(∫ x in U, fderiv ℝ f x v*phi x)
  calc
    _ = ∑ i, ∫ x in U, fderiv ℝ (fun y => F y i) x v*pd i x :=
      integral_finsetSum _ (fun i _ => hleft i)
    _ = ∑ i, -(∫ x in U, F x i*fderiv ℝ chi x (e i)) := Finset.sum_congr rfl (fun i _ => he i)
    _ = -(∫ x in U, ∑ i, F x i*fderiv ℝ chi x (e i)) := by
      rw [Finset.sum_neg_distrib,integral_finsetSum _ (fun i _ => hright i)]
    _ = ∫ x in U, f x*chi x := by
      have h := hdiv chi hchi hchic hchis
      change (∫ x in U, ∑ i, F x i*fderiv ℝ chi x (e i))=-(∫ x in U, f x*chi x) at h
      rw [h,neg_neg]
    _ = _ := actual_local_C1_directional_test_integral_two hU hf v hp hpc hps

theorem actual_hasWeakDiv_zero_directional_two
    {U : Set E} (hU : IsOpen U) {F : E → E}
    (hF : ∀ i : Fin (2+2), ContDiffOn ℝ 1 (fun x => F x i) U)
    (hdiv : HasWeakDiv (fun _ => 0) F U) (v : E) :
    HasWeakDiv (fun _ => 0)
      (fun x => WithLp.toLp 2 (fun i => fderiv ℝ (fun y => F y i) x v)) U := by
  simpa only [fderiv_const_apply,_root_.zero_apply] using
    actual_hasWeakDiv_directional_two hU hF contDiffOn_const hdiv v

end PowerConvexity
