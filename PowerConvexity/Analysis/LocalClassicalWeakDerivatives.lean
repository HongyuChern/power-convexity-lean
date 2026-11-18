import CHS.Analysis.LocalClassicalFlux

/-! # Actual integration by parts using only interior classical regularity.
The test support stays compactly inside the open domain. No extension of the
classical function across its boundary is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open DeGiorgi CHS.Analysis
variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

theorem local_continuous_mul_test_integrable
    {U : Set E} (hU : IsOpen U) {f phi : E → ℝ}
    (hf : ContinuousOn f U) (hp : Continuous phi)
    (hpc : HasCompactSupport phi) (hps : tsupport phi ⊆ U) :
    Integrable (fun x => f x*phi x) volume := by
  have hs0 : tsupport (fun x => f x*phi x) ⊆ tsupport phi := by
    simpa only [smul_eq_mul] using tsupport_smul_subset_right f phi
  have hs : tsupport (fun x => f x*phi x) ⊆ U := hs0.trans hps
  have hcont : Continuous (fun x => f x*phi x) :=
    (hf.mul hp.continuousOn).continuous_of_tsupport_subset hU hs
  exact hcont.integrable_of_hasCompactSupport hpc.mul_left

theorem hasWeakPartialDeriv_of_contDiffOn
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (i : Fin d) :
    HasWeakPartialDeriv i (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) f U := by
  intro phi hp hpc hps
  let v : E := EuclideanSpace.single i 1
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
    change f x*fderiv ℝ phi x v = 0
    rw [hz,mul_zero]

theorem hasWeakDiv_classical_of_contDiffOn
    {U : Set E} (hU : IsOpen U) {F : E → E}
    (hF : ∀ i : Fin d, ContDiffOn ℝ 1 (fun x => F x i) U) :
    HasWeakDiv (classicalDivergence F) F U := by
  intro phi hp hpc hps
  have hleft (i : Fin d) : IntegrableOn
      (fun x => F x i*fderiv ℝ phi x (EuclideanSpace.single i 1)) U volume := by
    apply Integrable.integrableOn
    exact local_continuous_mul_test_integrable hU (hF i).continuousOn
      ((hp.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hpc.fderiv_apply (𝕜 := ℝ) _) ((tsupport_fderiv_apply_subset ℝ _).trans hps)
  have hright (i : Fin d) : IntegrableOn
      (fun x => fderiv ℝ (fun y => F y i) x (EuclideanSpace.single i 1)*phi x) U volume := by
    apply Integrable.integrableOn
    exact local_continuous_mul_test_integrable hU
      (((hF i).fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn.clm_apply
        continuousOn_const) hp.continuous hpc hps
  rw [integral_finsetSum _ (fun i _ => hleft i)]
  simp only [classicalDivergence,Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hright i),← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact hasWeakPartialDeriv_of_contDiffOn hU (hF i) i phi hp hpc hps

theorem hasWeakPartialDeriv_congr_value_ae
    {U : Set E} {f g df : E → ℝ} {i : Fin d}
    (he : f =ᵐ[volume.restrict U] g) (hd : HasWeakPartialDeriv i df f U) :
    HasWeakPartialDeriv i df g U := by
  intro phi hp hpc hps
  rw [← hd phi hp hpc hps]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

end PowerConvexity
