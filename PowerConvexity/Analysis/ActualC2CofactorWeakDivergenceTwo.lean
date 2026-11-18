import PowerConvexity.Analysis.ActualC2HessianTestTransferFour
import PowerConvexity.Analysis.ActualCofactorMatrixDerivativeTwo
import PowerConvexity.Calculus.ComplexCofactorDivergenceUnconditionalTwo
import PowerConvexity.Calculus.LocalDirichletSubsolutionTwo

/-! # The genuine C2 cofactor has zero distributional column divergence

In complex dimension two the cofactor is a fixed linear function of the
actual real Hessian.  Two integrations by parts transfer this Hessian to a
smooth compactly supported test.  Its classical cofactor divergence vanishes
without any determinant or positivity premise.  The unknown potential is
assumed only C2 in the original open set; its cofactor is not assumed C1.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
local notation "CMat" => Matrix (Fin 2) (Fin 2) ℂ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualComplexHessianEuclideanFormTwo : Mat →L[ℝ] CMat :=
  ({ toFun := fun H i j => (4 : ℂ)⁻¹ *
      ((H (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) : ℂ)+
       (H (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) : ℂ)+Complex.I*
        ((H (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) : ℂ)-
         (H (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) : ℂ)))
     map_add' := by
       intro H K
       ext i j
       simp only [Matrix.add_apply,Complex.ofReal_add]
       ring
     map_smul' := by
       intro r H
       ext i j
       simp only [Matrix.smul_apply,smul_eq_mul,Complex.ofReal_mul,
         Complex.real_smul,RingHom.id_apply]
       ring } : Mat →ₗ[ℝ] CMat).toContinuousLinearMap

def actualCofactorEuclideanFormTwo : Mat →L[ℝ] Mat :=
  actualRealWeightLinearTwo.comp (actualAdjugateLinearTwo.comp actualComplexHessianEuclideanFormTwo)

theorem actualCofactorEuclideanFormTwo_bilinear (H : E →L[ℝ] E →L[ℝ] ℝ) :
    actualCofactorEuclideanFormTwo
      (fun i j => H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))=
      actualCofactorMatrixFormTwo H := rfl

theorem actualCofactorEuclideanFormTwo_eq {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) :
    actualCofactorEuclideanFormTwo (euclideanHessian u x)=complexCofactorCoeff u x := by
  change actualCofactorEuclideanFormTwo
    (fun i j => realHessian u x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))=_
  rw [actualCofactorEuclideanFormTwo_bilinear,actual_cofactor_matrix_form_eq_two hu]

theorem actual_C2_cofactor_continuousOn_two {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) :
    ContinuousOn (complexCofactorCoeff u) U := by
  intro x hx
  change ContinuousWithinAt
    (fun y => actualRealWeightLinearTwo (actualAdjugateLinearTwo
      (complexHessian realDirections imagDirections u y))) U x
  exact (actualRealWeightLinearTwo.continuous.continuousAt.comp
    (actualAdjugateLinearTwo.continuous.continuousAt.comp
      (complexHessian_continuousAt_of_C2 realDirections imagDirections
        (hu.contDiffAt (hU.mem_nhds hx))))).continuousWithinAt

theorem actual_smooth_cofactor_entry_directional_two
    {psi : E → ℝ} (hpsi : ContDiff ℝ 4 psi) (x : E) (v : E) (i j : Fin (2+2)) :
    fderiv ℝ (fun y => complexCofactorCoeff psi y i j) x v=
      actualCofactorEuclideanFormTwo
        (euclideanHessian (fun y => fderiv ℝ psi y v) x) i j := by
  have hd := actual_scaled_cofactor_entry_derivative_two isOpen_univ hpsi.contDiffOn
    (c := 1) (a := complexCofactorCoeff psi) (fun y _ => by simp)
    (mem_univ x) v i j
  simp only [inv_one,one_mul] at hd
  change fderiv ℝ (fun y => complexCofactorCoeff psi y i j) x v=
    actualCofactorEuclideanFormTwo
      (fun k l => realHessian (fun y => fderiv ℝ psi y v) x
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1)) i j
  rw [actualCofactorEuclideanFormTwo_bilinear]
  have he : realHessian (fun y => fderiv ℝ psi y v) x=fderiv ℝ (realHessian psi) x v := by
    ext a b
    exact (actual_third_jet_directional_identity_two (hpsi.of_le (by norm_num)).contDiffAt v a b).trans
      (actual_third_jet_cycle_two (hpsi.of_le (by norm_num)).contDiffAt v a b).symm
  rwa [he]

theorem actual_C2_cofactor_column_hasWeakDiv_zero_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (j : Fin (2+2)) :
    HasWeakDiv (fun _ => 0)
      (fun x => WithLp.toLp 2 (fun i => complexCofactorCoeff u x i j)) U := by
  intro psi hpsi hpc hps
  let e : Fin (2+2) → E := fun i => EuclideanSpace.single i 1
  let pd : Fin (2+2) → E → ℝ := fun i x => fderiv ℝ psi x (e i)
  let L : Fin (2+2) → Mat →L[ℝ] ℝ := fun i =>
    ((ContinuousLinearMap.proj j : (Fin (2+2) → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : Mat →L[ℝ] (Fin (2+2) → ℝ))).comp actualCofactorEuclideanFormTwo
  have hpc4 : ContDiff ℝ 4 psi := hpsi.of_le (WithTop.coe_le_coe.mpr le_top)
  have hpd (i : Fin (2+2)) : ContDiff ℝ (⊤ : ℕ∞) (pd i) :=
    (hpsi.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hpdc (i : Fin (2+2)) : HasCompactSupport (pd i) := hpc.fderiv_apply (𝕜 := ℝ) (e i)
  have hpds (i : Fin (2+2)) : tsupport (pd i) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ (e i)).trans hps
  have hCc := actual_C2_cofactor_continuousOn_two hU hu
  have hleft (i : Fin (2+2)) : IntegrableOn
      (fun x => complexCofactorCoeff u x i j*pd i x) U volume := by
    apply Integrable.integrableOn
    exact local_continuous_mul_test_integrable hU (continuousOn_pi.mp (continuousOn_pi.mp hCc i) j)
      (hpd i).continuous (hpdc i) (hpds i)
  have hright (i : Fin (2+2)) : IntegrableOn
      (fun x => u x*L i (euclideanHessian (pd i) x)) U volume := by
    obtain ⟨hc,hcp,hs⟩ := actual_linear_hessian_test_continuous_compact_four (hpd i) (hpdc i) (L i)
    exact (local_continuous_mul_test_integrable hU hu.continuousOn hc hcp (hs.trans (hpds i))).integrableOn
  have htransfer (i : Fin (2+2)) :
      (∫ x in U, complexCofactorCoeff u x i j*pd i x)=
        ∫ x in U, u x*L i (euclideanHessian (pd i) x) := by
    calc
      _ = ∫ x in U, L i (euclideanHessian u x)*pd i x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
        change complexCofactorCoeff u x i j*pd i x=
          actualCofactorEuclideanFormTwo (euclideanHessian u x) i j*pd i x
        rw [actualCofactorEuclideanFormTwo_eq (hu.contDiffAt (hU.mem_nhds hx))]
      _ = _ := actual_C2_linear_hessian_test_transfer_four hU hu (hpd i) (hpdc i) (hpds i) (L i)
  change (∫ x in U, ∑ i, complexCofactorCoeff u x i j*pd i x)= -∫ x in U, (0 : ℝ)*psi x
  simp only [zero_mul,integral_zero,neg_zero]
  rw [integral_finsetSum _ (fun i _ => hleft i)]
  simp_rw [htransfer]
  rw [← integral_finsetSum _ (fun i _ => hright i)]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  rw [← Finset.mul_sum]
  have hz : (∑ i : Fin (2+2), L i (euclideanHessian (pd i) x))=0 := by
    have he (i : Fin (2+2)) : L i (euclideanHessian (pd i) x)=
        fderiv ℝ (fun y => complexCofactorCoeff psi y i j) x (e i) :=
      (actual_smooth_cofactor_entry_directional_two hpc4 x (e i) i j).symm
    simp only [he]
    exact complexCofactorCoeff_divergence_unconditional_two (hpc4.of_le (by norm_num)).contDiffAt j
  rw [hz,mul_zero]
  rfl

end PowerConvexity
