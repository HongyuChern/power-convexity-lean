import PowerConvexity.Analysis.LocalClassicalWeakDerivatives
import CHS.Analysis.BlockCoordinates
import PowerConvexity.Calculus.ActualThirdJetNormTwo
import Mathlib.Data.Matrix.Basis

/-! # Transferring an actual C2 Hessian to a smooth compactly supported test

Only two actual interior derivatives of the unknown function are used.
Both integrations by parts take place on the original open set.  This
permits a fixed linear function of the Hessian, including the complex
two-dimensional cofactor, to be transferred to the smooth test function.
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

theorem actual_directional_gradient_derivative_entry_four
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (i j : Fin (2+2)) :
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)=
      euclideanHessian u x i j := by
  have hd := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [(hd.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single j 1) x)).fderiv]
  simp only [euclideanHessian,realHessian,_root_.add_apply,
    ContinuousLinearMap.comp_zero,_root_.zero_apply,ContinuousLinearMap.flip_apply,zero_add]

theorem actual_C2_hessian_entry_test_transfer_four
    {U : Set E} (hU : IsOpen U) {u psi : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpc : HasCompactSupport psi) (hps : tsupport psi ⊆ U)
    (i j : Fin (2+2)) :
    (∫ x in U, euclideanHessian u x i j*psi x)=
      ∫ x in U, u x*euclideanHessian psi x i j := by
  have hp2 : ContDiff ℝ 2 psi := hpsi.of_le (WithTop.coe_le_coe.mpr le_top)
  let e : Fin (2+2) → E := fun k => EuclideanSpace.single k 1
  have hdu : ContDiffOn ℝ 1 (fun x => fderiv ℝ u x (e j)) U :=
    (hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const
  have hpsiD : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ psi x (e i)) :=
    (hpsi.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have h1 := hasWeakPartialDeriv_of_contDiffOn hU hdu i psi hpsi hpc hps
  have h2 := hasWeakPartialDeriv_of_contDiffOn hU (hu.of_le (by norm_num)) j
    (fun x => fderiv ℝ psi x (e i)) hpsiD (hpc.fderiv_apply (𝕜 := ℝ) (e i))
    ((tsupport_fderiv_apply_subset ℝ (e i)).trans hps)
  have he1 : (∫ x in U,
      fderiv ℝ (fun y => fderiv ℝ u y (e j)) x (e i)*psi x)=
      ∫ x in U, euclideanHessian u x i j*psi x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [actual_directional_gradient_derivative_entry_four (hu.contDiffAt (hU.mem_nhds hx))]
  have he2 : (∫ x in U, u x*fderiv ℝ (fun y => fderiv ℝ psi y (e i)) x (e j))=
      ∫ x in U, u x*euclideanHessian psi x i j := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [actual_directional_gradient_derivative_entry_four hp2.contDiffAt]
    rw [euclideanHessian,euclideanHessian,realHessian_symm hp2.contDiffAt]
  change (∫ x in U, fderiv ℝ u x (e j)*fderiv ℝ psi x (e i))=
    -(∫ x in U, fderiv ℝ (fun y => fderiv ℝ u y (e j)) x (e i)*psi x) at h1
  change (∫ x in U, u x*fderiv ℝ (fun y => fderiv ℝ psi y (e i)) x (e j))=
    -(∫ x in U, fderiv ℝ u x (e j)*fderiv ℝ psi x (e i)) at h2
  rw [he1] at h1
  rw [he2] at h2
  linarith

theorem actual_realHessian_test_support_four {psi : E → ℝ}
    (hpc : HasCompactSupport psi) :
    HasCompactSupport (realHessian psi) ∧ tsupport (realHessian psi) ⊆ tsupport psi := by
  exact ⟨(hpc.fderiv ℝ).fderiv ℝ,(tsupport_fderiv_subset ℝ).trans (tsupport_fderiv_subset ℝ)⟩

theorem actual_matrix_linear_entry_expansion_four (L : Mat →L[ℝ] ℝ) (M : Mat) :
    L M=∑ i : Fin (2+2), ∑ j : Fin (2+2), M i j*L (Matrix.single i j 1) := by
  have hs (i j : Fin (2+2)) (r : ℝ) : Matrix.single i j r=r • (Matrix.single i j 1 : Mat) := by
    ext k l
    simp only [Matrix.single,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul]
    split_ifs <;> simp
  calc
    L M=L (∑ i : Fin (2+2), ∑ j : Fin (2+2), Matrix.single i j (M i j)) :=
      congrArg L (Matrix.matrix_eq_sum_single M)
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hs i j (M i j),map_smul,smul_eq_mul]

theorem actual_C2_linear_hessian_test_transfer_four
    {U : Set E} (hU : IsOpen U) {u psi : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpc : HasCompactSupport psi) (hps : tsupport psi ⊆ U)
    (L : Mat →L[ℝ] ℝ) :
    (∫ x in U, L (euclideanHessian u x)*psi x)=
      ∫ x in U, u x*L (euclideanHessian psi x) := by
  have hp2 : ContDiff ℝ 2 psi := hpsi.of_le (WithTop.coe_le_coe.mpr le_top)
  have hHc : ContinuousOn (realHessian u) U :=
    ((hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).fderiv_of_isOpen hU
      (m := 0) (by norm_num)).continuousOn
  have hpHc : Continuous (realHessian psi) :=
    ((hp2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  obtain ⟨hpH,hpHs⟩ := actual_realHessian_test_support_four hpc
  have hleft (i j : Fin (2+2)) : IntegrableOn
      (fun x => (euclideanHessian u x i j*L (Matrix.single i j 1))*psi x) U volume := by
    apply Integrable.integrableOn
    apply local_continuous_mul_test_integrable hU _ hpsi.continuous hpc hps
    exact ((hHc.clm_apply continuousOn_const).clm_apply continuousOn_const).mul continuousOn_const
  have hright (i j : Fin (2+2)) : IntegrableOn
      (fun x => u x*(euclideanHessian psi x i j*L (Matrix.single i j 1))) U volume := by
    let ev : (E →L[ℝ] E →L[ℝ] ℝ) → ℝ :=
      fun H => H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)*L (Matrix.single i j 1)
    have hev : ev 0=0 := by simp [ev]
    have htest : HasCompactSupport (fun x => euclideanHessian psi x i j*L (Matrix.single i j 1)) :=
      hpH.comp_left hev
    have htests : tsupport (fun x => euclideanHessian psi x i j*L (Matrix.single i j 1)) ⊆ U :=
      (tsupport_comp_subset hev (realHessian psi)).trans (hpHs.trans hps)
    apply Integrable.integrableOn
    apply local_continuous_mul_test_integrable hU hu.continuousOn _ htest htests
    exact ((hpHc.clm_apply continuous_const).clm_apply continuous_const).mul continuous_const
  have hlall : (fun x => L (euclideanHessian u x)*psi x)=
      fun x => ∑ i : Fin (2+2), ∑ j : Fin (2+2),
        (euclideanHessian u x i j*L (Matrix.single i j 1))*psi x := by
    funext x
    rw [actual_matrix_linear_entry_expansion_four L (euclideanHessian u x)]
    simp only [Finset.sum_mul]
  have hrall : (fun x => u x*L (euclideanHessian psi x))=
      fun x => ∑ i : Fin (2+2), ∑ j : Fin (2+2),
        u x*(euclideanHessian psi x i j*L (Matrix.single i j 1)) := by
    funext x
    rw [actual_matrix_linear_entry_expansion_four L (euclideanHessian psi x)]
    simp only [Finset.mul_sum]
  rw [hlall,hrall,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hleft i j)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hright i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hleft i j),integral_finsetSum _ (fun j _ => hright i j)]
  apply Finset.sum_congr rfl
  intro j _
  have hl : (fun x => (euclideanHessian u x i j*L (Matrix.single i j 1))*psi x)=
      fun x => L (Matrix.single i j 1)*(euclideanHessian u x i j*psi x) := by funext x; ring
  have hr : (fun x => u x*(euclideanHessian psi x i j*L (Matrix.single i j 1)))=
      fun x => L (Matrix.single i j 1)*(u x*euclideanHessian psi x i j) := by funext x; ring
  rw [hl,hr,integral_const_mul,integral_const_mul,
    actual_C2_hessian_entry_test_transfer_four hU hu hpsi hpc hps i j]

theorem actual_linear_hessian_test_continuous_compact_four
    {psi : E → ℝ} (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpc : HasCompactSupport psi) (L : Mat →L[ℝ] ℝ) :
    Continuous (fun x => L (euclideanHessian psi x)) ∧
      HasCompactSupport (fun x => L (euclideanHessian psi x)) ∧
      tsupport (fun x => L (euclideanHessian psi x)) ⊆ tsupport psi := by
  have hp2 : ContDiff ℝ 2 psi := hpsi.of_le (WithTop.coe_le_coe.mpr le_top)
  have hpHc : Continuous (realHessian psi) :=
    ((hp2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  obtain ⟨hpH,hpHs⟩ := actual_realHessian_test_support_four hpc
  let ev : (E →L[ℝ] E →L[ℝ] ℝ) → ℝ :=
    fun H => L (fun i j => H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
  have hev : ev 0=0 := by
    change L (0 : Mat)=0
    exact map_zero L
  refine ⟨?_,hpH.comp_left hev,(tsupport_comp_subset hev (realHessian psi)).trans hpHs⟩
  apply L.continuous.comp
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (hpHc.clm_apply continuous_const).clm_apply continuous_const

end PowerConvexity
