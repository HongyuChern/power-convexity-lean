import PowerConvexity.Analysis.ActualCofactorBoundaryBarrierTwo
import PowerConvexity.Analysis.ActualBoundaryBarrierComparisonTwo
import PowerConvexity.Analysis.ActualInteriorZeroDirichletTwo

/-! # Actual cofactor Dirichlet representatives with classical zero boundary

The actual weak solution is identified with a continuous zero extension and
has C2 regularity inside the original domain. Closure C2 jets are not yet a
conclusion of this module.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_cofactor_weak_classical_zero_boundary_representative_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure U, (complexHessian realDirections imagDirections w x).PosDef)
    (hwb : ∀ x ∈ frontier U, w x = 0)
    {v : E → ℝ} (hv : ContDiffOn ℝ 4 v U)
    (hvp : ∀ x ∈ U, (complexHessian realDirections imagDirections v x).PosDef)
    (hdet : ∀ x ∈ U, 1 ≤ (complexHessian realDirections imagDirections v x).det.re)
    {c : ℝ} (hc : 0 < c) (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff v x)
    {f : E → ℝ} (hf : ContinuousOn f (closure U)) (hfC : ContDiffOn ℝ 1 f U)
    {u : E → ℝ} (hu0 : MemH01 u U) (hu : ActualScalarWeakEquationTwo A f u) :
    ∃ H : E → ℝ, H =ᵐ[volume.restrict U] u ∧ Continuous H ∧ ContDiffOn ℝ 2 H U ∧
      MemH01 H U ∧ ActualScalarWeakEquationTwo A f H ∧ (∀ x ∈ frontier U, H x = 0) ∧
      (∀ x ∈ U, (complexHessian realDirections imagDirections v x).det.re *
        linearizedCMAOperatorTwo realDirections imagDirections v H x = -c*f x) := by
  have hfL2 := continuousOn_memLp_two_of_subset_compact hU.measurableSet hK subset_closure hf
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hv hvp hA
  have hpos : ∀ x ∈ U, (A.a x).PosDef := by
    intro x hx
    rw [hA x hx]
    exact (complexCofactorCoeff_posDef (hvp x hx)).smul (inv_pos.mpr hc)
  obtain ⟨k,hku,hkC,hkw,hkPDE⟩ := actual_scalar_weak_C2_interior_representative_two
    hU A hpos hreg hdiv hfL2 hfC hu
  have hk0 := actual_zeroTrace_congr_ae hku.symm hu0
  obtain ⟨p,g,hp,hpp,hpb,hg,hpw,hfg⟩ := actual_strictPsh_cofactor_boundary_barrier_two
    hU hK hw hwp hwb hv hvp hdet hc A hA hf
  have hfgAE : ∀ᵐ x ∂volume.restrict U, |f x| ≤ g x := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hfg x hx
  obtain ⟨H,hHk,hHae,hHC,hHC2,hH0,hHw,hHout⟩ := actual_zeroTrace_C2_zero_boundary_of_barrier_two
    hU hK hfL2 hg hkw hpw hk0 hkC (hp.of_le (by norm_num)) hpp hpb hfgAE
  refine ⟨H,hHae.trans hku,hHC,hHC2,hH0,hHw,?_,?_⟩
  · intro x hx
    apply hHout
    rw [hU.frontier_eq] at hx
    exact hx.2
  · intro x hx
    have he : H =ᶠ[𝓝 x] k := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hHk hy
    have hpde := hkPDE x hx
    have hess : euclideanHessian H x = euclideanHessian k x := by
      ext i j
      exact congrArg (fun B => B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
        (realHessian_eq_of_eventuallyEq he)
    rw [← hess,hA x hx] at hpde
    simp only [Matrix.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum] at hpde
    rw [complexCofactor_contraction_eq_density_linearized_two (hvp x hx)] at hpde
    have hh := congrArg (fun a : ℝ => c*a) hpde
    simpa only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul,mul_neg,neg_mul] using hh

theorem actual_cofactor_classical_zero_boundary_dirichlet_exists_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure U, (complexHessian realDirections imagDirections w x).PosDef)
    (hwb : ∀ x ∈ frontier U, w x = 0)
    {v : E → ℝ} (hv : ContDiffOn ℝ 4 v U)
    (hvp : ∀ x ∈ U, (complexHessian realDirections imagDirections v x).PosDef)
    (hdet : ∀ x ∈ U, 1 ≤ (complexHessian realDirections imagDirections v x).det.re)
    {c : ℝ} (hc : 0 < c) (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff v x)
    {f : E → ℝ} (hf : ContinuousOn f (closure U)) (hfC : ContDiffOn ℝ 1 f U) :
    ∃ H : E → ℝ, Continuous H ∧ ContDiffOn ℝ 2 H U ∧ MemH01 H U ∧
      ActualScalarWeakEquationTwo A f H ∧ (∀ x ∈ frontier U, H x = 0) ∧
      (∀ x ∈ U, (complexHessian realDirections imagDirections v x).det.re *
        linearizedCMAOperatorTwo realDirections imagDirections v H x = -c*f x) ∧
      ∀ k : E → ℝ, MemH01 k U → ActualScalarWeakEquationTwo A f k →
        ContinuousOn k U → EqOn H k U := by
  have hfL2 := continuousOn_memLp_two_of_subset_compact hU.measurableSet hK subset_closure hf
  have hUb := hK.isBounded.subset subset_closure
  obtain ⟨u,hu,huniq⟩ := scalar_weak_dirichlet_exists (by norm_num : 2 ≤ 2+2) hU hUb A hfL2
  obtain ⟨H,hHu,hHC,hHC2,hH0,hHw,hHb,hHPDE⟩ :=
    actual_cofactor_weak_classical_zero_boundary_representative_two hU hK hw hwp hwb hv hvp hdet hc A hA hf hfC hu.1
      (actual_scalar_weak_equation_of_dirichlet_two hU hUb A hu)
  refine ⟨H,hHC,hHC2,hH0,hHw,hHb,hHPDE,?_⟩
  intro k hk0 hkw hkC
  exact Measure.eqOn_open_of_ae_eq (hHu.trans (huniq k ⟨hk0,hkw.2⟩)) hU hHC.continuousOn hkC

end PowerConvexity
