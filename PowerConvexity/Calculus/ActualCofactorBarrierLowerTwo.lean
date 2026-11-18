import PowerConvexity.Algebra.ActualCompactHermitianMarginTwo
import PowerConvexity.Calculus.CofactorLinearizedDirichletTwo
import PowerConvexity.Calculus.LocalDirichletSubsolutionTwo

/-! # A uniform actual cofactor lower barrier from strict psh data

Only a determinant lower bound is used. The scalar margin belongs to the
fixed strict subsolution, before the unknown solution is selected.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology BigOperators ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_complex_cofactor_contraction_trace_two
    {u w : E → ℝ} {x : E}
    (hA : (complexHessian realDirections imagDirections u x).PosDef)
    (hw : ContDiffAt ℝ 2 w x) :
    (∑ i, ∑ j, complexCofactorCoeff u x i j*euclideanHessian w x i j) =
      ((complexHessian realDirections imagDirections w x)*
        (complexHessian realDirections imagDirections u x).adjugate).trace.re := by
  rw [complexCofactor_contraction_eq_density_linearized_two hA]
  unfold linearizedCMAOperatorTwo
  rw [← complexHessianContraction_pairing realDirections imagDirections _ hw,
    complex_contraction_eq_trace hw]
  let A := complexHessian realDirections imagDirections u x
  have hadj : A.adjugate = A.det • A⁻¹ := by
    rw [Matrix.inv_def,smul_smul,Ring.mul_inverse_cancel _
      ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit),one_smul]
  have him : A.det.im = 0 := (Complex.pos_iff.mp hA.det_pos).2.symm
  change A.det.re*((complexHessian realDirections imagDirections w x)*A⁻¹).trace.re = _
  rw [show (complexHessian realDirections imagDirections u x).adjugate = A.det • A⁻¹ from hadj,
    Matrix.mul_smul,Matrix.trace_smul]
  simp only [smul_eq_mul,Complex.mul_re,him,zero_mul,sub_zero]

theorem actual_compact_strictPsh_coordinate_margin_two
    {K : Set E} (hK : IsCompact K) {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ K, (complexHessian realDirections imagDirections w x).PosDef) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ x ∈ K,
      (complexHessian realDirections imagDirections w x-
        (eps : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosDef := by
  exact actual_compact_hermitian_scalar_margin_two hK
    (complexHessian realDirections imagDirections w)
    (continuous_iff_continuousAt.mpr (fun _ =>
      complexHessian_continuousAt_of_C2 realDirections imagDirections hw.contDiffAt))
    (fun _ => complexHessian_isHermitian hw.contDiffAt realDirections imagDirections) hwp

theorem actual_uniform_cofactor_barrier_contraction_lower_two
    {U : Set E} (hK : IsCompact (closure U)) {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure U, (complexHessian realDirections imagDirections w x).PosDef) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ u : E → ℝ,
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, 1 ≤ (complexHessian realDirections imagDirections u x).det.re) →
      ∀ x ∈ U,
        2*eps ≤ ∑ i, ∑ j, complexCofactorCoeff u x i j*euclideanHessian w x i j := by
  obtain ⟨eps,heps,hmargin⟩ := actual_compact_strictPsh_coordinate_margin_two hK hw hwp
  refine ⟨eps,heps,?_⟩
  intro u hup hud x hx
  rw [actual_complex_cofactor_contraction_trace_two (hup x hx) hw.contDiffAt]
  exact actual_cofactor_trace_lower_scalar_margin_two (hup x hx) (hud x hx) heps.le
    (hmargin x (subset_closure hx)).posSemidef

end PowerConvexity
