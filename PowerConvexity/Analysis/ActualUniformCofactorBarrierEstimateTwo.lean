import PowerConvexity.Analysis.ActualCofactorZeroBoundaryRepresentativeTwo

/-! # Uniform linear estimates from the fixed actual strict subsolution

The scalar margin is selected before the solution, the cofactor field and
the load. The bound is homogeneous in the load, including the zero load.
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

theorem actual_uniform_cofactor_zeroTrace_barrier_estimate_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure U, (complexHessian realDirections imagDirections w x).PosDef)
    (hwb : ∀ x ∈ frontier U, w x = 0) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ c : ℝ, 0 < c → ∀ v : E → ℝ,
      ContDiffOn ℝ 4 v U →
      (∀ x ∈ U, (complexHessian realDirections imagDirections v x).PosDef) →
      (∀ x ∈ U, 1 ≤ (complexHessian realDirections imagDirections v x).det.re) →
      ∀ A : EllipticCoeff (2+2) U,
      (∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff v x) →
      ∀ f u : E → ℝ, MemLp f 2 (volume.restrict U) →
      ActualScalarWeakEquationTwo A f u → MemH01 u U → ContinuousOn u U →
      ∀ F : ℝ, 0 ≤ F → (∀ x ∈ U, |f x| ≤ F) →
      ∀ x ∈ U, |u x| ≤ (c*F/(2*eps))*(-w x) := by
  obtain ⟨eps,heps,hmargin⟩ := actual_uniform_cofactor_barrier_contraction_lower_two hK hw hwp
  have hneg : ∀ x ∈ U, w x < 0 := strictPshDirichlet_negative hU hK
    hw.continuous.continuousOn hw.contDiffOn hwb realDirections imagDirections
    (fun x hx => hwp x (subset_closure hx))
  let p : E → ℝ := fun x => -w x
  have hp : ContDiff ℝ 2 p := hw.neg
  have hp0 : MemH01 p U := actual_positive_boundary_barrier_memH01_two hU hK
    (hp.of_le (by norm_num)) (fun x hx => neg_pos.mpr (hneg x hx))
    (fun x hx => by dsimp only [p]; rw [hwb x hx,neg_zero])
  refine ⟨eps,heps,?_⟩
  intro c hc v hv hvp hvd A hA f u hf hu hu0 huC F hF hfb
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hv hvp hA
  let g : E → ℝ := quadraticScalarSourceTwo A.a p
  have hg : MemLp g 2 (volume.restrict U) := actual_smooth_scalar_source_memLp_two hK A hp
  have hpw : ActualScalarWeakEquationTwo A g p :=
    actual_smooth_divergenceFree_scalar_weak_two hU hK A hreg hdiv hp
  let k : ℝ := c*F/(2*eps)
  have hk : 0 ≤ k := div_nonneg (mul_nonneg hc.le hF) (by positivity)
  have hke : k*c⁻¹*(2*eps) = F := by
    dsimp only [k]
    field_simp [hc.ne',heps.ne']
  have hglo (x : E) (hx : x ∈ U) : F ≤ k*g x := by
    have he : g x = c⁻¹*(∑ i, ∑ j,
        complexCofactorCoeff v x i j*euclideanHessian w x i j) := by
      simpa only [neg_one_mul,one_mul,p,g] using
        actual_scalar_source_neg_cofactor_barrier_two A (k := 1) (hA x hx)
    rw [he,← mul_assoc]
    rw [← hke]
    exact mul_le_mul_of_nonneg_left (hmargin v hvp hvd x hx)
      (mul_nonneg hk (inv_nonneg.mpr hc.le))
  have hfg : ∀ᵐ x ∂volume.restrict U, |f x| ≤ k*g x := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact (hfb x hx).trans (hglo x hx)
  exact actual_zeroTrace_scalar_barrier_abs_two hU (hK.isBounded.subset subset_closure)
    hf (hg.const_mul k) hu (actual_scalar_weak_smul_two hU hpw k)
    hu0 (MemW01p.smul k hp0) huC (continuousOn_const.mul hp.continuous.continuousOn) hfg

end PowerConvexity
