import PowerConvexity.Analysis.ActualScalarWeakC2RepresentativeTwo
import PowerConvexity.Calculus.CofactorLinearizedDirichletTwo

/-! # Actual zero-trace Dirichlet solutions with C2 interior regularity

Zero trace refers to the original H01 space. No classical pointwise boundary
value or closure C2 jet is inferred solely from that trace.
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

theorem actual_zeroTrace_C2_interior_dirichlet_exists_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U)
    (hpos : ∀ x ∈ U, (A.a x).PosDef)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U)
    (hdiv : ∀ y ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun z => A.a z i j) y (EuclideanSpace.single i 1)) = 0)
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict U)) (hfC : ContDiffOn ℝ 1 f U) :
    ∃ v : E → ℝ, MemH01 v U ∧ ContDiffOn ℝ 2 v U ∧ ActualScalarWeakEquationTwo A f v ∧
      (∀ x ∈ U, (∑ i, ∑ j, A.a x i j*euclideanHessian v x i j) = -f x) ∧
      ∀ w : E → ℝ, MemH01 w U → ActualScalarWeakEquationTwo A f w →
        ContinuousOn w U → EqOn v w U := by
  obtain ⟨u,hu,huniq⟩ := scalar_weak_dirichlet_exists (by norm_num : 2 ≤ 2+2) hU hUb A hf
  obtain ⟨v,hvu,hvC,hvw,hvPDE⟩ := actual_scalar_weak_C2_interior_representative_two hU A
    hpos hreg hdiv hf hfC (actual_scalar_weak_equation_of_dirichlet_two hU hUb A hu)
  have hv0 := actual_zeroTrace_congr_ae hvu.symm hu.1
  refine ⟨v,hv0,hvC,hvw,hvPDE,?_⟩
  intro w hw0 hww hwC
  have huw : u =ᵐ[volume.restrict U] w := huniq w ⟨hw0,hww.2⟩
  exact Measure.eqOn_open_of_ae_eq (hvu.trans huw) hU hvC.continuousOn hwC

theorem actual_scaled_cofactor_C2_interior_dirichlet_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {w : E → ℝ} (hw : ContDiffOn ℝ 4 w U)
    (hpsh : ∀ x ∈ U, (complexHessian realDirections imagDirections w x).PosDef)
    {c : ℝ} (hc : 0 < c) (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff w x)
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict U)) (hfC : ContDiffOn ℝ 1 f U) :
    ∃ v : E → ℝ, MemH01 v U ∧ ContDiffOn ℝ 2 v U ∧ ActualScalarWeakEquationTwo A f v ∧
      (∀ x ∈ U, (complexHessian realDirections imagDirections w x).det.re *
        linearizedCMAOperatorTwo realDirections imagDirections w v x = -c*f x) ∧
      ∀ k : E → ℝ, MemH01 k U → ActualScalarWeakEquationTwo A f k →
        ContinuousOn k U → EqOn v k U := by
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hw hpsh hA
  have hpos : ∀ x ∈ U, (A.a x).PosDef := by
    intro x hx
    rw [hA x hx]
    exact (complexCofactorCoeff_posDef (hpsh x hx)).smul (inv_pos.mpr hc)
  obtain ⟨v,hv0,hvC,hvw,hvPDE,huniq⟩ := actual_zeroTrace_C2_interior_dirichlet_exists_two
    hU hUb A hpos hreg hdiv hf hfC
  refine ⟨v,hv0,hvC,hvw,?_,huniq⟩
  intro x hx
  have hpde := hvPDE x hx
  rw [hA x hx] at hpde
  simp only [Matrix.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum] at hpde
  rw [complexCofactor_contraction_eq_density_linearized_two (hpsh x hx)] at hpde
  have hh := congrArg (fun a : ℝ => c*a) hpde
  simpa only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul,mul_neg,neg_mul] using hh

end PowerConvexity
