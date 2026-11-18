import PowerConvexity.Analysis.ActualCofactorZeroBoundaryRepresentativeTwo
import PowerConvexity.Calculus.CMAJetsIsometricTransport

/-! # The actual isometric linearized equation with classical zero boundary -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "F" => AmbientSpace (2+2)

theorem actual_isometric_cofactor_classical_zero_boundary_two
    {V : Set E} (hV : IsOpen V) (hK : IsCompact (closure V))
    (L : F ≃ₗᵢ[ℝ] E) (a b : Fin 2 → E)
    (hLa : ∀ i, L (realDirections i) = a i) (hLb : ∀ i, L (imagDirections i) = b i)
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure V, (complexHessian a b w x).PosDef)
    (hwb : ∀ x ∈ frontier V, w x = 0)
    {v ρ : E → ℝ} (hv : ContDiffOn ℝ 4 v V)
    (hvp : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    (hvd : ∀ x ∈ V, (complexHessian a b v x).det = (ρ x : ℂ))
    (hρ : ContDiff ℝ 1 ρ) (hρlo : ∀ x ∈ V, 1 ≤ ρ x)
    {c : ℝ} (hc : 0 < c) (A : EllipticCoeff (2+2) (L ⁻¹' V))
    (hA : ∀ x ∈ L ⁻¹' V, A.a x = c⁻¹ • complexCofactorCoeff (fun y => v (L y)) x)
    (g : E → ℝ) (hg : ContDiff ℝ 1 g) :
    ∃ H : F → ℝ, Continuous H ∧ ContDiffOn ℝ 2 H (L ⁻¹' V) ∧ MemH01 H (L ⁻¹' V) ∧
      (∀ x ∈ frontier (L ⁻¹' V), H x = 0) ∧
      (∀ x ∈ L ⁻¹' V,
        linearizedCMAOperatorTwo realDirections imagDirections (fun y => v (L y)) H x = g (L x)) ∧
      ActualScalarWeakEquationTwo A (fun x => -(c⁻¹*ρ (L x)*g (L x))) H := by
  have hU : IsOpen (L ⁻¹' V) := hV.preimage L.continuous
  have hcl : L ⁻¹' closure V = closure (L ⁻¹' V) := L.toHomeomorph.preimage_closure V
  have hUK : IsCompact (closure (L ⁻¹' V)) := by
    rw [← hcl]
    exact L.toHomeomorph.isCompact_preimage.mpr hK
  have hwL : ContDiff ℝ 2 (fun y => w (L y)) := hw.comp L.toContinuousLinearEquiv.contDiff
  have hvL : ContDiffOn ℝ 4 (fun y => v (L y)) (L ⁻¹' V) :=
    hv.comp L.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hx => hx)
  have hwH (x : F) : complexHessian realDirections imagDirections (fun y => w (L y)) x =
      complexHessian a b w (L x) := by
    simpa only [hLa,hLb] using complexHessian_comp_linearIsometry L (x := x) hw.contDiffAt
  have hvH (x : F) (hx : x ∈ L ⁻¹' V) :
      complexHessian realDirections imagDirections (fun y => v (L y)) x =
        complexHessian a b v (L x) := by
    simpa only [hLa,hLb] using complexHessian_comp_linearIsometry L
      ((hv.contDiffAt (hV.mem_nhds hx)).of_le (by norm_num))
  have hwLp : ∀ x ∈ closure (L ⁻¹' V),
      (complexHessian realDirections imagDirections (fun y => w (L y)) x).PosDef := by
    intro x hx
    rw [hwH]
    exact hwp _ (by rw [← hcl] at hx; exact hx)
  have hwLb : ∀ x ∈ frontier (L ⁻¹' V), w (L x) = 0 := by
    intro x hx
    have hfr : L ⁻¹' frontier V = frontier (L ⁻¹' V) := L.toHomeomorph.preimage_frontier V
    rw [← hfr] at hx
    exact hwb _ hx
  have hvLp : ∀ x ∈ L ⁻¹' V,
      (complexHessian realDirections imagDirections (fun y => v (L y)) x).PosDef := by
    intro x hx
    rw [hvH x hx]
    exact hvp _ hx
  have hvLd : ∀ x ∈ L ⁻¹' V,
      1 ≤ (complexHessian realDirections imagDirections (fun y => v (L y)) x).det.re := by
    intro x hx
    rw [hvH x hx,hvd _ hx,Complex.ofReal_re]
    exact hρlo _ hx
  let load : F → ℝ := fun x => -(c⁻¹*ρ (L x)*g (L x))
  have hload : ContDiff ℝ 1 load :=
    ((contDiff_const.mul (hρ.comp L.toContinuousLinearEquiv.contDiff)).mul
      (hg.comp L.toContinuousLinearEquiv.contDiff)).neg
  obtain ⟨H,hHC,hHC2,hH0,hHw,hHb,hHPDE,_⟩ :=
    actual_cofactor_classical_zero_boundary_dirichlet_exists_two hU hUK hwL hwLp hwLb
      hvL hvLp hvLd hc A hA hload.continuous.continuousOn hload.contDiffOn
  refine ⟨H,hHC,hHC2,hH0,hHb,?_,hHw⟩
  intro x hx
  have hh := hHPDE x hx
  rw [hvH x hx,hvd _ hx,Complex.ofReal_re] at hh
  have he : -c*load x = ρ (L x)*g (L x) := by
    dsimp only [load]
    field_simp [hc.ne']
  rw [he] at hh
  exact (mul_left_cancel₀ (by have hr := hρlo (L x) hx; linarith : ρ (L x) ≠ 0)) hh

end PowerConvexity
