import PowerConvexity.Analysis.ActualUniformContinuationBoundaryModulusTwo
import PowerConvexity.Calculus.ActualContinuationClosednessFromBoundaryTwo
import Mathlib.Topology.Sequences

/-! # Actual closedness of classical nonlinear continuation

The common boundary Hessian estimate is proved from the actual fixed
subsolution and original geometry before it is supplied to the established
C4 interior compactness and closure-jet limit construction. The same limit
has true zero trace, strict plurisubharmonicity and the limiting density.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance auccRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance auccRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem actual_continuation_classical_limit_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hgeometry : HasC2LocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 6 w) (hwb : ∀ y ∈ frontier U, w y=0)
    (hwp : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w y).PosDef)
    (hwd : ∀ y ∈ closure U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w y).det.re)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    {s : ℕ → ℝ} (hs : ∀ n, s n∈Icc (0 : ℝ) 1)
    {s₀ : ℝ} (hs₀ : s₀∈Icc (0 : ℝ) 1) (hslim : Tendsto s atTop (𝓝 s₀))
    (hex : ∀ n, ∃ u : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w (s n)) u) :
    ∃ u : E → ℝ, ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
      (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s₀) u := by
  obtain ⟨R,hR,_,alpha,ha,_,C,_,hboundary⟩ :=
    actual_continuation_uniform_boundary_hessian_modulus_two hU hconv hK hgeometry e hab
      hw hwb hwp hwd hf hfb hdef
  exact continuation_density_actual_classical_limit_of_boundary_modulus_two
    hU hconv hK hgeometry e hab hw hwb hwp hwd hf hfb hdef hR ha hboundary hs hs₀ hslim hex

theorem actual_continuation_classical_solvable_isClosed_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hgeometry : HasC2LocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 6 w) (hwb : ∀ y ∈ frontier U, w y=0)
    (hwp : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w y).PosDef)
    (hwd : ∀ y ∈ closure U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w y).det.re)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0) :
    IsClosed {s : Icc (0 : ℝ) 1 | ∃ u : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) u} := by
  apply IsSeqClosed.isClosed
  intro s s₀ hs hslim
  exact actual_continuation_classical_limit_two hU hconv hK hgeometry e hab
    hw hwb hwp hwd hf hfb hdef (fun n => (s n).property) s₀.property
    (continuous_subtype_val.continuousAt.tendsto.comp hslim) hs

end PowerConvexity
