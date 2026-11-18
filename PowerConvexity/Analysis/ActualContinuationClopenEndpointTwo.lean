import PowerConvexity.Analysis.ActualUniformContinuationClosednessTwo
import Mathlib.Topology.Connected.Clopen

/-! # Exact classical endpoint assembly for the original continuation density

Actual closedness is proved in the imported module. This topological
assembly states its openness input explicitly; it retains the actual
classical solution and obtains the determinant-one endpoint by the proved
identity of densities, without using any old convexity conclusion.
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
local instance acceRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance acceRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem actual_continuation_classical_solvable_of_open_two
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
    (hopen : IsOpen {s : Icc (0 : ℝ) 1 | ∃ u : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) u}) :
    ∀ s : Icc (0 : ℝ) 1, ∃ u : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) u := by
  let S := {s : Icc (0 : ℝ) 1 | ∃ u : E → ℝ,
    ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
      (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) u}
  have hclosed : IsClosed S := actual_continuation_classical_solvable_isClosed_two
    hU hconv hK hgeometry e hab hw hwb hwp hwd hf hfb hdef
  have hne : S.Nonempty := by
    refine ⟨⟨0,by constructor <;> norm_num⟩,w,?_⟩
    exact dirichletContinuationDensityTwo_start e (fun j => Complex.I • e j)
      (hw.of_le (by norm_num)) (fun x hx => hwp x (subset_closure hx)) hwb
  have hSu : S=univ := (show IsClopen S from ⟨hclosed,hopen⟩).eq_univ hne
  intro s
  have hs : s∈S := by rw [hSu]; trivial
  exact hs

theorem actual_continuation_classical_endpoint_of_open_two
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
    (hopen : IsOpen {s : Icc (0 : ℝ) 1 | ∃ u : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) u}) :
    ∃ u : E → ℝ, ClassicalDirichletDataTwo e (fun j => Complex.I • e j) U u := by
  obtain ⟨u,hu⟩ := actual_continuation_classical_solvable_of_open_two hU hconv hK hgeometry
    e hab hw hwb hwp hwd hf hfb hdef hopen ⟨1,by constructor <;> norm_num⟩
  exact ⟨u,(dirichletContinuationDensityTwo_end_iff e (fun j => Complex.I • e j) U w u).mp hu⟩

end PowerConvexity
