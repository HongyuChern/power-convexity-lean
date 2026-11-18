import PowerConvexity.Calculus.ClosureJetC1Compactness

/-! # A single C1-convergent subsequence of actual auxiliary Dirichlet solutions.
The constant is chosen before the parameter sequence and all solutions. The
limit has actual zero boundary values and a Lipschitz first derivative. No
classical second derivative or determinant equation for the limit is asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance cc1cRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance cc1cRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem continuation_density_sequence_C1_compactness_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w) (hwb : ∀ y ∈ frontier U, w y = 0)
    (hwp : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w y).PosDef)
    (hwd : ∀ y ∈ closure U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w y).det.re)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfb : ∀ x ∈ frontier U, f x = 0 ∧ fderiv ℝ f x ≠ 0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ∃ C : NNReal, ∀ s : ℕ → ℝ, (∀ n, s n ∈ Icc (0 : ℝ) 1) →
      ∀ u : ℕ → E → ℝ,
      (∀ n, ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w (s n)) (u n)) →
      ∀ J : ∀ n, ClosureC2Jet (u n) U,
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : E → ℝ, ∃ D : E → E →L[ℝ] ℝ,
        ContDiffOn ℝ 1 g (closure U) ∧ ContinuousOn D (closure U) ∧
        (∀ x ∈ closure U, HasFDerivWithinAt g (D x) (closure U) x) ∧
        (∀ x ∈ U, HasFDerivAt g (D x) x) ∧
        (∀ x ∈ frontier U, g x = 0) ∧
        TendstoUniformlyOn (fun n => u (phi n)) g atTop (closure U) ∧
        TendstoUniformlyOn (fun n => (J (phi n)).derivative) D atTop (closure U) ∧
        LipschitzOnWith C D (closure U) ∧
        ∀ x ∈ closure U, |g x| ≤ (C : ℝ) ∧ ‖D x‖ ≤ (C : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := continuation_density_uniform_closure_C2_bound_two
    hU hconv hK hboundary e hab hw hwb hwp hwd hf hfb hdef
  refine ⟨⟨C,hC⟩,?_⟩
  intro s hs u hdata J
  exact closureJet_C1_subsequence_of_uniform_C2_bound hU hconv hK u
    (fun n => (hdata n).1.of_le (by norm_num)) J
    (fun n => (hdata n).2.2.2.2) ⟨C,hC⟩
    (fun n x hx => hbound (s n) (hs n) (u n) (hdata n) (J n) x hx)

end PowerConvexity
