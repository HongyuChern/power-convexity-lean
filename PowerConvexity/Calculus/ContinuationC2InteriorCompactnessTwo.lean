import PowerConvexity.Calculus.ContinuationC2LimitTwo
import PowerConvexity.Calculus.ClosureJetC1Compactness

/-! # Actual C1-compact sequence with a C2 interior CMA limit.
The same first-jet subsequence retains actual zero boundary values and
solves the limiting density equation everywhere in the interior. This
still does not supply a closure C2 jet or an interior C4 upgrade.
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
local instance cc2icRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance cc2icRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem continuation_density_sequence_C2_interior_compactness_two
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
      ∀ s₀ ∈ Icc (0 : ℝ) 1, Tendsto s atTop (𝓝 s₀) →
      ∀ u : ℕ → E → ℝ,
      (∀ n, ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w (s n)) (u n)) →
      ∀ J : ∀ n, ClosureC2Jet (u n) U,
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : E → ℝ, ∃ D : E → E →L[ℝ] ℝ,
        ContDiffOn ℝ 1 g (closure U) ∧ ContDiffOn ℝ 2 g U ∧
        (∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) g x).PosDef ∧
          (complexHessian e (fun j => Complex.I • e j) g x).det =
            (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s₀ x : ℂ)) ∧
        ContinuousOn D (closure U) ∧
        (∀ x ∈ closure U, HasFDerivWithinAt g (D x) (closure U) x) ∧
        (∀ x ∈ U, HasFDerivAt g (D x) x) ∧
        (∀ x ∈ frontier U, g x = 0) ∧
        TendstoUniformlyOn (fun n => u (phi n)) g atTop (closure U) ∧
        TendstoUniformlyOn (fun n => (J (phi n)).derivative) D atTop (closure U) ∧
        LipschitzOnWith C D (closure U) ∧
        ∀ x ∈ closure U, |g x| ≤ (C : ℝ) ∧ ‖D x‖ ≤ (C : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := continuation_density_uniform_closure_C2_bound_two
    hU hconv hK hboundary e hab hw hwb hwp hwd hf hfb hdef
  have hactual (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (v : E → ℝ)
      (hv : ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) v)
      (x : E) (hx : x ∈ U) : ‖fderiv ℝ v x‖ ≤ C ∧ ‖realHessian v x‖ ≤ C := by
    obtain ⟨Jv⟩ := hv.2.1
    have hh := (hbound s hs v hv Jv x (subset_closure hx)).2
    simpa only [Jv.derivative_eq hx,Jv.hessian_eq hx,realHessian] using hh
  refine ⟨⟨C,hC⟩,?_⟩
  intro s hs s₀ hs₀ hslim u hdata J
  obtain ⟨phi,hphi,g,D,hg1,hDc,hDcl,hDg,hgb,hval,hder,hLip,hgbound⟩ :=
    closureJet_C1_subsequence_of_uniform_C2_bound hU hconv hK u
      (fun n => (hdata n).1.of_le (by norm_num)) J
      (fun n => (hdata n).2.2.2.2) ⟨C,hC⟩
      (fun n x hx => hbound (s n) (hs n) (u n) (hdata n) (J n) x hx)
  have hpoint (x : E) (hx : x ∈ U) :
      Tendsto (fun n => fderiv ℝ (u (phi n)) x) atTop (𝓝 (D x)) := by
    have he : (fun n => fderiv ℝ (u (phi n)) x) =
        (fun n => (J (phi n)).derivative x) := funext (fun n => ((J (phi n)).derivative_eq hx).symm)
    rw [he]
    exact hder.tendsto_at (subset_closure hx)
  obtain ⟨hg2,hgsol⟩ := continuation_density_C1_limit_is_interior_C2_solution_two
    hU hconv hK e hab hw hwd hC hactual (fun n => hs (phi n)) hs₀
    (hslim.comp hphi.tendsto_atTop) (fun n => u (phi n)) (fun n => hdata (phi n)) hDg hpoint
  exact ⟨phi,hphi,g,D,hg1,hg2,hgsol,hDc,hDcl,hDg,hgb,hval,hder,hLip,hgbound⟩

end PowerConvexity
