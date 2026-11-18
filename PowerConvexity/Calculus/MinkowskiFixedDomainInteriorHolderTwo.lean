import PowerConvexity.Calculus.MinkowskiFixedDomainClosureC2Two
import PowerConvexity.Calculus.ContinuationUniformInteriorHolderTwo

/-! # Uniform actual interior Holder estimates from the unchanged original endpoint -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder Pointwise Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance mfhcRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance mfhcRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem classicalDirichlet_minkowski_fixed_uniform_interior_holder_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R) :
    let b := fun j => Complex.I • e j
    let V := minkowskiDomain t U (ball (0 : E) R)
    ∃ w f : E → ℝ, ContDiff ℝ 6 w ∧ ContDiff ℝ 6 f ∧
      (∀ x ∈ closure V, (complexHessian e b w x).PosDef ∧
        (1 : ℂ) < (complexHessian e b w x).det) ∧
      (∀ x ∈ frontier V, w x = 0) ∧
      (∀ x ∈ frontier V, f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
        (∀ᶠ z in 𝓝 x, z ∈ V ↔ f z < 0)) ∧
      ClassicalDirichletDensityDataTwo e b V (dirichletContinuationDensityTwo e b w 0) w ∧
      (∀ s : ℝ, ContDiff ℝ 4 (dirichletContinuationDensityTwo e b w s)) ∧
      ∃ T : DeGiorgi.AmbientSpace (2+2) ≃ₗᵢ[ℝ] E,
        (∀ i, T (CHS.Analysis.realDirections i) = e i) ∧
        (∀ i, T (CHS.Analysis.imagDirections i) = Complex.I • e i) ∧
        ∀ rho : ℝ, 0 < rho → ∃ alpha C : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
          ClassicalDirichletDensityDataTwo e b V (dirichletContinuationDensityTwo e b w s) v →
          ∀ x₀ : DeGiorgi.AmbientSpace (2+2), ball x₀ (2*rho) ⊆ T ⁻¹' V →
          ∀ x ∈ ball x₀ rho, ∀ y ∈ ball x₀ rho,
            ‖realBlockHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections (fun z => v (T z)) x-
              realBlockHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections (fun z => v (T z)) y‖ ≤
                C*(‖x-y‖/rho)^alpha := by
  let b := fun j => Complex.I • e j
  let V := minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨w,f,hw,hf,hwp,hwb,hfb,hstart,hreg,M,hM,hbound⟩ :=
    classicalDirichlet_minkowski_fixed_uniform_closure_C2_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR
  have hVo : IsOpen V := by
    dsimp only [V]
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  have hVK : IsCompact (closure V) := by
    have hBK : IsCompact (closure (ball (0 : E) R)) := by
      rw [closure_ball 0 hR.ne']
      exact isCompact_closedBall 0 R
    dsimp only [V]
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul t).add (hBK.smul (1-t))
  refine ⟨w,f,hw,hf,hwp,hwb,hfb,hstart,hreg,?_⟩
  apply continuation_density_uniform_isometric_interior_holder_two hVo
    (minkowskiDomain_convex hconv (convex_ball (0 : E) R) t) hVK e hab
    (hw.of_le (by norm_num))
    (fun x hx => le_of_lt (Complex.lt_def.mp (hwp x hx).2).1) hM
  intro s hs v hv x hx
  obtain ⟨Jv⟩ := hv.2.1
  have hh := hbound s hs v hv Jv x (subset_closure hx)
  simpa only [Jv.derivative_eq hx,Jv.hessian_eq hx,realHessian] using hh.2

end PowerConvexity
