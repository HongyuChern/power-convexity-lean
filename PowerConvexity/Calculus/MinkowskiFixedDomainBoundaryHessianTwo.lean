import PowerConvexity.Calculus.MinkowskiFixedDomainC4DensityTwo
import PowerConvexity.Calculus.ContinuationUniformQuadraticBoundaryTwo

/-! # Actual fixed-domain auxiliary full boundary Hessian estimates from the original endpoint -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]

theorem classicalDirichlet_minkowski_fixed_uniform_boundary_hessian_two
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
      ∃ M ≥ 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
        ClassicalDirichletDensityDataTwo e b V (dirichletContinuationDensityTwo e b w s) v →
        ∀ Jv : ClosureC2Jet v V, ∀ x ∈ frontier V, ∀ z : E,
          Jv.hessian x z z ≤ M*‖z‖^2 := by
  let b := fun j => Complex.I • e j
  let V := minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨w,hw,hwp,hwb,hstart,hreg,_,_⟩ := classicalDirichlet_minkowski_fixed_C4_density_setup_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR
  obtain ⟨f,hf,_,hfb⟩ := classicalDirichlet_minkowski_exists_global_regular_C6_Levi_defining_two
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
  have hbV : HasC2LocalDefiningFunction V := smoothLocalDefiningFunction_implies_C2
    (minkowskiDomain_hasSmoothLocalDefiningFunction hU hconv hK hboundary ht ht1 hR)
  refine ⟨w,f,hw,hf,hwp,hwb,(fun x hx => ⟨(hfb x hx).1,(hfb x hx).2.1,(hfb x hx).2.2.1⟩),
    hstart,hreg,?_⟩
  exact continuation_density_uniform_boundary_quadratic_upper_two hVo
    (minkowskiDomain_convex hconv (convex_ball (0 : E) R) t) hVK hbV e hab
    (hw.of_le (by norm_num)) hwb (fun x hx => (hwp x hx).1)
    (fun x hx => le_of_lt (Complex.lt_def.mp (hwp x hx).2).1)
    (hf.of_le (by norm_num)) (fun x hx => ⟨(hfb x hx).1,(hfb x hx).2.1⟩)
    (fun x hx => (hfb x hx).2.2.1)

end PowerConvexity
