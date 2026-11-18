import PowerConvexity.Calculus.MinkowskiFixedDomainCofactorTwo
import PowerConvexity.Calculus.ActualPhysicalLinearizedDirichletTwo

/-! # Actual physical-domain classical linearized Dirichlet solves

The original endpoint hypotheses construct the same strict subsolution,
variable density path, fixed coordinates and uniformly elliptic coefficients.
Every C1 physical load has a unique classical C2 interior zero-boundary
solution on the same physical domain. The actual H01 equation is retained in
the fixed coordinates. Closure C2 regularity remains a separate task.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance mfplRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance mfplRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local notation "F" => AmbientSpace (2+2)

theorem classicalDirichlet_minkowski_fixed_physical_linearized_dirichlet_two
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
    ∃ w : E → ℝ, ContDiff ℝ 6 w ∧
      (∀ x ∈ closure V, (complexHessian e b w x).PosDef ∧
        (1 : ℂ) < (complexHessian e b w x).det) ∧
      (∀ x ∈ frontier V, w x = 0) ∧
      ClassicalDirichletDensityDataTwo e b V (dirichletContinuationDensityTwo e b w 0) w ∧
      ∃ L : F ≃ₗᵢ[ℝ] E,
        (∀ i, L (realDirections i) = e i) ∧
        (∀ i, L (imagDirections i) = Complex.I • e i) ∧
        ∃ c : ℝ, 0 < c ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
          ClassicalDirichletDensityDataTwo e b V (dirichletContinuationDensityTwo e b w s) v →
          ∃ B : NormalizedEllipticCoeff (2+2) (L ⁻¹' V), B.1.Λ = Λ ∧
            (∀ x ∈ L ⁻¹' V, B.1.a x = c⁻¹ • complexCofactorCoeff (fun y => v (L y)) x) ∧
            ∀ g : E → ℝ, ContDiff ℝ 1 g → ∃ h : E → ℝ,
              Continuous h ∧ ContDiffOn ℝ 2 h V ∧
              (∀ x ∈ frontier V, h x = 0) ∧
              (∀ x ∈ V, linearizedCMAOperatorTwo e b v h x = g x) ∧
              MemH01 (fun y => h (L y)) (L ⁻¹' V) ∧
              ActualScalarWeakEquationTwo B.1
                (fun y => -(c⁻¹*dirichletContinuationDensityTwo e b w s (L y)*g (L y)))
                (fun y => h (L y)) ∧
              ∀ k : E → ℝ, ContinuousOn k (closure V) → ContDiffOn ℝ 2 k V →
                (∀ x ∈ frontier V, k x = 0) →
                (∀ x ∈ V, linearizedCMAOperatorTwo e b v k x = g x) → EqOn h k (closure V) := by
  let b := fun j => Complex.I • e j
  let V := minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨w,f,hw,hf,hwp,hwb,hfb,hstart,hreg,L,hLa,hLb,c,hc,Λ,hΛ,hcoeff⟩ :=
    classicalDirichlet_minkowski_fixed_uniform_cofactor_ellipticity_two
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
  refine ⟨w,hw,hwp,hwb,hstart,L,hLa,hLb,c,hc,Λ,hΛ,?_⟩
  intro s hs v hv
  obtain ⟨B,hBΛ,hB⟩ := hcoeff s hs v hv
  refine ⟨B,hBΛ,hB,?_⟩
  intro g hg
  apply actual_physical_linearized_zero_boundary_dirichlet_two hVo hVK L e b hLa hLb
    (hw.of_le (by norm_num)) (fun x hx => (hwp x hx).1) hwb hv.1 hv.continuous_closure hv.2.2.2.2 hv.2.2.1 hv.2.2.2.1
    ((hreg s).of_le (by norm_num)) ?_ hc B.1 hB g hg
  intro x hx
  exact (dirichletContinuationDensityTwo_bounds e b hs
    (le_of_lt (Complex.lt_def.mp (hwp x (subset_closure hx)).2).1)).1

end PowerConvexity
