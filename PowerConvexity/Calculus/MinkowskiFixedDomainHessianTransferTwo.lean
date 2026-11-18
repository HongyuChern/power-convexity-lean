import PowerConvexity.Calculus.MinkowskiFixedDomainContinuationTwo
import PowerConvexity.Calculus.VariableDensityHessianBoundaryMaximumTwo

/-! # Uniform boundary-to-interior Hessian transfer on the actual fixed domain

The correction constant is chosen before every auxiliary parameter and
solution. An actual uniform boundary Hessian estimate remains to be proved.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]

theorem classicalDirichlet_minkowski_fixed_uniform_hessian_transfer_two
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
    ∃ w : E → ℝ, ContDiff ℝ 4 w ∧
      (∀ x ∈ closure V, (complexHessian e b w x).PosDef ∧
        (1 : ℂ) < (complexHessian e b w x).det) ∧
      (∀ x ∈ frontier V, w x = 0) ∧
      ClassicalDirichletDensityDataTwo e b V
        (dirichletContinuationDensityTwo e b w 0) w ∧
      ∃ N : ℝ, 0 ≤ N ∧ ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ v : E → ℝ, ClassicalDirichletDensityDataTwo e b V
          (dirichletContinuationDensityTwo e b w s) v →
        ∀ Jv : ClosureC2Jet v V, ∀ z : E, ‖z‖ = 1 →
          ∀ M : ℝ, (∀ x ∈ frontier V, Jv.hessian x z z ≤ M) →
            ∀ x ∈ closure V, Jv.hessian x z z ≤ M+N := by
  let b := fun j => Complex.I • e j
  let V := minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨w,hw,hwp,hwb,hstart,hreg,hdb,hcomp⟩ :=
    classicalDirichlet_minkowski_fixed_continuation_setup_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR
  have hVo : IsOpen V :=
    (minkowskiDomain_real_parameterGraph_isOpen hU isOpen_ball).preimage
      (continuous_const.prodMk continuous_id)
  have hVK : IsCompact (closure V) := by
    have hBK : IsCompact (closure (ball (0 : E) R)) := by
      rw [closure_ball 0 hR.ne']
      exact isCompact_closedBall 0 R
    dsimp only [V]
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul t).add (hBK.smul (1-t))
  have hd : ∀ x ∈ closure V, (1 : ℝ) ≤ (complexHessian e b w x).det.re := by
    intro x hx
    exact (Complex.lt_def.mp (hwp x hx).2).1.le
  obtain ⟨C,hC,htransfer⟩ :=
    continuation_density_uniform_directional_boundary_to_interior_two e b hVo hVK hw hd
  obtain ⟨B,hB⟩ := (hVK.image hw.continuous).isBounded.exists_norm_le
  let N : ℝ := (C/2)*max B 0
  have hN : 0 ≤ N := mul_nonneg (div_nonneg hC (by norm_num)) (le_max_right _ _)
  refine ⟨w,hw,hwp,hwb,hstart,N,hN,?_⟩
  intro s hs v hv Jv z hz M hM x hx
  have hh := htransfer s hs v hv Jv z hz M hM x hx
  have hwB : -w x ≤ max B 0 := by
    have hnorm : ‖w x‖ ≤ B := hB (w x) ⟨x,hx,rfl⟩
    have habs : |w x| ≤ B := by simpa only [Real.norm_eq_abs] using hnorm
    exact (neg_le_abs (w x)).trans (habs.trans (le_max_left _ _))
  have hvB : -v x ≤ max B 0 := (neg_le_neg ((hcomp s hs v hv).1 x hx)).trans hwB
  have hscale := mul_le_mul_of_nonneg_left hvB (div_nonneg hC (by norm_num : (0 : ℝ) ≤ 2))
  dsimp only [N]
  linarith

end PowerConvexity
