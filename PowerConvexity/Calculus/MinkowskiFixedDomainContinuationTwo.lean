import PowerConvexity.Calculus.DirichletContinuationDensityTwo
import PowerConvexity.Calculus.MinkowskiJointGlobalStrictSubsolutionTwo

/-! # Actual continuation data on each fixed intermediate Minkowski domain

The original endpoint and domain hypotheses construct w, its actual right-hand
side, the solvable initial equation, positive uniform density bounds and the
same subsolution for every auxiliary parameter. There is no existence premise
inside this setup. Solving the auxiliary equations remains a separate step.
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

theorem classicalDirichlet_minkowski_fixed_continuation_setup_two
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
      (∀ s : ℝ, ContDiff ℝ 2 (dirichletContinuationDensityTwo e b w s)) ∧
      (∃ M : ℝ, 1 ≤ M ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ closure V,
        1 ≤ dirichletContinuationDensityTwo e b w s x ∧
          dirichletContinuationDensityTwo e b w s x ≤ M) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
        ClassicalDirichletDensityDataTwo e b V
          (dirichletContinuationDensityTwo e b w s) v →
        (∀ x ∈ closure V, w x ≤ v x) ∧ (∀ x ∈ V, v x < 0)) := by
  let b := fun j => Complex.I • e j
  let V := minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨d,hd,W,hW,hdata⟩ :=
    classicalDirichlet_minkowski_exists_joint_global_strict_subsolution_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1.le hR
  have hactual := hdata t (mem_closedBall_self hd.le) ⟨ht.le,ht1.le⟩
  let w : E → ℝ := fun x => W (t,x)
  have hw : ContDiff ℝ 4 w := hactual.1
  have hwp (x : E) (hx : x ∈ V) : (complexHessian e b w x).PosDef :=
    (hactual.2.2.2 x (subset_closure hx)).1
  have hwd (x : E) (hx : x ∈ closure V) :
      (1 : ℝ) ≤ (complexHessian e b w x).det.re := by
    have hh := (Complex.lt_def.mp (hactual.2.2.2 x hx).2).1
    exact le_of_lt hh
  have hwb : ∀ x ∈ frontier V, w x = 0 := fun x hx => (hactual.2.2.1 x hx).1
  have hVK : IsCompact (closure V) := by
    have hBK : IsCompact (closure (ball (0 : E) R)) := by
      rw [closure_ball 0 hR.ne']
      exact isCompact_closedBall 0 R
    dsimp only [V]
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul t).add (hBK.smul (1-t))
  have hVo : IsOpen V :=
    (minkowskiDomain_real_parameterGraph_isOpen hU isOpen_ball).preimage
      (continuous_const.prodMk continuous_id)
  refine ⟨w,hw,hactual.2.2.2,hwb,
    dirichletContinuationDensityTwo_start e b hw hwp hwb,
    dirichletContinuationDensityTwo_contDiff e b hw,
    dirichletContinuationDensityTwo_uniform_bounds e b hVK hw hwd,?_⟩
  intro s hs v hv
  exact ⟨dirichletContinuationDensityTwo_subsolution_le e b hab hVo hVK hw hwp
    (fun x hx => hwd x (subset_closure hx)) hwb hs hv,
    dirichletContinuationDensityTwo_solution_negative e b hVo hVK hv⟩

end PowerConvexity
