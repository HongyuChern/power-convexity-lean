import PowerConvexity.Calculus.DirichletContinuationDensityC4Two
import PowerConvexity.Calculus.MinkowskiC6StrictSubsolutionTwo

/-! # C4 right-hand side on each actual fixed intermediate Minkowski domain

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

theorem classicalDirichlet_minkowski_fixed_C4_density_setup_two
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
      ClassicalDirichletDensityDataTwo e b V
        (dirichletContinuationDensityTwo e b w 0) w ∧
      (∀ s : ℝ, ContDiff ℝ 4 (dirichletContinuationDensityTwo e b w s)) ∧
      (∃ M : ℝ, 1 ≤ M ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ closure V,
        1 ≤ dirichletContinuationDensityTwo e b w s x ∧
          dirichletContinuationDensityTwo e b w s x ≤ M) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
        ClassicalDirichletDensityDataTwo e b V
          (dirichletContinuationDensityTwo e b w s) v →
        (∀ x ∈ closure V, w x ≤ v x) ∧ (∀ x ∈ V, v x < 0)) := by
  let b := fun j => Complex.I • e j
  let V := minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨w,hw6,_,hboundaryw,hactual⟩ :=
    classicalDirichlet_minkowski_exists_global_C6_strict_subsolution_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR
  have hw : ContDiff ℝ 4 w := hw6.of_le (by norm_num)
  have hwp (x : E) (hx : x ∈ V) : (complexHessian e b w x).PosDef :=
    (hactual x (subset_closure hx)).1
  have hwd (x : E) (hx : x ∈ closure V) :
      (1 : ℝ) ≤ (complexHessian e b w x).det.re :=
    le_of_lt (Complex.lt_def.mp (hactual x hx).2).1
  have hwb : ∀ x ∈ frontier V, w x = 0 := fun x hx => (hboundaryw x hx).1
  have hVK : IsCompact (closure V) := by
    have hBK : IsCompact (closure (ball (0 : E) R)) := by
      rw [closure_ball 0 hR.ne']
      exact isCompact_closedBall 0 R
    dsimp only [V]
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul t).add (hBK.smul (1-t))
  have hVo : IsOpen V := by
    dsimp only [V]
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  refine ⟨w,hw6,hactual,hwb,
    dirichletContinuationDensityTwo_start e b hw hwp hwb,
    dirichletContinuationDensityTwo_contDiff_C4 e b hw6,
    dirichletContinuationDensityTwo_uniform_bounds e b hVK hw hwd,?_⟩
  intro s hs v hv
  exact ⟨dirichletContinuationDensityTwo_subsolution_le e b hab hVo hVK hw hwp
    (fun x hx => hwd x (subset_closure hx)) hwb hs hv,
    dirichletContinuationDensityTwo_solution_negative e b hVo hVK hv⟩

end PowerConvexity
