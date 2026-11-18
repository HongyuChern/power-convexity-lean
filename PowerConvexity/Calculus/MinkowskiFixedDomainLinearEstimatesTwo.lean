import PowerConvexity.Calculus.MinkowskiFixedDomainContinuationTwo
import PowerConvexity.Calculus.VariableDensityTraceBarrierTwo

/-! # Uniform linear estimates along the actual fixed-domain density path

The constants below are chosen before the auxiliary parameter and before an
auxiliary solution. They give estimates for a solution if one exists; they do
not assert surjectivity of the linear Dirichlet operator or nonlinear existence.
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

theorem classicalDirichlet_minkowski_fixed_uniform_linear_estimates_two
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
    ∃ w : E → ℝ, ∃ D c C : ℝ, 1 ≤ D ∧ 0 < c ∧ 0 ≤ C ∧
      ContDiff ℝ 4 w ∧
      (∀ x ∈ closure V, (complexHessian e b w x).PosDef ∧
        (1 : ℂ) < (complexHessian e b w x).det) ∧
      (∀ x ∈ frontier V, w x = 0) ∧
      ClassicalDirichletDensityDataTwo e b V
        (dirichletContinuationDensityTwo e b w 0) w ∧
      (∀ s : ℝ, ContDiff ℝ 2 (dirichletContinuationDensityTwo e b w s)) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ closure V,
        1 ≤ dirichletContinuationDensityTwo e b w s x ∧
          dirichletContinuationDensityTwo e b w s x ≤ D) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
        ClassicalDirichletDensityDataTwo e b V
          (dirichletContinuationDensityTwo e b w s) v →
        (∀ x ∈ closure V, w x ≤ v x) ∧
        (∀ x ∈ V, v x < 0) ∧
        (∀ x ∈ V,
          linearizedCMAOperatorTwo e b v (fun y => v y-c*w y) x ≤
            -(1+((complexHessian e b v x)⁻¹).trace.re)) ∧
        (∀ f : E → ℝ, ContinuousOn f (closure V) → ContDiffOn ℝ 2 f V →
          (∀ x ∈ frontier V, f x = 0) →
          ∀ F : ℝ, 0 ≤ F →
            (∀ x ∈ V, |linearizedCMAOperatorTwo e b v f x| ≤ F) →
            ∀ x ∈ closure V, |f x| ≤ C*F) := by
  let b := fun j => Complex.I • e j
  let V := minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨w,hw,hwp,hwb,hstart,hreg,⟨D,hD,hdb⟩,hcomp⟩ :=
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
  obtain ⟨c,hc,hbarrier⟩ := strictPsh_variable_density_uniform_trace_barrier_two
    e hab hVo hVK (hw.of_le (by norm_num)) (fun x hx => (hwp x hx).1) hD
  obtain ⟨B,hB⟩ := (hVK.image hw.continuous).isBounded.exists_norm_le
  let C : ℝ := max B 0 / 2
  have hC : 0 ≤ C := div_nonneg (le_max_right _ _) (by norm_num)
  refine ⟨w,D,c,C,hD,hc,hC,hw,hwp,hwb,hstart,hreg,hdb,?_⟩
  intro s hs v hv
  have hle := (hcomp s hs v hv).1
  have hv2 : ContDiffOn ℝ 2 v V := hv.1.of_le (by norm_num)
  refine ⟨hle,(hcomp s hs v hv).2,?_,?_⟩
  · apply hbarrier v hv2 hv.2.2.1
    intro x hx
    have he := congrArg Complex.re (hv.2.2.2.1 x hx)
    simpa only [he,Complex.ofReal_re] using (hdb s hs x (subset_closure hx)).2
  · intro f hfc hf hfb F hF hLf x hx
    have hh := linearizedCMAOperatorTwo_abs_bound e b hVo hVK
      hv.continuous_closure hv2 hv.2.2.2.2 hv.2.2.1 hfc hf hfb hLf x hx
    have hwB : -w x ≤ max B 0 := by
      have hnorm : ‖w x‖ ≤ B := hB (w x) ⟨x,hx,rfl⟩
      have habs : |w x| ≤ B := by simpa only [Real.norm_eq_abs] using hnorm
      exact (neg_le_abs (w x)).trans (habs.trans (le_max_left _ _))
    have hvB : -v x ≤ max B 0 := (neg_le_neg (hle x hx)).trans hwB
    have hscale := mul_le_mul_of_nonneg_left hvB (div_nonneg hF (by norm_num : (0 : ℝ) ≤ 2))
    dsimp only [C]
    nlinarith

end PowerConvexity
