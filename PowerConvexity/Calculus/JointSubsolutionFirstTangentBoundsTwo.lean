import PowerConvexity.Calculus.StrictSubsolutionClosureGradientBoundTwo
import PowerConvexity.Calculus.ParameterFiberDerivative

/-! # One C1 and tangential C2 bound before the parameter and unknown solution

All constants are extracted from the actual joint subsolution on the compact
moving-closure graph. Actual comparison and directional derivative maximum
principles transfer them to every classical det=1 solution in every fiber.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance jftDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance jftDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance jftDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance jftHessAddGroup : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toAddCommGroup
local instance jftHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance jftHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance jftHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem joint_strict_subsolution_uniform_first_tangent_bounds_two
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {V : ℝ → Set E} {s d : ℝ} (hd : 0 < d)
    (hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)})
    (hgeometry : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      IsOpen (V t) ∧ Convex ℝ (V t) ∧ IsCompact (closure (V t)) ∧ HasC2LocalDefiningFunction (V t))
    {w : ℝ × E → ℝ} (hw : ContDiffOn ℝ 4 w (ball s (2*d) ×ˢ (univ : Set E)))
    (hdata : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      (∀ x ∈ frontier (V t), w (t,x) = 0) ∧
      ∀ x ∈ V t, (complexHessian a b (fun y => w (t,y)) x).PosDef ∧
        (1 : ℂ) < (complexHessian a b (fun y => w (t,y)) x).det) :
    ∃ C ≥ 0, ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      ∀ (u : E → ℝ) (J : ClosureC2Jet u (V t)), ContDiffOn ℝ 3 u (V t) →
        (∀ x ∈ frontier (V t), u x = 0) →
        (∀ x ∈ V t, (complexHessian a b u x).PosDef) →
        (∀ x ∈ V t, (complexHessian a b u x).det = 1) →
        (∀ x ∈ closure (V t), ‖J.derivative x‖ ≤ C) ∧
        ∀ x ∈ frontier (V t), ∀ v : E,
          J.derivative x v = 0 → J.hessian x v v ≤ C*‖v‖^2 := by
  let K : Set (ℝ × E) :=
    {q | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)} ∩ Prod.fst ⁻¹' closedBall s d
  have hK : IsCompact K := hgraph.inter_right (isClosed_closedBall.preimage continuous_fst)
  have hC2 (q : ℝ × E) (hq : q ∈ K) : ContDiffAt ℝ 2 w q :=
    (hw.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
      ⟨closedBall_subset_ball (by linarith : d < 2*d) hq.2,mem_univ q.2⟩)).of_le (by norm_num)
  have hD (q : ℝ × E) (hq : q ∈ K) : ContDiffAt ℝ 1
      (fun p : ℝ × E => fderiv ℝ (fun y => w (p.1,y)) p.2) q :=
    parameter_fiber_fderiv_contDiffAt (n := 1) (hC2 q hq)
  have hDc : ContinuousOn (fun p : ℝ × E => fderiv ℝ (fun y => w (p.1,y)) p.2) K :=
    fun q hq => (hD q hq).continuousAt.continuousWithinAt
  have hHc : ContinuousOn (fun p : ℝ × E => realHessian (fun y => w (p.1,y)) p.2) K :=
    fun q hq => (parameter_fiber_fderiv_contDiffAt (n := 0) (hD q hq)).continuousAt.continuousWithinAt
  obtain ⟨A,hA0⟩ := (hK.image_of_continuousOn hDc).isBounded.exists_norm_le
  obtain ⟨B,hB0⟩ := (hK.image_of_continuousOn hHc).isBounded.exists_norm_le
  have hA (q : ℝ × E) (hq : q ∈ K) : ‖fderiv ℝ (fun y => w (q.1,y)) q.2‖ ≤ A :=
    hA0 _ (mem_image_of_mem _ hq)
  have hB (q : ℝ × E) (hq : q ∈ K) : ‖realHessian (fun y => w (q.1,y)) q.2‖ ≤ B :=
    hB0 _ (mem_image_of_mem _ hq)
  let C := max 0 (max A B)
  have hC : 0 ≤ C := le_max_left _ _
  have hAC : A ≤ C := (le_max_left A B).trans (le_max_right 0 (max A B))
  have hBC : B ≤ C := (le_max_right A B).trans (le_max_right 0 (max A B))
  refine ⟨C,hC,?_⟩
  intro t ht hI u J hu hub hup hud
  obtain ⟨hVo,hconv,hVK,hboundary⟩ := hgeometry t ht hI
  have hw2 : ContDiff ℝ 2 (fun x => w (t,x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have hwq : ContDiffAt ℝ 2 w (t,x) :=
      (hw.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
        ⟨closedBall_subset_ball (by linarith : d < 2*d) ht,mem_univ x⟩)).of_le (by norm_num)
    exact hwq.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hwb := (hdata t ht hI).1
  have hwp (x : E) (hx : x ∈ V t) := ((hdata t ht hI).2 x hx).1
  have hwd (x : E) (hx : x ∈ V t) := ((hdata t ht hI).2 x hx).2
  have hu2 : ContDiffOn ℝ 2 u (V t) := hu.of_le (by norm_num)
  have hbound (x : E) (hx : x ∈ frontier (V t)) : ‖J.derivative x‖ ≤ C ∧
      ∀ v : E, J.derivative x v = 0 → J.hessian x v v ≤ C*‖v‖^2 := by
    obtain ⟨f,hf,hfx,hDf,hdef⟩ := hboundary x hx
    have hq : (t,x) ∈ K := ⟨⟨hI,frontier_subset_closure hx⟩,ht⟩
    refine ⟨(strict_subsolution_boundary_derivative_norm_le_two hVo hconv hVK a b hab hw2 hu2 J
      hwb hub hwp hwd hup hud hx hf hfx hDf hdef).trans ((hA (t,x) hq).trans hAC),?_⟩
    intro v hv
    obtain ⟨lam,hlam,hJ⟩ := classicalDirichlet_derivative_eq_positive_defining_multiple_two
      hVo hconv hVK hu2 J hub a b hab hup hud hx hf hfx hDf hdef
    have hfv : fderiv ℝ f x v = 0 := by
      rw [hJ] at hv
      simp only [ContinuousLinearMap.smul_apply,smul_eq_mul] at hv
      exact (mul_eq_zero.mp hv).resolve_left hlam.ne'
    have hupper := strict_subsolution_boundary_tangent_hessian_le_two
      hVo hconv hVK a b hab hw2 hu2 J hwb hub hwp hwd hup hud hx hf hfx hDf hdef v hfv
    apply hupper.trans
    have hEval : realHessian (fun y => w (t,y)) x v v ≤
        ‖realHessian (fun y => w (t,y)) x‖*‖v‖^2 := by
      have hh := (le_abs_self (realHessian (fun y => w (t,y)) x v v)).trans
        (by simpa only [Real.norm_eq_abs] using (realHessian (fun y => w (t,y)) x).le_opNorm₂ v v)
      simpa only [pow_two,mul_assoc] using hh
    exact hEval.trans (mul_le_mul_of_nonneg_right ((hB (t,x) hq).trans hBC) (sq_nonneg _))
  exact ⟨closure_derivative_norm_le_boundary_bound hVo hVK hu J hub a b hup hud hC
    (fun x hx => (hbound x hx).1),fun x hx => (hbound x hx).2⟩

end
end PowerConvexity
