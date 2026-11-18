import PowerConvexity.Calculus.ParameterPshOpenTwo
import PowerConvexity.Calculus.GermPreservingStrictPshExtensionTwo
import PowerConvexity.Analysis.CompactMovingBoundaryBounds

/-! # Extend a joint boundary family using one base global strict psh extension

The actual family is g(x)+rho(t,x)-rho(s,x). At the base parameter it equals
the global strict psh function g. On one fixed open neighborhood of the base
boundary, g and rho(s,.) agree as actual functions. Compactness of the moving
boundary graph preserves that agreement at all nearby actual boundaries.
Compactness of the actual closure graph preserves strict psh in the whole
nearby closure. No boundary-value PDE solution is used.
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

theorem joint_strictPsh_extension_from_base_germs_two
    (e : Module.Basis (Fin 2) ℂ E) {V : ℝ → Set E} {s delta : ℝ}
    (hdelta : 0 < delta)
    (hclosure : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)})
    (hfrontier : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)})
    {rho : ℝ × E → ℝ} (hrho : ContDiffOn ℝ 4 rho (ball s delta ×ˢ (univ : Set E)))
    {g : E → ℝ} (hg : ContDiff ℝ 4 g)
    (hgerm : ∀ x ∈ frontier (V s), g =ᶠ[𝓝 x] (fun y => rho (s,y)))
    (hgp : ∀ x ∈ closure (V s), (complexHessian e (fun j => Complex.I • e j) g x).PosDef) :
    ∃ d > 0, ∃ F : ℝ × E → ℝ,
      ContDiffOn ℝ 4 F (ball s (2*d) ×ˢ (univ : Set E)) ∧
      ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
        ContDiff ℝ 4 (fun x => F (t,x)) ∧
        (∀ x ∈ frontier (V t), (fun y => F (t,y)) =ᶠ[𝓝 x] (fun y => rho (t,y))) ∧
        ∀ x ∈ closure (V t),
          (complexHessian e (fun j => Complex.I • e j) (fun y => F (t,y)) x).PosDef := by
  have hrhobase : ContDiff ℝ 4 (fun x => rho (s,x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hrho.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
      ⟨mem_ball_self hdelta,mem_univ x⟩)).comp x (contDiffAt_const.prodMk contDiffAt_id)
  let F : ℝ × E → ℝ := fun q => g q.2+rho q-rho (s,q.2)
  have hF : ContDiffOn ℝ 4 F (ball s delta ×ˢ (univ : Set E)) :=
    ((hg.comp contDiff_snd).contDiffOn.add hrho).sub ((hrhobase.comp contDiff_snd).contDiffOn)
  have hFbase : (fun y => F (s,y)) = g := by
    funext y
    exact add_sub_cancel_right (g y) (rho (s,y))
  let W : Set E := {x | g =ᶠ[𝓝 x] (fun y => rho (s,y))}
  have hWo : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact hx.eventually_nhds
  have hnearGerm : ∀ᶠ t in 𝓝 s, ∀ x : E,
      t ∈ Icc (0 : ℝ) 1 ∧ x ∈ frontier (V t) → x ∈ W :=
    compact_parameter_graph_eventually_subset_open hfrontier hWo (fun x hx => hgerm x hx.2)
  have hnearPsh : ∀ᶠ t in 𝓝 s, ∀ x : E,
      t ∈ Icc (0 : ℝ) 1 ∧ x ∈ closure (V t) →
      (complexHessian e (fun j => Complex.I • e j) (fun y => F (t,y)) x).PosDef := by
    apply compact_parameter_graph_eventually_of_joint_local_property hclosure (s := s)
      (Q := fun q => (complexHessian e (fun j => Complex.I • e j) (fun y => F (q.1,y)) q.2).PosDef)
    intro x hx
    apply parameter_complexHessian_posDef_eventually_of_joint_C2_two e
      ((hF.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
        ⟨mem_ball_self hdelta,mem_univ x⟩)).of_le (by norm_num))
    rw [hFbase]
    exact hgp x hx.2
  obtain ⟨eps,heps,hepsN⟩ := Metric.mem_nhds_iff.mp (hnearGerm.and hnearPsh)
  let d := min (delta/4) (eps/2)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hd1 : d ≤ delta/4 := min_le_left _ _
  have hd2 : d ≤ eps/2 := min_le_right _ _
  refine ⟨d,hd,F,hF.mono (Set.prod_mono (ball_subset_ball (by linarith : 2*d ≤ delta)) Subset.rfl),?_⟩
  intro t ht hI
  have htd : t ∈ ball s delta := closedBall_subset_ball (by linarith : d < delta) ht
  have hte : t ∈ ball s eps := closedBall_subset_ball (by linarith : d < eps) ht
  have hFt : ContDiff ℝ 4 (fun x => F (t,x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hF.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨htd,mem_univ x⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨hFt,?_,fun x hx => (hepsN hte).2 x ⟨hI,hx⟩⟩
  intro x hx
  have hxeq : g =ᶠ[𝓝 x] (fun y => rho (s,y)) := (hepsN hte).1 x ⟨hI,hx⟩
  filter_upwards [hxeq] with y hy
  change g y+rho (t,y)-rho (s,y) = rho (t,y)
  rw [hy]
  ring

end PowerConvexity
