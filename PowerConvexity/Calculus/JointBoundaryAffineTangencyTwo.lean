import PowerConvexity.Calculus.ParameterStripThirdDerivativeBounds
import PowerConvexity.Calculus.ParameterAffineTangencyTwo

/-! # Quantitative defining geometry and affine fields before the parameter -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Metric Matrix
open scoped ContDiff Topology
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance jbatRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance jbatRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance jbatDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance jbatDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance jbatDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance jbatHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance jbatHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance jbatHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem joint_regular_defining_uniform_geometry_two
    {V : ℝ → Set E} {s d : ℝ} (hd : 0 < d)
    (hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)})
    {F : ℝ × E → ℝ} (hF : ContDiffOn ℝ 4 F (ball s (2*d) ×ˢ (univ : Set E)))
    (hreg : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ frontier (V t),
      fderiv ℝ (fun y => F (t,y)) x ≠ 0) :
    ∃ R > 0, ∃ eta > 0, ∃ D > 0, ∃ A > 0, ∃ L > 0,
      ∀ t ∈ closedBall s d,
        ContDiff ℝ 3 (fun y => F (t,y)) ∧
        (∀ x ∈ closedBall (0 : E) R,
          ‖realHessian (fun y => F (t,y)) x‖ ≤ A ∧
          ‖fderiv ℝ (realHessian (fun y => F (t,y))) x‖ ≤ L) ∧
        (t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ frontier (V t),
          ‖x‖ ≤ R ∧ eta ≤ ‖fderiv ℝ (fun y => F (t,y)) x‖ ∧
          ‖fderiv ℝ (fun y => F (t,y)) x‖ ≤ D) := by
  let K : Set (ℝ × E) :=
    {q | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)} ∩ Prod.fst ⁻¹' closedBall s d
  have hK : IsCompact K := hgraph.inter_right (isClosed_closedBall.preimage continuous_fst)
  have hC3 (t : ℝ) (ht : t ∈ closedBall s d) (x : E) : ContDiffAt ℝ 3 F (t,x) :=
    (hF.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
      ⟨closedBall_subset_ball (by linarith : d < 2*d) ht,mem_univ x⟩)).of_le (by norm_num)
  let DF : ℝ × E → (E →L[ℝ] ℝ) := fun q => fderiv ℝ (fun y => F (q.1,y)) q.2
  have hDc : ContinuousOn DF K := fun q hq =>
    (parameter_fiber_fderiv_contDiffAt (n := 2) (hC3 q.1 hq.2 q.2)).continuousAt.continuousWithinAt
  have hDn : ContinuousOn (fun q => ‖DF q‖) K := hDc.norm
  have hpos (q : ℝ × E) (hq : q ∈ K) : 0 < ‖DF q‖ :=
    norm_pos_iff.mpr (hreg q.1 hq.2 hq.1.1 q.2 hq.1.2)
  obtain ⟨eta,heta,hetaK⟩ := hK.exists_forall_le' hDn hpos
  obtain ⟨D0,hD0⟩ := (hK.image_of_continuousOn hDc).isBounded.exists_norm_le
  obtain ⟨R0,hR0⟩ := (hgraph.image continuous_snd).isBounded.exists_norm_le
  let R : ℝ := |R0|+1
  let D : ℝ := |D0|+1
  obtain ⟨A,hA,L,hL,hcaps⟩ := exists_parameter_strip_uniform_third_derivative_bounds
    (by positivity : 0 < 2*d) hF (0 : E) R
  refine ⟨R,by dsimp [R]; positivity,eta,heta,D,by dsimp [D]; positivity,A,hA,L,hL,?_⟩
  intro t ht
  have htcap : t ∈ closedBall s ((2*d)/2) := by simpa only [mul_div_cancel_left₀ d (by norm_num : (2 : ℝ) ≠ 0)] using ht
  refine ⟨?_,fun x hx => (hcaps t htcap x hx).2,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    exact (hC3 t ht x).comp x (contDiffAt_const.prodMk contDiffAt_id)
  · intro hI x hx
    have hq : (t,x) ∈ K := ⟨⟨hI,hx⟩,ht⟩
    refine ⟨?_,hetaK (t,x) hq,?_⟩
    · exact (hR0 x (mem_image_of_mem Prod.snd (show (t,x) ∈
        {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)} from ⟨hI,hx⟩))).trans
        (by dsimp [R]; linarith [le_abs_self R0])
    · exact (hD0 _ (mem_image_of_mem DF hq)).trans (by dsimp [D]; linarith [le_abs_self D0])

theorem joint_regular_defining_uniform_affine_tangency_two
    (e : Module.Basis (Fin 2) ℂ E) {V : ℝ → Set E} {s d : ℝ} (hd : 0 < d)
    (hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)})
    {F : ℝ × E → ℝ} (hF : ContDiffOn ℝ 4 F (ball s (2*d) ×ˢ (univ : Set E)))
    (hbd : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ frontier (V t),
      F (t,x) = 0 ∧ fderiv ℝ (fun y => F (t,y)) x ≠ 0) :
    ∃ eta > 0, ∃ D > 0, ∃ C > 0, ∃ M ≥ 0,
      ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
        ContDiff ℝ 3 (fun y => F (t,y)) ∧
        (∀ x ∈ frontier (V t), eta ≤ ‖fderiv ℝ (fun y => F (t,y)) x‖ ∧
          ‖fderiv ℝ (fun y => F (t,y)) x‖ ≤ D) ∧
        ∀ x ∈ frontier (V t), ∀ tau : E, ‖tau‖ ≤ 1 →
          fderiv ℝ (fun y => F (t,y)) x tau = 0 →
          ∃ (K : E →L[ℂ] E) (c : E),
            (complexFieldMatrixTwo e K).trace.re = 0 ∧ c+K x = tau ∧ ‖K‖ ≤ M ∧
            ∀ y ∈ frontier (V t),
              |fderiv ℝ (fun z => F (t,z)) y (c+K y)| ≤ C*‖y-x‖^2 := by
  obtain ⟨R,hR,eta,heta,D,hD,A,hA,L,hL,hgeo⟩ := joint_regular_defining_uniform_geometry_two
    hd hgraph hF (fun t ht hI x hx => (hbd t ht hI x hx).2)
  let T := {t : ℝ // t ∈ closedBall s d}
  let f : T → E → ℝ := fun t x => F (t.1,x)
  obtain ⟨C,hC,hfields⟩ := affine_complex_tangency_uniform_family_two f e hR.le heta hA.le hL.le
    (fun t x _ => (hgeo t.1 t.2).1.contDiffAt)
    (fun t x hx => ((hgeo t.1 t.2).2.1 x hx).1)
    (fun t x hx => ((hgeo t.1 t.2).2.1 x hx).2)
  refine ⟨eta,heta,D,hD,C,hC,2*A/eta,by positivity,?_⟩
  intro t ht hI
  have hgd := hgeo t ht
  refine ⟨hgd.1,fun x hx => (hgd.2.2 hI x hx).2,?_⟩
  intro x hx tau htau htangent
  have hxb : x ∈ closedBall (0 : E) R := by
    simpa only [mem_closedBall,dist_zero_right] using (hgd.2.2 hI x hx).1
  obtain ⟨K,c,htrace,hcx,hKn,hq⟩ := hfields ⟨t,ht⟩ x hxb
    ((hgd.2.2 hI x hx).2.1) (hbd t ht hI x hx).1 tau htau htangent
  refine ⟨K,c,htrace,hcx,hKn,?_⟩
  intro y hy
  apply hq y
  · simpa only [mem_closedBall,dist_zero_right] using (hgd.2.2 hI y hy).1
  · exact (hbd t ht hI y hy).1

end
end PowerConvexity
