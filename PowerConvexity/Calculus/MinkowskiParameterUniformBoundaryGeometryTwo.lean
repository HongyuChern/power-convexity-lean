import PowerConvexity.Calculus.JointGlobalBoundaryLeviTwo
import PowerConvexity.Calculus.ParameterStripThirdDerivativeBounds
import PowerConvexity.Analysis.CompactMovingBoundaryBounds

/-! # Whole-boundary parameter-uniform actual defining-function geometry

One actual joint family has a common nonzero-gradient bound on every nearby
actual boundary and common spatial Hessian and third-derivative bounds on one
fixed ball containing those boundaries. All constants precede the parameter.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance mpubgRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance mpubgRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance mpubgDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance mpubgDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance mpubgDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance mpubgHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance mpubgHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance mpubgHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem classicalDirichlet_minkowski_exists_parameter_uniform_global_boundary_geometry_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 < R) :
    let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
    ∃ d > 0, ∃ F : ℝ × E → ℝ,
      ContDiffOn ℝ 4 F (ball s (2*d) ×ˢ (univ : Set E)) ∧
      ∃ R0 > 0, ∃ eta > 0, ∃ A > 0, ∃ L > 0, ∀ t ∈ closedBall s d,
        ContDiff ℝ 4 (fun x => F (t,x)) ∧
        (∀ x ∈ closedBall (0 : E) R0,
          ContDiffAt ℝ 3 (fun y => F (t,y)) x ∧
          ‖realHessian (fun y => F (t,y)) x‖ ≤ A ∧
          ‖fderiv ℝ (realHessian (fun y => F (t,y))) x‖ ≤ L) ∧
        (t ∈ Icc (0 : ℝ) 1 → (∀ x ∈ V t, F (t,x) ≤ 0) ∧
          ∀ x ∈ frontier (V t), ‖x‖ ≤ R0 ∧ F (t,x) = 0 ∧
            eta ≤ ‖fderiv ℝ (fun y => F (t,y)) x‖ ∧
            (∀ᶠ z in 𝓝 x, z ∈ V t ↔ F (t,z) < 0) ∧
            ∀ v : E, v ≠ 0 → fderiv ℝ (fun y => F (t,y)) x v = 0 →
              fderiv ℝ (fun y => F (t,y)) x (Complex.I • v) = 0 →
              0 < realHessian (fun y => F (t,y)) x v v +
                realHessian (fun y => F (t,y)) x (Complex.I • v) (Complex.I • v)) := by
  let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨delta,hdelta,F,hF,hFdata⟩ :=
    classicalDirichlet_minkowski_exists_joint_global_regular_Levi_defining_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet hs hs1 hR
  let K : Set (ℝ × E) := {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ frontier (V p.1)}
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hgraph : IsCompact K :=
    minkowskiDomain_real_frontier_parameterGraph_isCompact hU isOpen_ball hK hBK
  have hVK : IsCompact (closure (V s)) := by
    change IsCompact (closure (minkowskiDomain s U (ball (0 : E) R)))
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul s).add (hBK.smul (1-s))
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.le,hs1⟩
  have hKs : IsCompact {x : E | (s,x) ∈ K} := by
    have he : {x : E | (s,x) ∈ K} = frontier (V s) := by
      ext x
      simp only [K,mem_setOf_eq,hsI,true_and]
    rw [he]
    exact hVK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hC2 (x : E) : ContDiffAt ℝ 2 F (s,x) :=
    (hF.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
      ⟨mem_ball_self hdelta,mem_univ x⟩)).of_le (by norm_num)
  have hDcont (x : E) (_hx : (s,x) ∈ K) :
      ContinuousAt (fun q : ℝ × E => ‖fderiv ℝ (fun y => F (q.1,y)) q.2‖) (s,x) :=
    ContinuousAt.norm (f := fun q : ℝ × E => fderiv ℝ (fun y => F (q.1,y)) q.2)
      (parameter_fiber_fderiv_contDiffAt (n := 1) (hC2 x)).continuousAt
  have hDpos (x : E) (hx : (s,x) ∈ K) :
      0 < ‖fderiv ℝ (fun y => F (s,y)) x‖ :=
    norm_pos_iff.mpr ((hFdata s (mem_ball_self hdelta) hsI).2.2 x hx.2).2.1
  obtain ⟨eta,heta,hnear⟩ := compact_parameter_graph_uniform_positive_lower hgraph hKs hDcont hDpos
  obtain ⟨eps,heps,hepsN⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨B0,hB0⟩ := (hgraph.image continuous_snd).isBounded.exists_norm_le
  let R0 := |B0|+1
  have hR0 : 0 < R0 := by dsimp only [R0]; positivity
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : E) (hx : x ∈ frontier (V t)) :
      ‖x‖ ≤ R0 := (hB0 x (mem_image_of_mem Prod.snd (show (t,x) ∈ K from ⟨ht,hx⟩))).trans
        (by dsimp only [R0]; linarith [le_abs_self B0])
  obtain ⟨A,hA,L,hL,hcaps⟩ := exists_parameter_strip_uniform_third_derivative_bounds hdelta hF (0 : E) R0
  let d := min (delta/4) (eps/2)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hd1 : d ≤ delta/4 := min_le_left _ _
  have hd2 : d ≤ eps/2 := min_le_right _ _
  have htdelta {t : ℝ} (ht : t ∈ closedBall s d) : t ∈ ball s delta :=
    closedBall_subset_ball (by linarith : d < delta) ht
  have htcap {t : ℝ} (ht : t ∈ closedBall s d) : t ∈ closedBall s (delta/2) :=
    closedBall_subset_closedBall (by linarith : d ≤ delta/2) ht
  refine ⟨d,hd,F,hF.mono (Set.prod_mono (ball_subset_ball (by linarith : 2*d ≤ delta)) Subset.rfl),
    R0,hR0,eta,heta,A,hA,L,hL,?_⟩
  intro t ht
  have hFt : ContDiff ℝ 4 (fun x => F (t,x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hF.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
      ⟨htdelta ht,mem_univ x⟩)).comp x (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨hFt,hcaps t (htcap ht),?_⟩
  intro hI
  have hactual := hFdata t (htdelta ht) hI
  refine ⟨hactual.2.1,?_⟩
  intro x hx
  have hxdata := hactual.2.2 x hx
  exact ⟨hbound t hI x hx,hxdata.1,
    hepsN (closedBall_subset_ball (by linarith : d < eps) ht) x ⟨hI,hx⟩,
    hxdata.2.2.1,hxdata.2.2.2⟩

end
end PowerConvexity
