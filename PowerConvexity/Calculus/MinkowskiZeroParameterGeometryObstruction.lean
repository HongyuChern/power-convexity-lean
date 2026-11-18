import PowerConvexity.Calculus.BallRegularBoundaryHessian
import PowerConvexity.Calculus.ParallelPrincipalCurvature
import PowerConvexity.Calculus.ParameterFiberDerivative

/-! # A real flat tangent obstructs a joint C2 regular defining family at zero

The null direction is transported on the actual positive-parameter boundaries.
Joint Hessian continuity would make it null on the limiting actual sphere,
which is impossible for a regular function vanishing on that sphere.
This rules out this geometry route, not the desired PDE estimate at zero.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem no_joint_C2_regular_minkowski_defining_family_at_zero_of_flat_tangent
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {v : E} (hv : v ≠ 0) (htan : fderiv ℝ f x v = 0)
    (hflat : realHessian f x v v = 0)
    {R delta : ℝ} (hR : 0 < R) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {F : ℝ × E → ℝ}
    (hF : ContDiffOn ℝ 2 F (ball 0 (2*delta) ×ˢ (univ : Set E)))
    (hregular : ∀ t ∈ Icc (0 : ℝ) delta,
      ∀ z ∈ frontier (minkowskiDomain t U (ball (0 : E) R)),
        F (t,z) = 0 ∧ fderiv ℝ (fun y => F (t,y)) z ≠ 0 ∧
        (∀ᶠ y in 𝓝 z, y ∈ minkowskiDomain t U (ball (0 : E) R) ↔ F (t,y) < 0)) :
    False := by
  let y : ℝ → E := fun t => definingParallelMap f t ((1-t)*R) x
  have hy0 : y 0 = R • definingUnitNormal f x := by simp only [y,definingParallelMap,zero_smul,sub_zero,one_mul,zero_add]
  have hUne : U.Nonempty := (show (closure U).Nonempty from ⟨x,frontier_subset_closure hx⟩).of_closure
  have hV0 : minkowskiDomain (0 : ℝ) U (ball (0 : E) R) = ball (0 : E) R := minkowskiDomain_zero hUne
  have hnorm : ‖y 0‖ = R := by
    rw [hy0,norm_smul,Real.norm_eq_abs,abs_of_pos hR,definingUnitNormal_norm hDf,mul_one]
  have hyfront : y 0 ∈ frontier (minkowskiDomain (0 : ℝ) U (ball (0 : E) R)) := by
    rw [hV0,frontier_ball (0 : E) hR.ne']
    simpa only [mem_sphere,dist_zero_right] using hnorm
  have hFq (t : ℝ) (ht : 0 ≤ t) (htd : t ≤ delta) (z : E) : ContDiffAt ℝ 2 F (t,z) := by
    have htb : t ∈ closedBall (0 : ℝ) delta := by
      simpa only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg ht] using htd
    exact hF.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
      ⟨closedBall_subset_ball (by linarith : delta < 2*delta) htb,mem_univ z⟩)
  have hFt (t : ℝ) (ht : 0 ≤ t) (htd : t ≤ delta) (z : E) :
      ContDiffAt ℝ 2 (fun a => F (t,a)) z :=
    (hFq t ht htd z).comp z (contDiffAt_const.prodMk contDiffAt_id)
  let H : ℝ → ℝ := fun t => realHessian (fun a => F (t,a)) (y t) v v
  have hzero (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) delta) : H t = 0 := by
    have ht1 : t ≤ 1 := ht.2.trans hdelta1
    have hyt : y t ∈ frontier (minkowskiDomain t U (ball (0 : E) R)) :=
      definingParallelMap_mem_minkowski_frontier hU hconv hx hf hfx hDf hdef ht.1 ht1 hR
    have hg := hFt t ht.1.le ht.2 (y t)
    have hgd := hregular t ⟨ht.1.le,ht.2⟩ (y t) hyt
    have htv := (parallel_defining_tangent_kernel_iff hU hconv hx hf hfx hDf hdef
      ht.1.le ht1 hg hgd.1 hgd.2.1 hgd.2.2 v).mpr htan
    exact (parallel_defining_tangent_null_iff hU hconv hx hf hfx hDf hdef
      ht.1 ht1 hR hg hgd.1 hgd.2.1 hgd.2.2 htv).mpr hflat
  have hD : ContDiffAt ℝ 1
      (fun q : ℝ × E => fderiv ℝ (fun a => F (q.1,a)) q.2) (0,y 0) :=
    parameter_fiber_fderiv_contDiffAt (n := 1) (hFq 0 le_rfl hdelta.le (y 0))
  have hHc : ContinuousAt
      (fun q : ℝ × E => realHessian (fun a => F (q.1,a)) q.2) (0,y 0) :=
    (parameter_fiber_fderiv_contDiffAt (n := 0) hD).continuousAt
  have hHv : ContinuousAt
      (fun q : ℝ × E => realHessian (fun a => F (q.1,a)) q.2 v v) (0,y 0) :=
    (hHc.clm_apply continuousAt_const).clm_apply continuousAt_const
  have hcurve : ContinuousAt (fun t : ℝ => (t,y t)) 0 := by
    dsimp only [y,definingParallelMap]
    fun_prop
  have hHcont : ContinuousAt H 0 :=
    ContinuousAt.comp (f := fun t : ℝ => (t,y t))
      (g := fun q : ℝ × E => realHessian (fun a => F (q.1,a)) q.2 v v) hHv hcurve
  have hcl : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) delta) := by
    rw [closure_Ioc hdelta.ne]
    exact ⟨le_rfl,hdelta.le⟩
  haveI : NeBot (𝓝[Ioc (0 : ℝ) delta] (0 : ℝ)) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hmem : ∀ᶠ t : ℝ in 𝓝[Ioc (0 : ℝ) delta] (0 : ℝ), t ∈ Ioc (0 : ℝ) delta :=
    self_mem_nhdsWithin
  have he : H =ᶠ[𝓝[Ioc (0 : ℝ) delta] (0 : ℝ)] (fun _ => 0) :=
    hmem.mono (fun t ht => hzero t ht)
  have hlim : Tendsto H (𝓝[Ioc (0 : ℝ) delta] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.congr' he.symm
  have htend : Tendsto H (𝓝[Ioc (0 : ℝ) delta] (0 : ℝ)) (𝓝 (H 0)) :=
    hHcont.continuousWithinAt.tendsto
  have hzero0 : H 0 = 0 := tendsto_nhds_unique htend hlim
  have htan0 : inner ℝ (y 0) v = 0 := by
    simp only [hy0,definingUnitNormal,real_inner_smul_left,inner_gradient_left,htan,mul_zero]
  have hD0 := (hregular 0 ⟨le_rfl,hdelta.le⟩ (y 0) hyfront).2.1
  have hgb : ∀ z ∈ frontier (ball (0 : E) R), F (0,z) = 0 := by
    intro z hz
    exact (hregular 0 ⟨le_rfl,hdelta.le⟩ z (by simpa only [hV0] using hz)).1
  exact ball_regular_zero_boundary_tangent_hessian_ne_zero hR hnorm hv htan0
    (hFt 0 le_rfl hdelta.le (y 0)) hD0 hgb hzero0

end PowerConvexity
