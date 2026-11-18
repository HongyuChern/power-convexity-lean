import PowerConvexity.Calculus.StrongDefiningJointGlobalSideTwo
import PowerConvexity.Analysis.ActualCompactParameterBoundaryGeometryFour
import PowerConvexity.Analysis.MinkowskiDomainGeometry
import PowerConvexity.Analysis.MinkowskiHomotheticTrapping

/-! # Actual common boundary geometry for all strong Minkowski fibers

The genuine joint defining families are pulled back by one actual real
isometry. Compactness of the moving closure and boundary graphs, actual
joint domain-side identifications, and common inner/outer balls construct
the quantitative geometry for the entire closed parameter interval.
No solution or boundary modulus is assumed in this geometric construction.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "V₀" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem actual_isometric_real_parameter_graph_isCompact_two
    (L : V₀ ≃ₗᵢ[ℝ] E) {A : ℝ → Set E}
    (hA : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ A q.1}) :
    IsCompact {q : ℝ × V₀ | q.1 ∈ Icc (0 : ℝ) 1 ∧ L q.2 ∈ A q.1} := by
  let Phi : ℝ × E → ℝ × V₀ := fun q => (q.1,L.symm q.2)
  have hPhi : Continuous Phi := continuous_fst.prodMk (L.symm.continuous.comp continuous_snd)
  have he : Phi '' {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ A q.1}=
      {q : ℝ × V₀ | q.1 ∈ Icc (0 : ℝ) 1 ∧ L q.2 ∈ A q.1} := by
    ext q
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨hp.1,by simpa only [Phi,L.apply_symm_apply] using hp.2⟩
    · intro hq
      exact ⟨(q.1,L q.2),hq,by simp only [Phi,L.symm_apply_apply,Prod.mk.eta]⟩
  rw [← he]
  exact hA.image hPhi

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]

theorem strong_defining_minkowski_actual_common_frame_geometry_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hH : ∀ x ∈ frontier U, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian f x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (L : V₀ ≃ₗᵢ[ℝ] E)
    {R rho0 Dout : ℝ} (hR : 0 < R) (hrho0 : 0 < rho0)
    (hballU : closedBall (0 : E) rho0 ⊆ U)
    (hballB : closedBall (0 : E) rho0 ⊆ ball (0 : E) R)
    (hUb : ∀ x ∈ U, ‖x‖ ≤ Dout) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ Dout) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ Hchart > 0, ∃ F > 0, ∃ margin > 0,
      ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F margin rho0 Dout,
        Geo.domain=L ⁻¹' minkowskiDomain t U (ball (0 : E) R) := by
  let V : ℝ → Set E := fun t => minkowskiDomain t U (ball (0 : E) R)
  let W : ℝ → Set V₀ := fun t => L ⁻¹' V t
  have hUn : U.Nonempty := ⟨0,hballU (mem_closedBall_self hrho0.le)⟩
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hcl (t : ℝ) : closure (W t)=L ⁻¹' closure (V t) :=
    (L.toHomeomorph.preimage_closure (V t)).symm
  have hfr (t : ℝ) : frontier (W t)=L ⁻¹' frontier (V t) :=
    (L.toHomeomorph.preimage_frontier (V t)).symm
  have hgeometry (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      IsOpen (W t) ∧ Convex ℝ (W t) ∧ IsCompact (closure (W t)) := by
    have hVo : IsOpen (V t) :=
      (minkowskiDomain_real_parameterGraph_isOpen hU isOpen_ball).preimage
        (continuous_const.prodMk continuous_id)
    have hVK : IsCompact (closure (V t)) := minkowskiDomain_isCompact_closure hUb hBb ht.1 ht.2
    refine ⟨hVo.preimage L.continuous,
      (minkowskiDomain_convex hconv (convex_ball (0 : E) R) t).linear_preimage L.toLinearMap,?_⟩
    rw [hcl]
    exact (L.toHomeomorph.isCompact_preimage).mpr hVK
  have hclosure : IsCompact {q : ℝ × V₀ | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (W q.1)} := by
    have hh := actual_isometric_real_parameter_graph_isCompact_two L
      (A := fun t => closure (V t))
      (minkowskiDomain_real_closure_parameterGraph_isCompact hK hBK)
    simpa only [hcl,mem_preimage] using hh
  have hfrontier : IsCompact {q : ℝ × V₀ | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (W q.1)} := by
    have hh := actual_isometric_real_parameter_graph_isCompact_two L
      (A := fun t => frontier (V t))
      (minkowskiDomain_real_frontier_parameterGraph_isCompact hU isOpen_ball hK hBK)
    simpa only [hfr,mem_preimage] using hh
  have hinner (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) : closedBall (0 : V₀) rho0 ⊆ W t := by
    intro x hx
    have hxL : L x ∈ closedBall (0 : E) rho0 := by
      simpa only [mem_closedBall,dist_zero_right,L.norm_map] using hx
    exact minkowskiDomain_contains_inter t U (ball (0 : E) R) ⟨hballU hxL,hballB hxL⟩
  have houter (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : V₀) (hx : x ∈ closure (W t)) : ‖x‖ ≤ Dout := by
    have hbound : ∀ y ∈ closure (V t), ‖y‖ ≤ Dout := le_on_closure
      (fun y hy => minkowskiDomain_norm_le hUb hBb ht.1 ht.2 hy)
      continuous_norm.continuousOn continuousOn_const
    have hh := hbound (L x) (by rwa [hcl] at hx)
    simpa only [L.norm_map] using hh
  apply actual_compact_joint_common_boundary_geometry_four hgeometry hclosure hfrontier hinner houter
  intro s hs
  obtain ⟨d0,hd0,F,hF,hFdata⟩ := strong_defining_minkowski_exists_joint_global_defining_side_two
    hU hconv hK hUn hf hb hdelta hH e hab hs.1 hs.2 hR
  let d := d0/4
  have hd : 0 < d := by dsimp only [d]; positivity
  let fL : ℝ × V₀ → ℝ := fun q => F (q.1,L q.2)
  have hparam : ContDiff ℝ 4 (fun q : ℝ × V₀ => (q.1,L q.2)) :=
    contDiff_fst.prodMk (L.contDiff.comp contDiff_snd)
  have hfL : ContDiffOn ℝ 4 fL (ball s (2*d) ×ˢ (univ : Set V₀)) :=
    hF.comp hparam.contDiffOn (fun q hq =>
      ⟨ball_subset_ball (by dsimp only [d]; linarith : 2*d ≤ d0) hq.1,mem_univ _⟩)
  refine ⟨d,hd,fL,hfL,?_⟩
  intro t ht hI x hx
  have htd0 : t ∈ ball s d0 := closedBall_subset_ball (by dsimp only [d]; linarith : d < d0) ht
  have hxL : L x ∈ frontier (V t) := by rwa [hfr] at hx
  have hdata := hFdata t htd0 hI
  have hbd := hdata.2.2 (L x) hxL
  have hfd : fderiv ℝ (fun y : V₀ => F (t,L y)) x=
      (fderiv ℝ (fun y : E => F (t,y)) (L x)).comp L.toContinuousLinearMap :=
    ((hdata.1.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  refine ⟨hbd.1,?_,?_⟩
  · intro hz
    change fderiv ℝ (fun y : V₀ => F (t,L y)) x=0 at hz
    rw [hfd] at hz
    apply hbd.2.1
    ext v
    change fderiv ℝ (fun y : E => F (t,y)) (L x) v = 0
    have hh := congrArg (fun D : V₀ →L[ℝ] ℝ => D (L.symm v)) hz
    change fderiv ℝ (fun y : E => F (t,y)) (L x) (L (L.symm v))=0 at hh
    simpa only [L.apply_symm_apply] using hh
  · have hmap : Tendsto (fun q : ℝ × V₀ => (q.1,L q.2)) (𝓝 (t,x)) (𝓝 (t,L x)) :=
      hparam.continuous.continuousAt.tendsto
    filter_upwards [hmap.eventually hbd.2.2.2.2] with q hq
    exact fun hqI => hq hqI

end PowerConvexity
