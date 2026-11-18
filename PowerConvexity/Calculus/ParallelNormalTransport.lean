import PowerConvexity.Calculus.MinkowskiSmoothBoundary
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Actual normal derivatives along parallel convex boundaries

All normals are normalized actual gradients. The tangent derivative identity
is proved by differentiating equality on a genuine boundary chart.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem symmetric_bilinear_null_on_kernel
    (H : E →L[ℝ] E →L[ℝ] ℝ) (l : E →L[ℝ] ℝ)
    (hsym : ∀ v w, H v w = H w v)
    (hpos : ∀ v, l v = 0 → 0 ≤ H v v)
    {u v : E} (hu : l u = 0) (hv : l v = 0) (hzero : H u u = 0) : H u v = 0 := by
  let p : ℝ → E := fun s => u+s • v
  have hp0 : p 0 = u := by simp [p]
  have hpd : HasDerivAt p v 0 := by
    simpa only [p,id_eq,one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have hmin : IsLocalMin (fun s => H (p s) (p s)) 0 := by
    apply Filter.Eventually.of_forall
    intro s
    have hps : l (p s) = 0 := by simp [p,map_add,map_smul,hu,hv]
    simpa only [hp0,hzero] using hpos (p s) hps
  have hd := (H.hasFDerivAt.comp_hasDerivAt 0 hpd).clm_apply hpd
  have hz := hmin.hasDerivAt_eq_zero hd
  simp only [Function.comp_def,hp0,hsym v u] at hz
  linarith

theorem convex_defining_normal_derivative_zero_of_tangent_null
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {v : E} (hv : fderiv ℝ f x v = 0) (hnull : realHessian f x v v = 0) :
    fderiv ℝ (definingUnitNormal f) x v = 0 := by
  have hw : fderiv ℝ f x (fderiv ℝ (definingUnitNormal f) x v) = 0 := by
    rw [← inner_gradient_left]
    exact definingUnitNormal_fderiv_normal_orthogonal hf hDf v
  have hcross := symmetric_bilinear_null_on_kernel (realHessian f x) (fderiv ℝ f x)
    (realHessian_symm hf)
    (definingFunction_tangent_hessian_nonneg_of_convex hU hconv hx hf hfx hDf hdef) hv hw hnull
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [definingUnitNormal_fderiv_tangent_pair hf hDf v _ hw,hcross,zero_div]

theorem definingFunction_zero_of_frontier
    {V : Set E} (hV : IsOpen V) {g : E → ℝ} {y : E}
    (hy : y ∈ frontier V) (hg : ContinuousAt g y)
    (hdef : ∀ᶠ z in 𝓝 y, z ∈ V ↔ g z < 0) : g y = 0 := by
  have hyn : y ∉ V := by rw [hV.frontier_eq] at hy; exact hy.2
  apply le_antisymm
  · by_contra! hpos
    have he : ∀ᶠ z in 𝓝 y, 0 < g z := hg.tendsto.eventually (lt_mem_nhds hpos)
    obtain ⟨z,hz,hpz,hdz⟩ := ((mem_closure_iff_frequently.mp (frontier_subset_closure hy)).and_eventually
      (he.and hdef)).exists
    have hn := hdz.mp hz
    linarith
  · by_contra! hneg
    exact hyn (hdef.self_of_nhds.mpr hneg)

theorem definingUnitNormal_support_minkowski_closure
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {t R : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ z ∈ closure (minkowskiDomain t U (ball (0 : E) R)),
      inner ℝ (definingUnitNormal f x) (z-definingParallelMap f t ((1-t)*R) x) ≤ 0 := by
  let n := definingUnitNormal f x
  have hn : ‖n‖ = 1 := definingUnitNormal_norm hDf
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq,hn,one_pow]
  have hs := definingUnitNormal_support_nonpos_of_convex hU hconv (frontier_subset_closure hx)
    (hf.differentiableAt (by norm_num)) hfx hdef
  change closure (minkowskiDomain t U (ball (0 : E) R)) ⊆
    {z : E | inner ℝ n (z-definingParallelMap f t ((1-t)*R) x) ≤ 0}
  apply closure_minimal
  · rintro z ⟨a,ha,b,hb,rfl⟩
    have hsa := hs a ha
    have hsb : inner ℝ n b ≤ R := by
      have hb' : ‖b‖ < R := by simpa only [mem_ball,dist_zero_right] using hb
      exact (real_inner_le_norm n b).trans (by simpa only [hn,one_mul] using hb'.le)
    change inner ℝ n (t • a+(1-t) • b-(t • x+((1-t)*R) • n)) ≤ 0
    simp only [inner_sub_right,inner_add_right,real_inner_smul_right,hnn,mul_one]
    change inner ℝ n (a-x) ≤ 0 at hsa
    rw [inner_sub_right] at hsa
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ht hsa,
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) (sub_nonpos.mpr hsb)]
  · exact isClosed_le
      (show Continuous (fun z : E => inner ℝ n (z-definingParallelMap f t ((1-t)*R) x)) by fun_prop)
      continuous_const

theorem definingUnitNormal_parallel_eq
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {t R : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g (definingParallelMap f t ((1-t)*R) x))
    (hgy : g (definingParallelMap f t ((1-t)*R) x) = 0)
    (hDg : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 (definingParallelMap f t ((1-t)*R) x),
      z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0) :
    definingUnitNormal g (definingParallelMap f t ((1-t)*R) x) = definingUnitNormal f x := by
  exact (supporting_unit_vector_eq_definingUnitNormal hg hgy hDg hgdef
    (definingUnitNormal_norm hDf)
    (definingUnitNormal_support_minkowski_closure hU hconv hx hf hfx hDf hdef ht ht1)).symm

theorem definingUnitNormal_parallel_fderiv_tangent
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R)
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g (definingParallelMap f t ((1-t)*R) x))
    (hgy : g (definingParallelMap f t ((1-t)*R) x) = 0)
    (hDg : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 (definingParallelMap f t ((1-t)*R) x),
      z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0)
    (v : E) (hv : fderiv ℝ f x v = 0) :
    fderiv ℝ (definingUnitNormal g) (definingParallelMap f t ((1-t)*R) x)
      (fderiv ℝ (definingParallelMap f t ((1-t)*R)) x v) =
        fderiv ℝ (definingUnitNormal f) x v := by
  let F := definingParallelMap f t ((1-t)*R)
  let V := minkowskiDomain t U (ball (0 : E) R)
  have hVo : IsOpen V := by
    change IsOpen (minkowskiDomain t U (ball (0 : E) R))
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  obtain ⟨γ,N,hNo,h0N,hγ0,hγc,hγb,hγf,hγD⟩ :=
    exists_contDiff_defining_boundary_chart hU hf hfx hDf hdef
  have hγca := hγc.contDiffAt (hNo.mem_nhds h0N)
  have hγd := hγca.differentiableAt (by norm_num)
  have hγt : Tendsto γ (𝓝 (0 : E)) (𝓝 x) := by simpa only [hγ0] using hγca.continuousAt.tendsto
  have hFd : DifferentiableAt ℝ F x :=
    (definingParallelMap_contDiffAt (n := 1) (by simpa only [one_add_one_eq_two] using hf) hDf t ((1-t)*R)).differentiableAt (by norm_num)
  have hφt : Tendsto (F ∘ γ) (𝓝 (0 : E)) (𝓝 (F x)) := hFd.continuousAt.tendsto.comp hγt
  have hnearDf := (hf.fderiv_right (m := 1) (by norm_num)).continuousAt.tendsto.eventually
    (eventually_ne_nhds hDf)
  have hnearDg := (hg.fderiv_right (m := 1) (by norm_num)).continuousAt.tendsto.eventually
    (eventually_ne_nhds hDg)
  have heq : (definingUnitNormal g ∘ F) ∘ γ =ᶠ[𝓝 (0 : E)] definingUnitNormal f ∘ γ := by
    filter_upwards [hNo.mem_nhds h0N,hγt.eventually (hf.eventually (by norm_num)),
      hγt.eventually hnearDf,hγt.eventually hdef.eventually_nhds,
      hφt.eventually (hg.eventually (by norm_num)),hφt.eventually hnearDg,
      hφt.eventually hgdef.eventually_nhds] with z hz hfz hDfz hdefz hgz hDgz hgdefz
    have hbz := definingParallelMap_mem_minkowski_frontier hU hconv (hγb hz) hfz
      (hγf z hz) hDfz hdefz ht ht1 hR
    have hgz0 := definingFunction_zero_of_frontier hVo hbz hgz.continuousAt hgdefz
    exact definingUnitNormal_parallel_eq hU hconv (hγb hz) hfz (hγf z hz) hDfz hdefz
      ht.le ht1 hgz hgz0 hDgz hgdefz
  have hngd := definingUnitNormal_differentiableAt hg hDg
  have hnfd := definingUnitNormal_differentiableAt hf hDf
  have hleft : DifferentiableAt ℝ (definingUnitNormal g ∘ F) (γ 0) := by
    rw [hγ0]
    exact hngd.comp x hFd
  have hright : DifferentiableAt ℝ (definingUnitNormal f) (γ 0) := by rwa [hγ0]
  have hder := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp 0 hleft hγd,fderiv_comp 0 hright hγd,hγ0,
    fderiv_comp x hngd hFd] at hder
  have hh := congrArg (fun D : E →L[ℝ] E => D v) hder
  simpa only [ContinuousLinearMap.comp_apply,hγD v hv] using hh

end PowerConvexity
