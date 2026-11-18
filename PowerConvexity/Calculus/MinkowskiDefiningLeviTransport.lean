import PowerConvexity.Calculus.ParallelNormalTransport

/-! # Levi positivity on the actual intermediate Minkowski domains

The argument transports the actual normal derivative and its null directions.
It preserves positive complex tangent pairs without assuming positive real
principal curvature or postulating a formal parallel shape operator.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem parallel_defining_tangent_kernel_iff
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {t R : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g (definingParallelMap f t ((1-t)*R) x))
    (hgy : g (definingParallelMap f t ((1-t)*R) x) = 0)
    (hDg : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 (definingParallelMap f t ((1-t)*R) x),
      z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0) (v : E) :
    fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) v = 0 ↔ fderiv ℝ f x v = 0 := by
  have he := definingUnitNormal_parallel_eq hU hconv hx hf hfx hDf hdef ht ht1 hg hgy hDg hgdef
  have hh := congrArg (fun n : E => inner ℝ n v) he
  simp only [definingUnitNormal,real_inner_smul_left,inner_gradient_left] at hh
  have hfn := inv_ne_zero (norm_ne_zero_iff.mpr (definingGradient_ne_zero hDf))
  have hgn := inv_ne_zero (norm_ne_zero_iff.mpr (definingGradient_ne_zero hDg))
  constructor
  · intro hz
    rw [hz,mul_zero] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hfn
  · intro hz
    rw [hz,mul_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left hgn

variable [FiniteDimensional ℝ E]

theorem parallel_defining_tangent_hessian_null_transfer
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R)
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g (definingParallelMap f t ((1-t)*R) x))
    (hgy : g (definingParallelMap f t ((1-t)*R) x) = 0)
    (hDg : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 (definingParallelMap f t ((1-t)*R) x),
      z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0)
    {v : E} (hv : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) v = 0)
    (hnull : realHessian g (definingParallelMap f t ((1-t)*R) x) v v = 0) :
    realHessian f x v v = 0 := by
  let F := definingParallelMap f t ((1-t)*R)
  let V := minkowskiDomain t U (ball (0 : E) R)
  have hVo : IsOpen V := by
    change IsOpen (minkowskiDomain t U (ball (0 : E) R))
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  have hVc : Convex ℝ V := minkowskiDomain_convex hconv (convex_ball (0 : E) R) t
  have hy := definingParallelMap_mem_minkowski_frontier hU hconv hx hf hfx hDf hdef ht ht1 hR
  have hnnew := convex_defining_normal_derivative_zero_of_tangent_null hVo hVc hy hg hgy hDg hgdef hv hnull
  have hvold := (parallel_defining_tangent_kernel_iff hU hconv hx hf hfx hDf hdef
    ht.le ht1 hg hgy hDg hgdef v).mp hv
  let L := fderiv ℝ F x
  have hi : Function.Injective L := definingParallelMap_fderiv_injective_of_convex
    hU hconv hx hf hfx hDf hdef ht (mul_nonneg (sub_nonneg.mpr ht1) hR.le)
  obtain ⟨w,hw⟩ := (LinearEquiv.ofInjectiveEndo L.toLinearMap hi).surjective v
  change fderiv ℝ (definingParallelMap f t ((1-t)*R)) x w = v at hw
  have hmap := hw
  rw [definingParallelMap_fderiv hf hDf] at hmap
  change t • w+((1-t)*R) • fderiv ℝ (definingUnitNormal f) x w = v at hmap
  have hfw : fderiv ℝ f x (fderiv ℝ (definingUnitNormal f) x w) = 0 := by
    rw [← inner_gradient_left]
    exact definingUnitNormal_fderiv_normal_orthogonal hf hDf w
  have hwtan : fderiv ℝ f x w = 0 := by
    have hh := congrArg (fun z : E => fderiv ℝ f x z) hmap
    simp only [map_add,map_smul,hfw,hvold,smul_eq_mul,mul_zero,add_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left ht.ne'
  have hchain := definingUnitNormal_parallel_fderiv_tangent hU hconv hx hf hfx hDf hdef
    ht ht1 hR hg hgy hDg hgdef w hwtan
  rw [hw,hnnew] at hchain
  have hnw : fderiv ℝ (definingUnitNormal f) x w = 0 := hchain.symm
  rw [hnw,smul_zero,add_zero] at hmap
  have hnv : fderiv ℝ (definingUnitNormal f) x v = 0 := by
    rw [← hmap,map_smul,hnw,smul_zero]
  have hh := definingUnitNormal_fderiv_tangent_pair hf hDf v v hvold
  rw [hnv,inner_zero_left] at hh
  exact (div_eq_zero_iff.mp hh.symm).resolve_right
    (norm_ne_zero_iff.mpr (definingGradient_ne_zero hDf))

theorem parallel_defining_Levi_positive
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (I : E → E)
    (hLevi : ∀ v : E, v ≠ 0 → fderiv ℝ f x v = 0 → fderiv ℝ f x (I v) = 0 →
      0 < realHessian f x v v+realHessian f x (I v) (I v))
    {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R)
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g (definingParallelMap f t ((1-t)*R) x))
    (hgy : g (definingParallelMap f t ((1-t)*R) x) = 0)
    (hDg : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 (definingParallelMap f t ((1-t)*R) x),
      z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0) :
    ∀ v : E, v ≠ 0 → fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) v = 0 →
      fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) (I v) = 0 →
      0 < realHessian g (definingParallelMap f t ((1-t)*R) x) v v+
        realHessian g (definingParallelMap f t ((1-t)*R) x) (I v) (I v) := by
  intro v hv htv htIv
  have htvf := (parallel_defining_tangent_kernel_iff hU hconv hx hf hfx hDf hdef
    ht.le ht1 hg hgy hDg hgdef v).mp htv
  have htIvf := (parallel_defining_tangent_kernel_iff hU hconv hx hf hfx hDf hdef
    ht.le ht1 hg hgy hDg hgdef (I v)).mp htIv
  have hp := hLevi v hv htvf htIvf
  have hVo : IsOpen (minkowskiDomain t U (ball (0 : E) R)) := by
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  have hVc := minkowskiDomain_convex hconv (convex_ball (0 : E) R) t
  have hy := definingParallelMap_mem_minkowski_frontier hU hconv hx hf hfx hDf hdef ht ht1 hR
  have hqv := definingFunction_tangent_hessian_nonneg_of_convex hVo hVc hy hg hgy hDg hgdef v htv
  have hqIv := definingFunction_tangent_hessian_nonneg_of_convex hVo hVc hy hg hgy hDg hgdef (I v) htIv
  by_contra! hnot
  have hzv : realHessian g (definingParallelMap f t ((1-t)*R) x) v v = 0 := by linarith
  have hzIv : realHessian g (definingParallelMap f t ((1-t)*R) x) (I v) (I v) = 0 := by linarith
  have hfv := parallel_defining_tangent_hessian_null_transfer hU hconv hx hf hfx hDf hdef
    ht ht1 hR hg hgy hDg hgdef htv hzv
  have hfIv := parallel_defining_tangent_hessian_null_transfer hU hconv hx hf hfx hDf hdef
    ht ht1 hR hg hgy hDg hgdef htIv hzIv
  rw [hfv,hfIv,add_zero] at hp
  exact lt_irrefl 0 hp

theorem minkowskiDomain_defining_Levi_positive
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U) (I : E → E)
    (hLevi : ∀ x ∈ frontier U, ∀ f : E → ℝ,
      ContDiffAt ℝ 2 f x → f x = 0 → fderiv ℝ f x ≠ 0 →
      (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) →
      ∀ v : E, v ≠ 0 → fderiv ℝ f x v = 0 → fderiv ℝ f x (I v) = 0 →
        0 < realHessian f x v v+realHessian f x (I v) (I v))
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain t U (ball (0 : E) R)))
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g y) (hgy : g y = 0) (hDg : fderiv ℝ g y ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 y, z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0) :
    ∀ v : E, v ≠ 0 → fderiv ℝ g y v = 0 → fderiv ℝ g y (I v) = 0 →
      0 < realHessian g y v v+realHessian g y (I v) (I v) := by
  obtain ⟨x,hx,f,hf,hfx,hDf,hdef,hyf⟩ := minkowski_frontier_exists_parallel_normal
    hU hconv hK hboundary ht ht1 hR hy
  subst y
  exact parallel_defining_Levi_positive hU hconv hx hf hfx hDf hdef I
    (hLevi x hx f hf hfx hDf hdef) ht ht1.le hR hg hgy hDg hgdef

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem classicalDirichlet_minkowski_defining_Levi_positive_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain t U (ball (0 : E) R)))
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g y) (hgy : g y = 0) (hDg : fderiv ℝ g y ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 y, z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0) :
    ∀ v : E, v ≠ 0 → fderiv ℝ g y v = 0 → fderiv ℝ g y (Complex.I • v) = 0 →
      0 < realHessian g y v v+realHessian g y (Complex.I • v) (Complex.I • v) := by
  apply minkowskiDomain_defining_Levi_positive hU hconv hK
    (smoothLocalDefiningFunction_implies_C2 hboundary) (fun v => Complex.I • v)
    _ ht ht1 hR hy hg hgy hDg hgdef
  intro x hx f hf hfx hDf hdef
  exact classicalDirichlet_defining_Levi_positive_two hU hconv hK hu J hb e hab hpsh hdet
    hx hf hfx hDf hdef

theorem classicalDirichlet_minkowski_exists_smooth_Levi_defining_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain t U (ball (0 : E) R))) :
    ∃ g : E → ℝ, ContDiffAt ℝ ∞ g y ∧ g y = 0 ∧ fderiv ℝ g y ≠ 0 ∧
      (∀ᶠ z in 𝓝 y, z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0) ∧
      ∀ v : E, v ≠ 0 → fderiv ℝ g y v = 0 → fderiv ℝ g y (Complex.I • v) = 0 →
        0 < realHessian g y v v+realHessian g y (Complex.I • v) (Complex.I • v) := by
  obtain ⟨g,hg,hgy,hDg,hgdef⟩ := minkowskiDomain_hasSmoothLocalDefiningFunction hU hconv hK hboundary ht ht1 hR y hy
  refine ⟨g,hg,hgy,hDg,hgdef,?_⟩
  exact classicalDirichlet_minkowski_defining_Levi_positive_two hU hconv hK hboundary hu J hb e hab hpsh hdet
    ht ht1 hR hy ((contDiffAt_infty.mp hg) 2) hgy hDg hgdef

end PowerConvexity
