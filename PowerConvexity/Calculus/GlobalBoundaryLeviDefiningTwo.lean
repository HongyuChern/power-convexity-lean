import PowerConvexity.Calculus.RegularLocalSubsolutionCoverTwo
import PowerConvexity.Calculus.FiniteBoundaryLeviGluing
import PowerConvexity.Calculus.ComplexLeviPairPositiveTwo
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import CHS.Calculus.HessianLocality

/-! # A global C4 regular, strictly Levi-positive boundary defining function

Two nested cutoffs retain genuine local subsolution jets wherever a weight
is positive. This avoids making assumptions on local functions outside their
validity balls. Full ambient strict psh and a global subsolution are later steps.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem exists_global_regular_Levi_defining_of_local_subsolutions_two
    (e : Module.Basis (Fin 2) ℂ E) {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hK : IsCompact (frontier U))
    (hlocal : ∀ x ∈ frontier U, ∃ r : ℝ, ∃ w : E → ℝ,
      RegularBallSubsolutionDataTwo e (fun j => Complex.I • e j) U x r w) :
    ∃ F : E → ℝ, ContDiff ℝ 4 F ∧ (∀ x ∈ U, F x ≤ 0) ∧
      ∀ x ∈ frontier U, F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
        (∀ᶠ z in 𝓝 x, z ∈ U ↔ F z < 0) ∧
        ∀ v : E, v ≠ 0 → fderiv ℝ F x v = 0 → fderiv ℝ F x (Complex.I • v) = 0 →
          0 < realHessian F x v v+realHessian F x (Complex.I • v) (Complex.I • v) := by
  classical
  obtain ⟨r,w,S,hdata,hcover⟩ := exists_finite_regular_subsolution_boundary_cover_two
    e (fun j => Complex.I • e j) hK hlocal
  let B (p : frontier U) : ContDiffBump (p : E) :=
    ⟨r p/4,r p/2,div_pos (hdata p).1.1 (by norm_num),by linarith [(hdata p).1.1]⟩
  let D (p : frontier U) : ContDiffBump (p : E) :=
    ⟨r p/2,3*r p/4,div_pos (hdata p).1.1 (by norm_num),by linarith [(hdata p).1.1]⟩
  let g (p : frontier U) (x : E) := D p x*w p x
  let F : E → ℝ := fun x => ∑ p ∈ S, B p x*g p x
  let W : Set E := ⋃ p ∈ S, ball (p : E) (r p/4)
  have hBball (p : frontier U) {x : E} (hBx : B p x ≠ 0) : x ∈ ball (p : E) (r p/2) := by
    change x ∈ ball (p : E) (B p).rOut
    rw [← (B p).support_eq]
    exact hBx
  have hsmall (p : frontier U) : ball (p : E) (r p/2) ⊆ ball (p : E) (r p) :=
    ball_subset_ball (by linarith [(hdata p).1.1])
  have hgeq (p : frontier U) {x : E} (hx : x ∈ ball (p : E) (r p/2)) :
      g p =ᶠ[𝓝 x] w p := by
    have hh := (D p).eventuallyEq_one_of_mem_ball hx
    filter_upwards [hh] with y hy
    change D p y*w p y = w p y
    simp only [hy,Pi.one_apply,one_mul]
  have hg (p : frontier U) : ContDiff ℝ 4 (g p) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball (p : E) (r p)
    · exact (D p).contDiffAt.mul ((hdata p).1.2.1.contDiffAt (isOpen_ball.mem_nhds hx))
    · have hd : 3*r p/4 < dist x (p : E) := by
        have hh : r p ≤ dist x (p : E) := not_lt.mp hx
        linarith [(hdata p).1.1]
      have hn : ∀ᶠ y in 𝓝 x, 3*r p/4 < dist y (p : E) :=
        (continuous_id.dist continuous_const).continuousAt.tendsto.eventually (lt_mem_nhds hd)
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hn] with y hy
      have hz : D p y = 0 := (D p).zero_of_le_dist hy.le
      change D p y*w p y = 0
      simp only [hz,zero_mul]
  have hgzero (p : frontier U) {x : E} (hx : x ∈ frontier U) : g p x = 0 := by
    by_cases hz : D p x = 0
    · simp only [g,hz,zero_mul]
    · have hs : x ∈ ball (p : E) (3*r p/4) := by
        change x ∈ ball (p : E) (D p).rOut
        rw [← (D p).support_eq]
        exact hz
      have hb : x ∈ ball (p : E) (r p) := ball_subset_ball (by linarith [(hdata p).1.1]) hs
      dsimp only [g]
      rw [(hdata p).1.2.2.2.1 x ⟨hb,hx⟩,mul_zero]
  have hF : ContDiff ℝ 4 F := ContDiff.sum (fun p _ => (B p).contDiff.mul (hg p))
  have hnegTerm (x : E) (hx : x ∈ U) (p : frontier U) : B p x*g p x ≤ 0 := by
    by_cases hz : B p x = 0
    · simp only [hz,zero_mul,le_refl]
    · have hb := hBball p hz
      rw [(hgeq p hb).self_of_nhds]
      exact mul_nonpos_of_nonneg_of_nonpos (B p).nonneg
        (((hdata p).1.2.2.1 x (hsmall p hb)).mp hx).le
  have hposTerm (x : E) (hx : x ∉ U) (p : frontier U) : 0 ≤ B p x*g p x := by
    by_cases hz : B p x = 0
    · simp only [hz,zero_mul,le_refl]
    · have hb := hBball p hz
      rw [(hgeq p hb).self_of_nhds]
      have hw : 0 ≤ w p x := not_lt.mp (fun hh => hx (((hdata p).1.2.2.1 x (hsmall p hb)).mpr hh))
      exact mul_nonneg (B p).nonneg hw
  have hFnonpos (x : E) (hx : x ∈ U) : F x ≤ 0 := Finset.sum_nonpos (fun p _ => hnegTerm x hx p)
  have hWdef (x : E) (hxW : x ∈ W) : x ∈ U ↔ F x < 0 := by
    constructor
    · intro hxU
      obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp hxW
      have hBx : B p x = 1 := (B p).one_of_mem_closedBall (mem_closedBall.mpr (mem_ball.mp hxp).le)
      have hb : x ∈ ball (p : E) (r p/2) := ball_subset_ball (by linarith [(hdata p).1.1]) hxp
      have hwx : w p x < 0 := ((hdata p).1.2.2.1 x (hsmall p hb)).mp hxU
      have hh : ∑ p ∈ S, B p x*g p x < ∑ _p ∈ S, (0 : ℝ) :=
        Finset.sum_lt_sum (fun q _ => hnegTerm x hxU q)
          ⟨p,hp,by rw [hBx,one_mul,(hgeq p hb).self_of_nhds]; exact hwx⟩
      simpa only [Finset.sum_const_zero] using hh
    · intro hneg
      by_contra hxU
      have hh : 0 ≤ F x := Finset.sum_nonneg (fun p _ => hposTerm x hxU p)
      exact (not_lt_of_ge hh) hneg
  refine ⟨F,hF,hFnonpos,?_⟩
  intro x hx
  have hFx : F x = 0 := Finset.sum_eq_zero (fun p _ => by rw [hgzero p hx,mul_zero])
  have hFdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ F z < 0 := by
    have hWo : IsOpen W := isOpen_biUnion (fun _ _ => isOpen_ball)
    filter_upwards [hWo.mem_nhds (hcover hx)] with z hz
    exact hWdef z hz
  have hap : ∃ p ∈ S, 0 < B p x := by
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hcover hx)
    refine ⟨p,hp,?_⟩
    rw [(B p).one_of_mem_closedBall (mem_closedBall.mpr (mem_ball.mp hxp).le)]
    norm_num
  have hdefg (p : frontier U) (_hp : p ∈ S) (hap : 0 < B p x) :
      fderiv ℝ (g p) x ≠ 0 ∧ (∀ᶠ z in 𝓝 x, z ∈ U ↔ g p z < 0) := by
    have hb := hBball p hap.ne'
    have he := hgeq p hb
    refine ⟨by rw [he.fderiv_eq]; exact (hdata p).2 x (hsmall p hb),?_⟩
    filter_upwards [isOpen_ball.mem_nhds (hsmall p hb),he] with z hz hez
    rw [hez]
    exact (hdata p).1.2.2.1 z hz
  have hpair (p : frontier U) (_hp : p ∈ S) (hap : 0 < B p x) (v : E) (hv : v ≠ 0) :
      0 < realHessian (g p) x v v+realHessian (g p) x (Complex.I • v) (Complex.I • v) := by
    have hb := hBball p hap.ne'
    have he := hgeq p hb
    rw [realHessian_eq_of_eventuallyEq he]
    exact complexHessian_posDef_paired_positive_two e
      (((hdata p).1.2.1.contDiffAt (isOpen_ball.mem_nhds (hsmall p hb))).of_le (by norm_num))
      ((hdata p).1.2.2.2.2 x (hsmall p hb)).1 v hv
  have hjet := finite_weighted_defining_Levi_positive hU hconv hx S (fun v => Complex.I • v)
    (fun p _ => (B p).contDiffAt) (fun p _ => (hg p).contDiffAt.of_le (by norm_num))
    (fun p _ => hgzero p hx) (fun p _ => Eventually.of_forall (fun _ => (B p).nonneg))
    hap hdefg hpair hFdef
  exact ⟨hFx,hjet.1,hFdef,hjet.2⟩

theorem classicalDirichlet_minkowski_exists_global_regular_Levi_defining_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R) :
    let V := minkowskiDomain t U (ball (0 : E) R)
    ∃ F : E → ℝ, ContDiff ℝ 4 F ∧ (∀ x ∈ V, F x ≤ 0) ∧
      ∀ x ∈ frontier V, F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
        (∀ᶠ z in 𝓝 x, z ∈ V ↔ F z < 0) ∧
        ∀ v : E, v ≠ 0 → fderiv ℝ F x v = 0 → fderiv ℝ F x (Complex.I • v) = 0 →
          0 < realHessian F x v v+realHessian F x (Complex.I • v) (Complex.I • v) := by
  let V := minkowskiDomain t U (ball (0 : E) R)
  have hVo : IsOpen V := by
    change IsOpen (minkowskiDomain t U (ball (0 : E) R))
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  have hKV : IsCompact (closure V) := by
    obtain ⟨L,hL⟩ := hK.isBounded.exists_norm_le
    have hUb (x : E) (hx : x ∈ U) : ‖x‖ ≤ max L R :=
      (hL x (subset_closure hx)).trans (le_max_left _ _)
    have hBb (x : E) (hx : x ∈ ball (0 : E) R) : ‖x‖ ≤ max L R := by
      have hh : ‖x‖ < R := by simpa only [mem_ball,dist_zero_right] using hx
      exact hh.le.trans (le_max_right _ _)
    exact minkowskiDomain_isCompact_closure hUb hBb ht.le ht1.le
  apply exists_global_regular_Levi_defining_of_local_subsolutions_two e hVo
    (minkowskiDomain_convex hconv (convex_ball (0 : E) R) t)
    (hKV.of_isClosed_subset isClosed_frontier frontier_subset_closure)
  intro x hx
  exact classicalDirichlet_minkowski_exists_regular_ball_subsolution_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR hx

end PowerConvexity
