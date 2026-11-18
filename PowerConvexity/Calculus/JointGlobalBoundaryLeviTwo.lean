import PowerConvexity.Calculus.JointRegularSubsolutionCoverTwo
import PowerConvexity.Calculus.GlobalBoundaryLeviDefiningTwo

/-! # A single jointly C4 global defining family from a common finite cover

The same spatial bump functions are used for every nearby parameter. Their
inner cutoffs retain the actual local jets wherever the outer weight is
positive. Joint regularity is proved on the entire parameter strip, including
spatial points outside every local validity ball.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem exists_joint_global_regular_Levi_defining_of_finite_subsolutions_two
    (e : Module.Basis (Fin 2) ℂ E) {V : ℝ → Set E} {s : ℝ} {S : Set ℝ}
    (hVo : ∀ t ∈ S, IsOpen (V t)) (hconv : ∀ t ∈ S, Convex ℝ (V t))
    {ι : Type*} (c : ι → E) (r : ι → ℝ) (w : ι → ℝ × E → ℝ) (T : Finset ι)
    (hdata : ∀ i, JointRegularBallSubsolutionDataTwo e (fun j => Complex.I • e j)
      V S s (c i) (r i) (w i))
    {delta : ℝ} (hdelta : 0 < delta)
    (hcover : ∀ t ∈ ball s delta, t ∈ S →
      frontier (V t) ⊆ ⋃ i ∈ T, ball (c i) (r i/4)) :
    ∃ d > 0, d ≤ delta ∧ ∃ F : ℝ × E → ℝ,
      ContDiffOn ℝ 4 F (ball s d ×ˢ (univ : Set E)) ∧
      ∀ t ∈ ball s d, t ∈ S →
        ContDiff ℝ 4 (fun x => F (t,x)) ∧ (∀ x ∈ V t, F (t,x) ≤ 0) ∧
        ∀ x ∈ frontier (V t), F (t,x) = 0 ∧ fderiv ℝ (fun y => F (t,y)) x ≠ 0 ∧
          (∀ᶠ z in 𝓝 x, z ∈ V t ↔ F (t,z) < 0) ∧
          ∀ v : E, v ≠ 0 → fderiv ℝ (fun y => F (t,y)) x v = 0 →
            fderiv ℝ (fun y => F (t,y)) x (Complex.I • v) = 0 →
            0 < realHessian (fun y => F (t,y)) x v v +
              realHessian (fun y => F (t,y)) x (Complex.I • v) (Complex.I • v) := by
  classical
  have hnear : ∀ᶠ t in 𝓝 s, ∀ i ∈ T, t ∈ ball s (r i/2) :=
    (eventually_all_finset T).mpr (fun i _ => ball_mem_nhds s (half_pos (hdata i).1))
  obtain ⟨d0,hd0,hd0N⟩ := Metric.mem_nhds_iff.mp hnear
  let d := min d0 delta
  have hd : 0 < d := lt_min hd0 hdelta
  have hddelta : d ≤ delta := min_le_right _ _
  have hparam (t : ℝ) (ht : t ∈ ball s d) (i : ι) (hi : i ∈ T) :
      t ∈ ball s (r i/2) := hd0N (ball_subset_ball (min_le_left _ _) ht) i hi
  have hpair (t : ℝ) (ht : t ∈ ball s d) (i : ι) (hi : i ∈ T)
      (x : E) (hx : x ∈ ball (c i) (r i)) : (t,x) ∈ ball (s,c i) (r i) := by
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball (by linarith [(hdata i).1]) (hparam t ht i hi),hx⟩
  let B (i : ι) : ContDiffBump (c i) :=
    ⟨r i/4,r i/2,div_pos (hdata i).1 (by norm_num),by linarith [(hdata i).1]⟩
  let D (i : ι) : ContDiffBump (c i) :=
    ⟨r i/2,3*r i/4,div_pos (hdata i).1 (by norm_num),by linarith [(hdata i).1]⟩
  let g (i : ι) (q : ℝ × E) := D i q.2*w i q
  let F : ℝ × E → ℝ := fun q => ∑ i ∈ T, B i q.2*g i q
  let W : Set E := ⋃ i ∈ T, ball (c i) (r i/4)
  have hBball (i : ι) {x : E} (hBx : B i x ≠ 0) : x ∈ ball (c i) (r i/2) := by
    change x ∈ ball (c i) (B i).rOut
    rw [← (B i).support_eq]
    exact hBx
  have hsmall (i : ι) : ball (c i) (r i/2) ⊆ ball (c i) (r i) :=
    ball_subset_ball (by linarith [(hdata i).1])
  have hgeq (i : ι) (t : ℝ) {x : E} (hx : x ∈ ball (c i) (r i/2)) :
      (fun y => g i (t,y)) =ᶠ[𝓝 x] (fun y => w i (t,y)) := by
    have hh := (D i).eventuallyEq_one_of_mem_ball hx
    filter_upwards [hh] with y hy
    change D i y*w i (t,y) = w i (t,y)
    simp only [hy,Pi.one_apply,one_mul]
  have hgeqpoint (i : ι) (t : ℝ) {x : E} (hx : x ∈ ball (c i) (r i/2)) :
      g i (t,x) = w i (t,x) := (hgeq i t hx).self_of_nhds
  have hg (i : ι) (hi : i ∈ T) :
      ContDiffOn ℝ 4 (g i) (ball s d ×ˢ (univ : Set E)) := by
    intro q hq
    by_cases hx : q.2 ∈ ball (c i) (r i)
    · exact (((D i).contDiffAt.comp q contDiffAt_snd).mul
        ((hdata i).2.1.contDiffAt (isOpen_ball.mem_nhds
          (hpair q.1 hq.1 i hi q.2 hx)))).contDiffWithinAt
    · have hd : 3*r i/4 < dist q.2 (c i) := by
        have hh : r i ≤ dist q.2 (c i) := not_lt.mp hx
        linarith [(hdata i).1]
      have hn : ∀ᶠ p : ℝ × E in 𝓝 q, 3*r i/4 < dist p.2 (c i) :=
        (continuous_snd.dist continuous_const).continuousAt.tendsto.eventually (lt_mem_nhds hd)
      have hzreg : ContDiffAt ℝ 4 (g i) q := by
        apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [hn] with p hp
        have hz : D i p.2 = 0 := (D i).zero_of_le_dist hp.le
        change D i p.2*w i p = 0
        simp only [hz,zero_mul]
      exact hzreg.contDiffWithinAt
  have hFjoint : ContDiffOn ℝ 4 F (ball s d ×ˢ (univ : Set E)) :=
    ContDiffOn.sum (fun i hi => ((B i).contDiff.comp contDiff_snd).contDiffOn.mul (hg i hi))
  refine ⟨d,hd,hddelta,F,hFjoint,?_⟩
  intro t ht hS
  have hlocal (i : ι) (hi : i ∈ T) :
      RegularBallSubsolutionDataTwo e (fun j => Complex.I • e j)
        (V t) (c i) (r i) (fun y => w i (t,y)) := by
    have hp (y : E) (hy : y ∈ ball (c i) (r i)) :=
      (hdata i).2.2 (t,y) (hpair t ht i hi y hy)
    refine ⟨⟨(hdata i).1,?_,?_,?_,?_⟩,?_⟩
    · intro y hy
      exact (hp y hy).1.contDiffWithinAt
    · intro y hy
      exact ((hp y hy).2.2.2.2 hS).1
    · intro y hy
      exact ((hp y hy.1).2.2.2.2 hS).2 hy.2
    · intro y hy
      exact ⟨(hp y hy).2.2.1,(hp y hy).2.2.2.1⟩
    · intro y hy
      exact (hp y hy).2.1
  have hgfiber (i : ι) (hi : i ∈ T) : ContDiff ℝ 4 (fun x => g i (t,x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact ((hg i hi).contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  have hFfiber : ContDiff ℝ 4 (fun x => F (t,x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hFjoint.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  have hgzero (i : ι) (hi : i ∈ T) {x : E} (hx : x ∈ frontier (V t)) : g i (t,x) = 0 := by
    by_cases hz : D i x = 0
    · simp only [g,hz,zero_mul]
    · have hs : x ∈ ball (c i) (3*r i/4) := by
        change x ∈ ball (c i) (D i).rOut
        rw [← (D i).support_eq]
        exact hz
      have hb : x ∈ ball (c i) (r i) := ball_subset_ball (by linarith [(hdata i).1]) hs
      dsimp only [g]
      have hwzero : w i (t,x) = 0 := (hlocal i hi).1.2.2.2.1 x ⟨hb,hx⟩
      rw [hwzero,mul_zero]
  have hnegTerm (x : E) (hx : x ∈ V t) (i : ι) (hi : i ∈ T) : B i x*g i (t,x) ≤ 0 := by
    by_cases hz : B i x = 0
    · simp only [hz,zero_mul,le_refl]
    · have hb := hBball i hz
      rw [hgeqpoint i t hb]
      exact mul_nonpos_of_nonneg_of_nonpos (B i).nonneg
        (((hlocal i hi).1.2.2.1 x (hsmall i hb)).mp hx).le
  have hposTerm (x : E) (hx : x ∉ V t) (i : ι) (hi : i ∈ T) : 0 ≤ B i x*g i (t,x) := by
    by_cases hz : B i x = 0
    · simp only [hz,zero_mul,le_refl]
    · have hb := hBball i hz
      rw [hgeqpoint i t hb]
      have hw : 0 ≤ w i (t,x) := not_lt.mp
        (fun hh => hx (((hlocal i hi).1.2.2.1 x (hsmall i hb)).mpr hh))
      exact mul_nonneg (B i).nonneg hw
  have hFnonpos (x : E) (hx : x ∈ V t) : F (t,x) ≤ 0 :=
    Finset.sum_nonpos (fun i hi => hnegTerm x hx i hi)
  have hWdef (x : E) (hxW : x ∈ W) : x ∈ V t ↔ F (t,x) < 0 := by
    constructor
    · intro hxV
      obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hxW
      have hBx : B i x = 1 := (B i).one_of_mem_closedBall (mem_closedBall.mpr (mem_ball.mp hxi).le)
      have hb : x ∈ ball (c i) (r i/2) := ball_subset_ball (by linarith [(hdata i).1]) hxi
      have hwx : w i (t,x) < 0 := ((hlocal i hi).1.2.2.1 x (hsmall i hb)).mp hxV
      have hh : ∑ i ∈ T, B i x*g i (t,x) < ∑ _i ∈ T, (0 : ℝ) :=
        Finset.sum_lt_sum (fun j hj => hnegTerm x hxV j hj)
          ⟨i,hi,by rw [hBx,one_mul,hgeqpoint i t hb]; exact hwx⟩
      simpa only [Finset.sum_const_zero] using hh
    · intro hneg
      by_contra hxV
      have hh : 0 ≤ F (t,x) := Finset.sum_nonneg (fun i hi => hposTerm x hxV i hi)
      exact (not_lt_of_ge hh) hneg
  refine ⟨hFfiber,hFnonpos,?_⟩
  intro x hx
  have hxcover : x ∈ W := hcover t (ball_subset_ball hddelta ht) hS hx
  have hFx : F (t,x) = 0 := Finset.sum_eq_zero (fun i hi => by rw [hgzero i hi hx,mul_zero])
  have hFdef : ∀ᶠ z in 𝓝 x, z ∈ V t ↔ F (t,z) < 0 := by
    have hWo : IsOpen W := isOpen_biUnion (fun _ _ => isOpen_ball)
    filter_upwards [hWo.mem_nhds hxcover] with z hz
    exact hWdef z hz
  have hap : ∃ i ∈ T, 0 < B i x := by
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hxcover
    refine ⟨i,hi,?_⟩
    rw [(B i).one_of_mem_closedBall (mem_closedBall.mpr (mem_ball.mp hxi).le)]
    norm_num
  have hdefg (i : ι) (hi : i ∈ T) (hap : 0 < B i x) :
      fderiv ℝ (fun y => g i (t,y)) x ≠ 0 ∧
        (∀ᶠ z in 𝓝 x, z ∈ V t ↔ g i (t,z) < 0) := by
    have hb := hBball i hap.ne'
    have he := hgeq i t hb
    refine ⟨by rw [he.fderiv_eq]; exact (hlocal i hi).2 x (hsmall i hb),?_⟩
    filter_upwards [isOpen_ball.mem_nhds (hsmall i hb),he] with z hz hez
    rw [hez]
    exact (hlocal i hi).1.2.2.1 z hz
  have hpairpos (i : ι) (hi : i ∈ T) (hap : 0 < B i x) (v : E) (hv : v ≠ 0) :
      0 < realHessian (fun y => g i (t,y)) x v v +
        realHessian (fun y => g i (t,y)) x (Complex.I • v) (Complex.I • v) := by
    have hb := hBball i hap.ne'
    have he := hgeq i t hb
    rw [realHessian_eq_of_eventuallyEq he]
    exact complexHessian_posDef_paired_positive_two e
      (((hlocal i hi).1.2.1.contDiffAt (isOpen_ball.mem_nhds (hsmall i hb))).of_le (by norm_num))
      ((hlocal i hi).1.2.2.2.2 x (hsmall i hb)).1 v hv
  have hjet := finite_weighted_defining_Levi_positive (hVo t hS) (hconv t hS) hx T
    (fun v => Complex.I • v) (fun i _ => (B i).contDiffAt)
    (fun i hi => (hgfiber i hi).contDiffAt.of_le (by norm_num))
    (fun i hi => hgzero i hi hx) (fun i _ => Eventually.of_forall (fun _ => (B i).nonneg))
    hap hdefg hpairpos hFdef
  exact ⟨hFx,hjet.1,hFdef,hjet.2⟩

theorem classicalDirichlet_minkowski_exists_joint_global_regular_Levi_defining_two
    [CompleteSpace E]
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
      ContDiffOn ℝ 4 F (ball s d ×ˢ (univ : Set E)) ∧
      ∀ t ∈ ball s d, t ∈ Icc (0 : ℝ) 1 →
        ContDiff ℝ 4 (fun x => F (t,x)) ∧ (∀ x ∈ V t, F (t,x) ≤ 0) ∧
        ∀ x ∈ frontier (V t), F (t,x) = 0 ∧ fderiv ℝ (fun y => F (t,y)) x ≠ 0 ∧
          (∀ᶠ z in 𝓝 x, z ∈ V t ↔ F (t,z) < 0) ∧
          ∀ v : E, v ≠ 0 → fderiv ℝ (fun y => F (t,y)) x v = 0 →
            fderiv ℝ (fun y => F (t,y)) x (Complex.I • v) = 0 →
            0 < realHessian (fun y => F (t,y)) x v v +
              realHessian (fun y => F (t,y)) x (Complex.I • v) (Complex.I • v) := by
  let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨r,w,T,hdata,delta,hdelta,hcover⟩ :=
    classicalDirichlet_minkowski_exists_finite_parameter_subsolution_boundary_cover_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet hs hs1 hR
  have hVo (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) : IsOpen (V t) :=
    (minkowskiDomain_real_parameterGraph_isOpen hU isOpen_ball).preimage
      (continuous_const.prodMk continuous_id)
  obtain ⟨d,hd,_hddelta,F,hF,hFdata⟩ :=
    exists_joint_global_regular_Levi_defining_of_finite_subsolutions_two e hVo
      (fun t _ => minkowskiDomain_convex hconv (convex_ball (0 : E) R) t)
      (fun p : frontier (V s) => (p : E)) r w T hdata hdelta
      (fun t ht hI => (hcover t ht hI).2)
  exact ⟨d,hd,F,hF,hFdata⟩

end PowerConvexity
