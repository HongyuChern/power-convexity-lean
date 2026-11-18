import PowerConvexity.Calculus.StrongDefiningJointGlobalGeometryTwo
import PowerConvexity.Calculus.MinkowskiJointGlobalStrictSubsolutionTwo
import PowerConvexity.Calculus.MinkowskiParameterUniformBoundaryTwo
import PowerConvexity.Calculus.MinkowskiParameterUniformFirstTangentTwo

/-! # Actual locally common a priori bounds for strong Minkowski approximants

The joint strong-domain geometry works also at the ball endpoint. The actual
boundary strict subsolution is extended into each true moving closure with
one common local parameter scale, then supplies actual first-derivative and
full boundary Hessian bounds before the parameter and the unknown solution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]

theorem strong_defining_minkowski_exists_joint_boundary_strict_subsolution_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hUn : U.Nonempty) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hH : ∀ x ∈ frontier U, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian f x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {s R : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hR : 0 < R) :
    let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
    ∃ d > 0, ∃ w : ℝ × E → ℝ,
      ContDiffOn ℝ 4 w (ball s (2*d) ×ˢ (univ : Set E)) ∧
      ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
        ContDiff ℝ 4 (fun x => w (t,x)) ∧
        ∀ x ∈ frontier (V t), w (t,x) = 0 ∧ fderiv ℝ (fun y => w (t,y)) x ≠ 0 ∧
          (∀ᶠ z in 𝓝 x, z ∈ V t ↔ w (t,z) < 0) ∧
          (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).PosDef ∧
          (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).det := by
  let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨delta,hdelta,F,hF,hFdata⟩ :=
    strong_defining_minkowski_exists_joint_global_regular_Levi_defining_two
      hU hconv hK hUn hf hb hdelta hH e hab hs hs1 hR
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hVK : IsCompact (closure (V s)) := by
    change IsCompact (closure (minkowskiDomain s U (ball (0 : E) R)))
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul s).add (hBK.smul (1-s))
  exact joint_C4_strict_subsolution_on_nearby_boundaries_two e ⟨hs,hs1⟩ hdelta
    (hVK.of_isClosed_subset isClosed_frontier frontier_subset_closure)
    (minkowskiDomain_real_frontier_parameterGraph_isCompact hU isOpen_ball hK hBK) hF
    (fun t ht hI => (hFdata t ht hI).2.2)


theorem strong_defining_minkowski_exists_joint_global_strict_subsolution_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hUn : U.Nonempty) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hH : ∀ x ∈ frontier U, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian f x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {s R : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hR : 0 < R) :
    let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
    ∃ d > 0, ∃ w : ℝ × E → ℝ,
      ContDiffOn ℝ 4 w (ball s (2*d) ×ˢ (univ : Set E)) ∧
      ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
        ContDiff ℝ 4 (fun x => w (t,x)) ∧ Nonempty (ClosureC2Jet (fun x => w (t,x)) (V t)) ∧
        (∀ x ∈ frontier (V t), w (t,x) = 0 ∧ fderiv ℝ (fun y => w (t,y)) x ≠ 0 ∧
          (∀ᶠ z in 𝓝 x, z ∈ V t ↔ w (t,z) < 0)) ∧
        ∀ x ∈ closure (V t),
          (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).PosDef ∧
          (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).det := by
  let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨d0,hd0,rho,hrho,hrhodata⟩ :=
    strong_defining_minkowski_exists_joint_boundary_strict_subsolution_two
      hU hconv hK hUn hf hb hdelta hH e hab hs hs1 hR
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hVK : IsCompact (closure (V s)) := by
    change IsCompact (closure (minkowskiDomain s U (ball (0 : E) R)))
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul s).add (hBK.smul (1-s))
  have hVo : IsOpen (V s) :=
    (minkowskiDomain_real_parameterGraph_isOpen hU isOpen_ball).preimage
      (continuous_const.prodMk continuous_id)
  have hbase := hrhodata s (mem_closedBall_self hd0.le) ⟨hs,hs1⟩
  obtain ⟨g,hg,hgerm,hgp⟩ := global_C4_strictPsh_extension_preserving_boundary_germs_two
    e hab hVo hVK hbase.1 (fun x hx => (hbase.2 x hx).1)
    (fun x hx => (hbase.2 x hx).2.2.1) (fun x hx => (hbase.2 x hx).2.2.2.1)
  have hclosure : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)} :=
    minkowskiDomain_real_closure_parameterGraph_isCompact hK hBK
  have hfrontier : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)} :=
    minkowskiDomain_real_frontier_parameterGraph_isCompact hU isOpen_ball hK hBK
  obtain ⟨d1,hd1,F,hF,hFdata⟩ := joint_strictPsh_extension_from_base_germs_two e
    (by positivity : 0 < 2*d0) hclosure hfrontier hrho hg hgerm hgp
  let d := min (d0/2) (d1/2)
  have hd : 0 < d := lt_min (half_pos hd0) (half_pos hd1)
  have hdd0 : d ≤ d0 := (min_le_left (d0/2) (d1/2)).trans (by linarith)
  have hdd1 : d ≤ d1 := (min_le_right (d0/2) (d1/2)).trans (by linarith)
  have hFjoint : ContDiffOn ℝ 4 F (ball s (2*d) ×ˢ (univ : Set E)) :=
    hF.mono (Set.prod_mono (ball_subset_ball (by linarith : 2*d ≤ 2*d1)) Subset.rfl)
  have hFpos (t : ℝ) (ht : t ∈ closedBall s d) (hI : t ∈ Icc (0 : ℝ) 1) :=
    (hFdata t (closedBall_subset_closedBall hdd1 ht) hI).2.2
  obtain ⟨c,hc1,hcpos⟩ := exists_joint_uniform_positive_scaling_on_closures_two
    e (fun j => Complex.I • e j) hd hclosure hFjoint hFpos
  have hc : 0 < c := lt_trans (by norm_num) hc1
  let w : ℝ × E → ℝ := fun q => c*F q
  refine ⟨d,hd,w,contDiffOn_const.mul hFjoint,?_⟩
  intro t ht hI
  have hFt := (hFdata t (closedBall_subset_closedBall hdd1 ht) hI).1
  have hwt : ContDiff ℝ 4 (fun x => w (t,x)) := contDiff_const.mul hFt
  have hwt2 : ContDiff ℝ 2 (fun x => w (t,x)) := hwt.of_le (by norm_num)
  have hJ : Nonempty (ClosureC2Jet (fun x => w (t,x)) (V t)) :=
    (c2OnClosure_of_neighborhood isOpen_univ (subset_univ _) hwt2.contDiffOn).2
  refine ⟨hwt,hJ,?_,hcpos t ht hI⟩
  intro x hx
  have he := (hFdata t (closedBall_subset_closedBall hdd1 ht) hI).2.1 x hx
  have hrd := (hrhodata t (closedBall_subset_closedBall hdd0 ht) hI).2 x hx
  have hFx : F (t,x) = 0 := he.self_of_nhds.trans hrd.1
  have hDF : fderiv ℝ (fun y => F (t,y)) x ≠ 0 := by
    rw [he.fderiv_eq]
    exact hrd.2.1
  refine ⟨by simp only [w,hFx,mul_zero],?_,?_⟩
  · change fderiv ℝ (fun y => c*F (t,y)) x ≠ 0
    rw [fderiv_const_mul (hFt.contDiffAt.differentiableAt (by norm_num))]
    exact smul_ne_zero hc.ne' hDF
  · filter_upwards [he,hrd.2.2.1] with z hez hdefz
    rw [hdefz]
    change rho (t,z) < 0 ↔ c*F (t,z) < 0
    have hez' : F (t,z) = rho (t,z) := hez
    rw [hez']
    constructor
    · exact fun hn => mul_neg_of_pos_of_neg hc hn
    · intro hn
      by_contra! hnn
      exact (not_lt_of_ge (mul_nonneg hc.le hnn)) hn


theorem strong_defining_minkowski_parameter_uniform_boundary_quadratic_upper_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hUn : U.Nonempty) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hH : ∀ x ∈ frontier U, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian f x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {s R : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hR : 0 < R) :
    let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
    ∃ d > 0, ∃ C ≥ 0, ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      ∀ (v : E → ℝ) (Jv : ClosureC2Jet v (V t)), ContDiffOn ℝ 3 v (V t) →
        (∀ x ∈ frontier (V t), v x = 0) →
        (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) v x).PosDef) →
        (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) v x).det = 1) →
        ∀ x ∈ frontier (V t), ∀ z : E, Jv.hessian x z z ≤ C*‖z‖^2 := by
  let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨d,hd,w,hw,hwdata⟩ :=
    strong_defining_minkowski_exists_joint_global_strict_subsolution_two
      hU hconv hK hUn hf hb hdelta hH e hab hs hs1 hR
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)} :=
    minkowskiDomain_real_closure_parameterGraph_isCompact hK hBK
  have hfront : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)} :=
    minkowskiDomain_real_frontier_parameterGraph_isCompact hU isOpen_ball hK hBK
  have hgeometry (t : ℝ) (ht : t ∈ closedBall s d) (hI : t ∈ Icc (0 : ℝ) 1) :
      IsOpen (V t) ∧ Convex ℝ (V t) ∧ IsCompact (closure (V t)) ∧ HasC2LocalDefiningFunction (V t) := by
    have hVo : IsOpen (V t) :=
      (minkowskiDomain_real_parameterGraph_isOpen hU isOpen_ball).preimage
        (continuous_const.prodMk continuous_id)
    have hVK : IsCompact (closure (V t)) := by
      change IsCompact (closure (minkowskiDomain t U (ball (0 : E) R)))
      rw [minkowskiDomain_closure hK hBK]
      exact (hK.smul t).add (hBK.smul (1-t))
    refine ⟨hVo,minkowskiDomain_convex hconv (convex_ball (0 : E) R) t,hVK,?_⟩
    intro x hx
    have hwd := hwdata t ht hI
    have hbd := hwd.2.2.1 x hx
    exact ⟨(fun y => w (t,y)),hwd.1.contDiffAt.of_le (by norm_num),hbd.1,hbd.2.1,hbd.2.2⟩
  obtain ⟨C,hC,hbound⟩ := joint_strict_subsolution_uniform_boundary_quadratic_upper_two
    e hab hd hgraph hfront hgeometry hw
    (fun t ht hI => (hwdata t ht hI).2.2.1)
    (fun t ht hI x hx => ((hwdata t ht hI).2.2.2 x hx).1)
    (fun t ht hI x hx => ((hwdata t ht hI).2.2.2 x (subset_closure hx)).2)
  exact ⟨d,hd,C,hC,hbound⟩


theorem strong_defining_minkowski_parameter_uniform_first_tangent_bounds_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hUn : U.Nonempty) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hH : ∀ x ∈ frontier U, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian f x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {s R : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hR : 0 < R) :
    let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
    ∃ d > 0, ∃ C ≥ 0, ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      ∀ (v : E → ℝ) (Jv : ClosureC2Jet v (V t)), ContDiffOn ℝ 3 v (V t) →
        (∀ x ∈ frontier (V t), v x = 0) →
        (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) v x).PosDef) →
        (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) v x).det = 1) →
        (∀ x ∈ closure (V t), ‖Jv.derivative x‖ ≤ C) ∧
        ∀ x ∈ frontier (V t), ∀ z : E,
          Jv.derivative x z = 0 → Jv.hessian x z z ≤ C*‖z‖^2 := by
  let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨d,hd,w,hw,hwdata⟩ :=
    strong_defining_minkowski_exists_joint_global_strict_subsolution_two
      hU hconv hK hUn hf hb hdelta hH e hab hs hs1 hR
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)} :=
    minkowskiDomain_real_closure_parameterGraph_isCompact hK hBK
  have hgeometry (t : ℝ) (ht : t ∈ closedBall s d) (hI : t ∈ Icc (0 : ℝ) 1) :
      IsOpen (V t) ∧ Convex ℝ (V t) ∧ IsCompact (closure (V t)) ∧ HasC2LocalDefiningFunction (V t) := by
    have hVo : IsOpen (V t) :=
      (minkowskiDomain_real_parameterGraph_isOpen hU isOpen_ball).preimage
        (continuous_const.prodMk continuous_id)
    have hVK : IsCompact (closure (V t)) := by
      change IsCompact (closure (minkowskiDomain t U (ball (0 : E) R)))
      rw [minkowskiDomain_closure hK hBK]
      exact (hK.smul t).add (hBK.smul (1-t))
    refine ⟨hVo,minkowskiDomain_convex hconv (convex_ball (0 : E) R) t,hVK,?_⟩
    intro x hx
    have hwd := hwdata t ht hI
    have hbd := hwd.2.2.1 x hx
    exact ⟨(fun y => w (t,y)),hwd.1.contDiffAt.of_le (by norm_num),hbd.1,hbd.2.1,hbd.2.2⟩
  obtain ⟨C,hC,hbound⟩ := joint_strict_subsolution_uniform_first_tangent_bounds_two
    e (fun j => Complex.I • e j) hab hd hgraph hgeometry hw
    (by
      intro t ht hI
      have hwd := hwdata t ht hI
      exact ⟨fun x hx => (hwd.2.2.1 x hx).1,fun x hx => hwd.2.2.2 x (subset_closure hx)⟩)
  exact ⟨d,hd,C,hC,hbound⟩


end PowerConvexity
