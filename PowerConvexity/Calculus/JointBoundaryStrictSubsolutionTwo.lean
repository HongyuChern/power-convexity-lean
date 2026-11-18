import PowerConvexity.Calculus.JointGlobalBoundaryLeviTwo
import PowerConvexity.Calculus.GlobalStrictPshBoundaryNeighborhoodTwo
import PowerConvexity.Calculus.ParameterStrictSubsolutionScalingTwo
import PowerConvexity.Analysis.CompactMovingBoundaryBounds
import PowerConvexity.Analysis.CompactPositiveScaling
import PowerConvexity.Calculus.ParameterSubsolutionOpenTwo

/-! # One jointly C4 strict subsolution on all nearby actual boundaries

One normal correction coefficient and one positive scaling are chosen on the
whole compact base boundary. Joint actual Hessian continuity and compactness
of the actual moving-boundary graph preserve strict psh and det>1 everywhere
on the nearby boundaries. This does not assert positivity in the whole domain.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance jbssRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance jbssRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance jbssDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance jbssDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance jbssDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance jbssHessAddGroup : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toAddCommGroup
local instance jbssHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance jbssHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance jbssHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem joint_C4_strict_subsolution_on_nearby_boundaries_two
    (e : Module.Basis (Fin 2) ℂ E) {V : ℝ → Set E} {s delta : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hdelta : 0 < delta)
    (hK : IsCompact (frontier (V s)))
    (hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)})
    {F : ℝ × E → ℝ} (hF : ContDiffOn ℝ 4 F (ball s delta ×ˢ (univ : Set E)))
    (hboundary : ∀ t ∈ ball s delta, t ∈ Icc (0 : ℝ) 1 →
      ∀ x ∈ frontier (V t), F (t,x) = 0 ∧ fderiv ℝ (fun y => F (t,y)) x ≠ 0 ∧
        (∀ᶠ z in 𝓝 x, z ∈ V t ↔ F (t,z) < 0) ∧
        ∀ v : E, v ≠ 0 → fderiv ℝ (fun y => F (t,y)) x v = 0 →
          fderiv ℝ (fun y => F (t,y)) x (Complex.I • v) = 0 →
          0 < realHessian (fun y => F (t,y)) x v v +
            realHessian (fun y => F (t,y)) x (Complex.I • v) (Complex.I • v)) :
    ∃ d > 0, ∃ w : ℝ × E → ℝ,
      ContDiffOn ℝ 4 w (ball s (2*d) ×ˢ (univ : Set E)) ∧
      ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
        ContDiff ℝ 4 (fun x => w (t,x)) ∧
        ∀ x ∈ frontier (V t), w (t,x) = 0 ∧ fderiv ℝ (fun y => w (t,y)) x ≠ 0 ∧
          (∀ᶠ z in 𝓝 x, z ∈ V t ↔ w (t,z) < 0) ∧
          (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).PosDef ∧
          (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).det := by
  let I : E →L[ℝ] E := (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  have hI (v : E) : I v = Complex.I • v := rfl
  have hFfiber (t : ℝ) (ht : t ∈ ball s delta) : ContDiff ℝ 4 (fun x => F (t,x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hF.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  let f : E → ℝ := fun x => F (s,x)
  have hf : ContDiff ℝ 4 f := hFfiber s (mem_ball_self hdelta)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hDc : Continuous (fderiv ℝ f) := continuous_iff_continuousAt.mpr (fun _ =>
    (hf2.contDiffAt.fderiv_right (m := 1) (by norm_num)).continuousAt)
  have hHc : Continuous (realHessian f) := continuous_iff_continuousAt.mpr (fun _ =>
    ((hf2.contDiffAt.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt)
  obtain ⟨lam,hlam,hpos⟩ := exists_uniform_rankTwo_stabilization_positive hK
    (fun x => pairedBilinearForm I (realHessian f x)) (fderiv ℝ f)
    (fun x => (fderiv ℝ f x).comp I) ((continuous_pairedBilinearForm I).comp hHc)
    hDc (hDc.clm_comp continuous_const)
    (by
      intro x hx v hv hDv hDIv
      exact (hboundary s (mem_ball_self hdelta) hs x hx).2.2.2 v hv hDv hDIv)
  let rho : ℝ × E → ℝ := fun q => F q+(lam/2)*(F q*F q)
  have hrho : ContDiffOn ℝ 4 rho (ball s delta ×ˢ (univ : Set E)) :=
    hF.add (contDiffOn_const.mul (hF.mul hF))
  have hrhobase : ContDiff ℝ 4 (fun x => rho (s,x)) :=
    hf.add (contDiff_const.mul (hf.mul hf))
  have hrhobase2 : ContDiff ℝ 2 (fun x => rho (s,x)) := hrhobase.of_le (by norm_num)
  have hposbase (x : E) (hx : x ∈ frontier (V s)) :
      (complexHessian e (fun j => Complex.I • e j) (fun y => rho (s,y)) x).PosDef := by
    apply complexHessian_posDef_of_paired_positive_two e hrhobase2.contDiffAt
    intro v hv
    have hfx : f x = 0 := (hboundary s (mem_ball_self hdelta) hs x hx).1
    change 0 < realHessian (fun y => f y+(lam/2)*(f y*f y)) x v v +
      realHessian (fun y => f y+(lam/2)*(f y*f y)) x (I v) (I v)
    rw [realHessian_defining_normal_correction hf2.contDiffAt hfx,
      realHessian_defining_normal_correction hf2.contDiffAt hfx]
    have hh := hpos x hx v hv
    change 0 < realHessian f x v v+realHessian f x (I v) (I v) +
      lam*((fderiv ℝ f x v)^2+(fderiv ℝ f x (I v))^2) at hh
    nlinarith
  let detR : E → ℝ := fun x =>
    (complexHessian e (fun j => Complex.I • e j) (fun y => rho (s,y)) x).det.re
  have hdetR : Continuous detR := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((Complex.continuous_re.comp continuous_id.matrix_det).continuousAt).comp
      (complexHessian_continuousAt_of_C2 e (fun j => Complex.I • e j) hrhobase2.contDiffAt)
  obtain ⟨c,hc1,hcK⟩ := exists_uniform_square_scaling_gt_one hK hdetR
    (fun x hx => (Complex.pos_iff.mp (hposbase x hx).det_pos).1)
  have hc : 0 < c := lt_trans (by norm_num) hc1
  let w : ℝ × E → ℝ := fun q => c*rho q
  have hw : ContDiffOn ℝ 4 w (ball s delta ×ˢ (univ : Set E)) := contDiffOn_const.mul hrho
  have hwbase : ContDiff ℝ 4 (fun x => w (s,x)) := contDiff_const.mul hrhobase
  have hwbase2 : ContDiff ℝ 2 (fun x => w (s,x)) := hwbase.of_le (by norm_num)
  have hwbasePos (x : E) (hx : x ∈ frontier (V s)) :
      (complexHessian e (fun j => Complex.I • e j) (fun y => w (s,y)) x).PosDef ∧
      (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) (fun y => w (s,y)) x).det := by
    have hscale := complexHessian_const_mul_at hrhobase2.contDiffAt c e (fun j => Complex.I • e j) (x := x)
    have hp : (complexHessian e (fun j => Complex.I • e j) (fun y => w (s,y)) x).PosDef := by
      change (complexHessian e (fun j => Complex.I • e j) (fun y => c*rho (s,y)) x).PosDef
      rw [hscale]
      exact (hposbase x hx).smul (show (0 : ℂ) < (c : ℂ) from Complex.pos_iff.mpr ⟨hc,by simp⟩)
    have he : (complexHessian e (fun j => Complex.I • e j) (fun y => w (s,y)) x).det.re = c^2*detR x := by
      change (complexHessian e (fun j => Complex.I • e j) (fun y => c*rho (s,y)) x).det.re = _
      rw [hscale,Matrix.det_smul]
      simp [detR,Complex.mul_re,Complex.mul_im,pow_two]
    refine ⟨hp,Complex.lt_def.mpr ⟨?_,?_⟩⟩
    · simpa only [Complex.one_re,he] using hcK x hx
    · simpa only [Complex.one_im] using (Complex.pos_iff.mp hp.det_pos).2
  let Q : ℝ × E → Prop := fun q =>
    (complexHessian e (fun j => Complex.I • e j) (fun y => w (q.1,y)) q.2).PosDef ∧
    (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) (fun y => w (q.1,y)) q.2).det
  have hlocal (x : E) (hx : x ∈ frontier (V s)) : ∀ᶠ q in 𝓝 (s,x), Q q := by
    have hw2 : ContDiffAt ℝ 2 w (s,x) :=
      (hw.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
        ⟨mem_ball_self hdelta,mem_univ x⟩)).of_le (by norm_num)
    exact parameter_strict_subsolution_eventually_of_joint_C2_two e (F := w) (p := (s,x))
      hw2 (hwbasePos x hx).1 (hwbasePos x hx).2
  have hnear : ∀ᶠ t in 𝓝 s, ∀ x : E,
      t ∈ Icc (0 : ℝ) 1 ∧ x ∈ frontier (V t) → Q (t,x) :=
    compact_parameter_graph_eventually_of_joint_local_property hgraph
      (Q := Q) (s := s) (fun x hx => hlocal x hx.2)
  obtain ⟨eps,heps,hepsN⟩ := Metric.mem_nhds_iff.mp hnear
  let d := min (delta/4) (eps/2)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hd1 : d ≤ delta/4 := min_le_left _ _
  have hd2 : d ≤ eps/2 := min_le_right _ _
  refine ⟨d,hd,w,hw.mono (Set.prod_mono (ball_subset_ball (by linarith : 2*d ≤ delta)) Subset.rfl),?_⟩
  intro t ht hIcc
  have htd : t ∈ ball s delta := closedBall_subset_ball (by linarith : d < delta) ht
  have hwt : ContDiff ℝ 4 (fun x => w (t,x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hw.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨htd,mem_univ x⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨hwt,?_⟩
  intro x hx
  obtain ⟨hFx,hDF,hdef,_hLevi⟩ := hboundary t htd hIcc x hx
  have hft : ContDiffAt ℝ 2 (fun y => F (t,y)) x :=
    (hFfiber t htd).contDiffAt.of_le (by norm_num)
  have hdf := hft.differentiableAt (by norm_num)
  have hprod := hdf.fun_mul hdf
  have hmul := hprod.const_mul (lam/2)
  have hrd : DifferentiableAt ℝ (fun y => rho (t,y)) x := hdf.fun_add hmul
  have hDrho : fderiv ℝ (fun y => rho (t,y)) x = fderiv ℝ (fun y => F (t,y)) x := by
    change fderiv ℝ (fun y => F (t,y)+(lam/2)*(F (t,y)*F (t,y))) x = _
    rw [fderiv_fun_add hdf hmul,fderiv_const_mul hprod,fderiv_fun_mul hdf hdf,hFx]
    simp
  have hDw : fderiv ℝ (fun y => w (t,y)) x ≠ 0 := by
    change fderiv ℝ (fun y => c*rho (t,y)) x ≠ 0
    rw [fderiv_const_mul hrd,hDrho]
    exact smul_ne_zero hc.ne' hDF
  have hcoef : ∀ᶠ z in 𝓝 x, 0 < 1+(lam/2)*F (t,z) :=
    (continuousAt_const.add (continuousAt_const.mul hft.continuousAt)).tendsto.eventually
      (lt_mem_nhds (by rw [hFx]; norm_num : (0 : ℝ) < 1+(lam/2)*F (t,x)))
  have hwdef : ∀ᶠ z in 𝓝 x, z ∈ V t ↔ w (t,z) < 0 := by
    filter_upwards [hdef,hcoef] with z hz hcz
    rw [hz]
    have he : w (t,z) = (c*(1+(lam/2)*F (t,z)))*F (t,z) := by dsimp only [w,rho]; ring
    rw [he]
    constructor
    · exact fun hn => mul_neg_of_pos_of_neg (mul_pos hc hcz) hn
    · intro hn
      by_contra! hnn
      exact (not_lt_of_ge (mul_nonneg (mul_pos hc hcz).le hnn)) hn
  have hQ := hepsN (closedBall_subset_ball (by linarith : d < eps) ht) x ⟨hIcc,hx⟩
  exact ⟨by simp only [w,rho,hFx,mul_zero,add_zero],hDw,hwdef,hQ.1,hQ.2⟩

end
end PowerConvexity
