import PowerConvexity.Calculus.SmallScaledSupersolutionTwo
import PowerConvexity.Calculus.ParameterSubsolutionOpenTwo

/-! # One genuine small supersolution scale on a moving compact closure graph -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_strictPsh_has_small_det_scaling_two
    (a b : Fin 2 → E) {V : ℝ → Set E} {s d : ℝ} (hd : 0 < d)
    (hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)})
    {w : ℝ × E → ℝ} (hw : ContDiffOn ℝ 4 w (ball s (2*d) ×ˢ (univ : Set E)))
    (hwp : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ closure (V t),
      (complexHessian a b (fun y => w (t,y)) x).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      ∀ x ∈ closure (V t),
        (complexHessian a b (fun y => c*w (t,y)) x).PosDef ∧
        (complexHessian a b (fun y => c*w (t,y)) x).det.re < 1 := by
  let K : Set (ℝ × E) :=
    {q | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)} ∩ Prod.fst ⁻¹' closedBall s d
  have hK : IsCompact K := hgraph.inter_right (isClosed_closedBall.preimage continuous_fst)
  have hC2 (q : ℝ × E) (hq : q ∈ K) : ContDiffAt ℝ 2 w q :=
    (hw.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
      ⟨closedBall_subset_ball (by linarith : d < 2*d) hq.2,mem_univ q.2⟩)).of_le (by norm_num)
  let D : ℝ × E → ℝ := fun q => (complexHessian a b (fun y => w (q.1,y)) q.2).det.re
  have hDc (q : ℝ × E) (hq : q ∈ K) : ContinuousAt D q :=
    parameter_complexHessian_det_re_continuousAt_of_joint_C2_two a b (hC2 q hq)
  let F : ℝ × (ℝ × E) → ℝ := fun z => 1-z.1^2*D z.2
  have hFc (q : ℝ × E) (hq : q ∈ K) : ContinuousAt F (0,q) := by
    have hDs : ContinuousAt (fun z : ℝ × (ℝ × E) => D z.2) (0,q) :=
      ContinuousAt.comp (f := Prod.snd) (g := D) (hDc q hq) continuousAt_snd
    exact continuousAt_const.sub ((continuousAt_fst.pow 2).mul hDs)
  obtain ⟨c,hc,hsmall⟩ := compact_small_parameter_positive (F := F) hK hFc
    (fun q _ => by simp [F])
  refine ⟨c,hc,?_⟩
  intro t ht hI x hx
  have hq : (t,x) ∈ K := ⟨⟨hI,hx⟩,ht⟩
  have hwx : ContDiffAt ℝ 2 (fun y => w (t,y)) x :=
    (hC2 (t,x) hq).comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hscale := complexHessian_const_mul_at hwx c a b
  refine ⟨?_,?_⟩
  · rw [hscale]
    exact (hwp t ht hI x hx).smul
      (show (0 : ℂ) < (c : ℂ) from Complex.pos_iff.mpr ⟨hc,by simp⟩)
  · have he : (complexHessian a b (fun y => c*w (t,y)) x).det.re = c^2*D (t,x) := by
      rw [hscale,Matrix.det_smul]
      simp [D,Complex.mul_re,Complex.mul_im,pow_two]
    have hh := hsmall c (by simpa only [Real.norm_eq_abs,abs_of_pos hc]
      using (le_rfl : c ≤ c)) (t,x) hq
    change 0 < 1-c^2*D (t,x) at hh
    rw [he]
    linarith

theorem joint_strictPsh_uniform_scaled_supersolution_comparison_two
    (a b : Fin 2 → E) {V : ℝ → Set E} {s d : ℝ} (hd : 0 < d)
    (hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)})
    (hgeometry : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      IsOpen (V t) ∧ Convex ℝ (V t) ∧ IsCompact (closure (V t)))
    {w : ℝ × E → ℝ} (hw : ContDiffOn ℝ 4 w (ball s (2*d) ×ˢ (univ : Set E)))
    (hwb : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ frontier (V t), w (t,x) = 0)
    (hwp : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ closure (V t),
      (complexHessian a b (fun y => w (t,y)) x).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      ∀ (u : E → ℝ) (J : ClosureC2Jet u (V t)), ContDiffOn ℝ 2 u (V t) →
        (∀ x ∈ frontier (V t), u x = 0) →
        (∀ x ∈ V t, (complexHessian a b u x).PosDef) →
        (∀ x ∈ V t, (complexHessian a b u x).det = 1) →
        (∀ x ∈ closure (V t), u x ≤ c*w (t,x)) ∧
        ∀ x ∈ frontier (V t), ∀ y ∈ closure (V t),
          J.derivative x (y-x) ≤ c*fderiv ℝ (fun z => w (t,z)) x (y-x) := by
  obtain ⟨c,hc,hscale⟩ := joint_strictPsh_has_small_det_scaling_two a b hd hgraph hw hwp
  refine ⟨c,hc,?_⟩
  intro t ht hI u J hu hub hup hud
  obtain ⟨hU,hconv,hK⟩ := hgeometry t ht hI
  have hw2 : ContDiff ℝ 2 (fun x => w (t,x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have hwq : ContDiffAt ℝ 2 w (t,x) :=
      (hw.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
        ⟨closedBall_subset_ball (by linarith : d < 2*d) ht,mem_univ x⟩)).of_le (by norm_num)
    exact hwq.comp x (contDiffAt_const.prodMk contDiffAt_id)
  let W : E → ℝ := fun y => c*w (t,y)
  have hW : ContDiff ℝ 2 W := contDiff_const.mul hw2
  have hWb : ∀ x ∈ frontier (V t), W x = 0 := fun x hx => by
    simp only [W,hwb t ht hI x hx,mul_zero]
  have hle : ∀ x ∈ closure (V t), u x ≤ W x := by
    apply classical_strict_comparison_two hU hK a b J.continuous_value
      hW.continuous.continuousOn hu hW.contDiffOn hup
    · intro x hx
      rw [hud x hx,Complex.one_re]
      exact (hscale t ht hI x (subset_closure hx)).2
    · intro x hx
      rw [hub x hx,hWb x hx]
  refine ⟨hle,?_⟩
  intro x hx y hy
  have hm : IsMinOn (fun z => W z-u z) (closure (V t)) x := by
    intro z hz
    change W x-u x ≤ W z-u z
    rw [hWb x hx,hub x hx,sub_self]
    exact sub_nonneg.mpr (hle z hz)
  have hdu := closureJet_hasFDerivWithinAt hU hconv
    (hu.differentiableOn (by norm_num)) J (frontier_subset_closure hx)
  have hdW : HasFDerivWithinAt W (fderiv ℝ W x) (closure (V t)) x :=
    (hW.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  have hh := hm.localize.hasFDerivWithinAt_nonneg (hdW.sub hdu)
    (sub_mem_posTangentConeAt_of_segment_subset
      (hconv.closure.segment_subset (frontier_subset_closure hx) hy))
  have hder : fderiv ℝ W x = c • fderiv ℝ (fun z => w (t,z)) x :=
    fderiv_const_mul (hw2.contDiffAt.differentiableAt (by norm_num)) c
  rw [hder] at hh
  simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,sub_nonneg] using hh

end PowerConvexity
