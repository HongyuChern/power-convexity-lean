import PowerConvexity.Calculus.ParameterStrictSubsolutionScalingTwo
import PowerConvexity.Analysis.CompactPositiveScaling

/-! # One det>1 scaling on every nearby actual closure

The minimum is taken on the compact actual parameter-closure graph, after
restricting to one closed parameter interval contained in the C4 strip.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_joint_uniform_positive_scaling_on_closures_two
    (a b : Fin 2 → E) {V : ℝ → Set E} {s d : ℝ} (hd : 0 < d)
    (hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)})
    {F : ℝ × E → ℝ} (hF : ContDiffOn ℝ 4 F (ball s (2*d) ×ˢ (univ : Set E)))
    (hpos : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ closure (V t),
      (complexHessian a b (fun y => F (t,y)) x).PosDef) :
    ∃ c > 1, ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ closure (V t),
      (complexHessian a b (fun y => c*F (t,y)) x).PosDef ∧
      (1 : ℂ) < (complexHessian a b (fun y => c*F (t,y)) x).det := by
  let K : Set (ℝ × E) :=
    {q | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)} ∩ Prod.fst ⁻¹' closedBall s d
  have hK : IsCompact K := hgraph.inter_right (isClosed_closedBall.preimage continuous_fst)
  have hC2 (q : ℝ × E) (hq : q ∈ K) : ContDiffAt ℝ 2 F q :=
    (hF.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
      ⟨closedBall_subset_ball (by linarith : d < 2*d) hq.2,mem_univ q.2⟩)).of_le (by norm_num)
  let detF : ℝ × E → ℝ := fun q => (complexHessian a b (fun y => F (q.1,y)) q.2).det.re
  have hdc : ContinuousOn detF K := by
    intro q hq
    exact (((Complex.continuous_re.comp continuous_id.matrix_det).continuousAt).comp
      (parameter_complexHessian_continuousAt_of_joint_C2 a b (hC2 q hq))).continuousWithinAt
  have hdetpos (q : ℝ × E) (hq : q ∈ K) : 0 < detF q :=
    (Complex.pos_iff.mp (hpos q.1 hq.2 hq.1.1 q.2 hq.1.2).det_pos).1
  obtain ⟨m,hm,hmK⟩ := hK.exists_forall_le' hdc hdetpos
  let c := 1/m+1
  have hc1 : 1 < c := by dsimp only [c]; linarith [div_pos (by norm_num : (0 : ℝ) < 1) hm]
  have hc : 0 < c := lt_trans (by norm_num) hc1
  have hcm : c*m = 1+m := by dsimp only [c]; rw [add_mul,one_mul,div_mul_cancel₀ _ hm.ne']
  have hc2m : 1 < c^2*m := by
    have hh := mul_le_mul_of_nonneg_right hc1.le (mul_nonneg hc.le hm.le)
    nlinarith
  refine ⟨c,hc1,?_⟩
  intro t ht hI x hx
  have hq : (t,x) ∈ K := ⟨⟨hI,hx⟩,ht⟩
  have hf2 : ContDiffAt ℝ 2 (fun y => F (t,y)) x :=
    (hC2 (t,x) hq).comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hscale := complexHessian_const_mul_at hf2 c a b
  have hp : (complexHessian a b (fun y => c*F (t,y)) x).PosDef := by
    rw [hscale]
    exact (hpos t ht hI x hx).smul
      (show (0 : ℂ) < (c : ℂ) from Complex.pos_iff.mpr ⟨hc,by simp⟩)
  have he : (complexHessian a b (fun y => c*F (t,y)) x).det.re = c^2*detF (t,x) := by
    rw [hscale,Matrix.det_smul]
    simp [detF,Complex.mul_re,Complex.mul_im,pow_two]
  refine ⟨hp,Complex.lt_def.mpr ⟨?_,?_⟩⟩
  · simp only [Complex.one_re,he]
    exact hc2m.trans_le (mul_le_mul_of_nonneg_left (hmK (t,x) hq) (sq_nonneg c))
  · simpa only [Complex.one_im] using (Complex.pos_iff.mp hp.det_pos).2

end PowerConvexity
