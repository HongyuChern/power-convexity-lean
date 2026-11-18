import PowerConvexity.Algebra.SchurTraceDetTwo
import PowerConvexity.Calculus.TraceDetRatioRegularity
import PowerConvexity.Algebra.EigenvalueCovarianceTwo

/-! # The actual invariant trace-determinant scalar and its smooth approximants -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def modifiedTraceTwo (a b : Fin 2 → E) (u : E → ℝ) (x : E) : ℝ :=
  (modifiedK a b u x).trace.re
noncomputable def modifiedDetTwo (a b : Fin 2 → E) (u : E → ℝ) (x : E) : ℝ :=
  (modifiedK a b u x).det.re
noncomputable def modifiedTraceRatioTwo (a b : Fin 2 → E) (u : E → ℝ) (x : E) : ℝ :=
  traceDetRatioTwo (modifiedTraceTwo a b u x) (modifiedDetTwo a b u x)
noncomputable def modifiedTraceRatioRegularizedTwo (a b : Fin 2 → E) (u : E → ℝ) (e : ℝ) (x : E) : ℝ :=
  traceDetRatioTwo (modifiedTraceTwo a b u x+2*e)
    (modifiedDetTwo a b u x+e*modifiedTraceTwo a b u x+e^2)

theorem modifiedTraceDetTwo_contDiffAt {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hA : (complexHessian a b u x).PosDef) :
    ContDiffAt ℝ 2 (modifiedTraceTwo a b u) x ∧
      ContDiffAt ℝ 2 (modifiedDetTwo a b u) x := by
  have hK := modifiedK_contDiffAt_two hu hx a b hA
  constructor
  · have hh := Complex.reCLM.contDiff.contDiffAt.comp x ((hK 0 0).add (hK 1 1))
    change ContDiffAt ℝ 2 (fun y => (modifiedK a b u y).trace.re) x
    simpa only [Matrix.trace,Matrix.diag,Fin.sum_univ_two,Function.comp_def,Complex.reCLM_apply] using hh
  · have hh := Complex.reCLM.contDiff.contDiffAt.comp x
      (((hK 0 0).mul (hK 1 1)).sub ((hK 0 1).mul (hK 1 0)))
    change ContDiffAt ℝ 2 (fun y => (modifiedK a b u y).det.re) x
    simpa only [Matrix.det_fin_two,Function.comp_def,Complex.reCLM_apply] using hh

theorem modifiedTraceDetTwo_bounds {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hA : (complexHessian a b u x).PosDef) (hM : (modifiedSchur a b u x).PosSemidef) :
    0 ≤ modifiedTraceTwo a b u x ∧ 0 ≤ modifiedDetTwo a b u x ∧
      modifiedDetTwo a b u x ≤ (modifiedTraceTwo a b u x)^2/4 :=
  schur_quotient_trace_det_bounds_two (modifiedA_posDef a b hx hA) (modifiedB_transpose hu a b) hM

theorem modifiedTraceRatioTwo_bounds {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hA : (complexHessian a b u x).PosDef) (hM : (modifiedSchur a b u x).PosSemidef) :
    modifiedTraceTwo a b u x ≤ modifiedTraceRatioTwo a b u x ∧
      modifiedTraceRatioTwo a b u x ≤ (5/4)*modifiedTraceTwo a b u x := by
  obtain ⟨ht,hd,hdt⟩ := modifiedTraceDetTwo_bounds hu hx a b hA hM
  exact traceDetRatioTwo_bounds ht hd hdt

theorem modifiedTraceRatioTwo_differentiableAt {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    (hM : ∀ y ∈ U, (modifiedSchur a b u y).PosSemidef)
    {x : E} (hx : x ∈ U) : DifferentiableAt ℝ (modifiedTraceRatioTwo a b u) x := by
  obtain ⟨ht,hd⟩ := modifiedTraceDetTwo_contDiffAt (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) a b (hA x hx)
  apply traceDetRatioTwo_differentiableAt (ht.differentiableAt (by norm_num))
    (hd.differentiableAt (by norm_num))
  filter_upwards [hU.mem_nhds hx] with y hy
  exact modifiedTraceDetTwo_bounds ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))
    (hneg y hy) a b (hA y hy) (hM y hy)

theorem modifiedTraceRatioRegularizedTwo_contDiffAt {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hA : (complexHessian a b u x).PosDef) (hM : (modifiedSchur a b u x).PosSemidef)
    {e : ℝ} (he : 0 < e) : ContDiffAt ℝ 2 (modifiedTraceRatioRegularizedTwo a b u e) x := by
  obtain ⟨ht,hd⟩ := modifiedTraceDetTwo_contDiffAt hu hx a b hA
  exact traceDetRatioTwo_regularized_contDiffAt ht hd
    (modifiedTraceDetTwo_bounds (hu.of_le (by norm_num)) hx a b hA hM).1 he

theorem modifiedTraceRatioRegularizedTwo_bounds {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hA : (complexHessian a b u x).PosDef) (hM : (modifiedSchur a b u x).PosSemidef)
    {e : ℝ} (he : 0 ≤ e) :
    modifiedTraceRatioTwo a b u x ≤ modifiedTraceRatioRegularizedTwo a b u e x ∧
      modifiedTraceRatioRegularizedTwo a b u e x ≤ modifiedTraceRatioTwo a b u x+3*e := by
  obtain ⟨ht,hd,hdt⟩ := modifiedTraceDetTwo_bounds hu hx a b hA hM
  exact traceDetRatioTwo_regularization_bounds ht hd hdt he

theorem modifiedTraceRatioRegularizedTwo_tendsto {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hA : (complexHessian a b u x).PosDef) (hM : (modifiedSchur a b u x).PosSemidef) :
    Tendsto (fun n : ℕ => modifiedTraceRatioRegularizedTwo a b u (1/((n:ℝ)+1)) x)
      atTop (𝓝 (modifiedTraceRatioTwo a b u x)) := by
  obtain ⟨ht,hd,hdt⟩ := modifiedTraceDetTwo_bounds hu hx a b hA hM
  exact traceDetRatioTwo_regularization_tendsto
    (Filter.Eventually.of_forall fun n : ℕ => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat ht hd hdt

theorem modifiedTraceDetTwo_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : IsUnit Q.det) (a b : Fin 2 → E) :
    modifiedTraceTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u x = modifiedTraceTwo a b u x ∧
      modifiedDetTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u x = modifiedDetTwo a b u x := by
  have he : (modifiedK (complexFrameReal Q a b) (complexFrameImag Q a b) u x).charpoly =
      (modifiedK a b u x).charpoly := by
    unfold modifiedK
    rw [modifiedSchur_quotient_complexFrame hu hx Q hQ]
    exact charpoly_complex_similarity Q _ hQ
  obtain ⟨ht,hd⟩ := trace_det_eq_of_charpoly_eq_two he
  exact ⟨congrArg Complex.re ht,congrArg Complex.re hd⟩

theorem modifiedTraceRatioTwo_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : IsUnit Q.det) (a b : Fin 2 → E) :
    modifiedTraceRatioTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u x = modifiedTraceRatioTwo a b u x := by
  obtain ⟨ht,hd⟩ := modifiedTraceDetTwo_complexFrame hu hx Q hQ a b
  simp only [modifiedTraceRatioTwo,ht,hd]

end PowerConvexity
