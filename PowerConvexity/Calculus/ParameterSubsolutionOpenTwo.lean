import PowerConvexity.Calculus.ParameterPshOpenTwo

/-! # Actual determinant continuity and openness of strict subsolution jets -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E]

section General
variable [NormedSpace ℝ E]

theorem parameter_complexHessian_det_re_continuousAt_of_joint_C2_two
    (a b : Fin 2 → E) {F : ℝ × E → ℝ} {p : ℝ × E}
    (hF : ContDiffAt ℝ 2 F p) :
    ContinuousAt (fun q : ℝ × E => (complexHessian a b (fun y => F (q.1,y)) q.2).det.re) p := by
  have hH : ContinuousAt (fun q : ℝ × E => complexHessian a b (fun y => F (q.1,y)) q.2) p :=
    parameter_complexHessian_continuousAt_of_joint_C2 a b hF
  have hd : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ => A.det.re) :=
    Complex.continuous_re.comp continuous_id.matrix_det
  exact hd.continuousAt.comp hH

end General

variable [InnerProductSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem parameter_strict_subsolution_eventually_of_joint_C2_two
    (e : Module.Basis (Fin 2) ℂ E) {F : ℝ × E → ℝ} {p : ℝ × E}
    (hF : ContDiffAt ℝ 2 F p)
    (hp : (complexHessian e (fun j => Complex.I • e j) (fun y => F (p.1,y)) p.2).PosDef)
    (hd : (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) (fun y => F (p.1,y)) p.2).det) :
    ∀ᶠ q : ℝ × E in 𝓝 p,
      (complexHessian e (fun j => Complex.I • e j) (fun y => F (q.1,y)) q.2).PosDef ∧
      (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) (fun y => F (q.1,y)) q.2).det := by
  have hnearPos := parameter_complexHessian_posDef_eventually_of_joint_C2_two e hF hp
  have hdc := parameter_complexHessian_det_re_continuousAt_of_joint_C2_two e (fun j => Complex.I • e j) hF
  have hd0 : (1 : ℝ) < (complexHessian e (fun j => Complex.I • e j) (fun y => F (p.1,y)) p.2).det.re :=
    (Complex.lt_def.mp hd).1
  filter_upwards [hnearPos,hdc.tendsto.eventually (lt_mem_nhds hd0)] with q hpq hdq
  exact ⟨hpq,Complex.lt_def.mpr
    ⟨hdq,by simpa only [Complex.one_im] using (Complex.pos_iff.mp hpq.det_pos).2⟩⟩

end PowerConvexity
