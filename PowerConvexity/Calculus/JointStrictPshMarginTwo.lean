import PowerConvexity.Calculus.ParameterFiberDerivative
import PowerConvexity.Calculus.UniformStrictPshMarginTwo
import PowerConvexity.Analysis.CompactPositiveBilinearMarginOn

/-! # One strict psh margin for every nearby actual closure -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance jspmRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance jspmRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance jspmDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance jspmDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance jspmDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance jspmHessAddGroup : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toAddCommGroup
local instance jspmHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance jspmHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance jspmHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem joint_strictPsh_has_uniform_scalar_and_paired_margin_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {V : ℝ → Set E} {s d : ℝ} (hd : 0 < d)
    (hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)})
    {w : ℝ × E → ℝ} (hw : ContDiffOn ℝ 4 w (ball s (2*d) ×ˢ (univ : Set E)))
    (hpos : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ closure (V t),
      (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).PosDef) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ closure (V t),
      (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x -
        (eps : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosDef ∧
      ∀ v : E, (4*eps)*‖v‖^2 ≤ realHessian (fun y => w (t,y)) x v v +
        realHessian (fun y => w (t,y)) x (Complex.I • v) (Complex.I • v) := by
  let I : E →L[ℝ] E := (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  have hI (v : E) : I v = Complex.I • v := rfl
  let K : Set (ℝ × E) :=
    {q | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)} ∩ Prod.fst ⁻¹' closedBall s d
  have hK : IsCompact K := hgraph.inter_right (isClosed_closedBall.preimage continuous_fst)
  have hC2 (q : ℝ × E) (hq : q ∈ K) : ContDiffAt ℝ 2 w q :=
    (hw.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
      ⟨closedBall_subset_ball (by linarith : d < 2*d) hq.2,mem_univ q.2⟩)).of_le (by norm_num)
  have hW2 (q : ℝ × E) (hq : q ∈ K) : ContDiffAt ℝ 2 (fun y => w (q.1,y)) q.2 :=
    (hC2 q hq).comp q.2 (contDiffAt_const.prodMk contDiffAt_id)
  let Q : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ :=
    fun q => pairedBilinearForm I (realHessian (fun y => w (q.1,y)) q.2)
  let N := pairedBilinearForm I (realHessian (fun y : E => ‖y‖^2) 0)
  have hQc : ContinuousOn Q K := by
    intro q hq
    have hD : ContDiffAt ℝ 1
        (fun p : ℝ × E => fderiv ℝ (fun y => w (p.1,y)) p.2) q :=
      parameter_fiber_fderiv_contDiffAt (n := 1) (hC2 q hq)
    have hH : ContinuousAt
        (fun p : ℝ × E => realHessian (fun y => w (p.1,y)) p.2) q :=
      (parameter_fiber_fderiv_contDiffAt (n := 0) hD).continuousAt
    exact ((continuous_pairedBilinearForm I).continuousAt.comp hH).continuousWithinAt
  have hQpos (q : ℝ × E) (hq : q ∈ K) (v : E) (hv : v ≠ 0) : 0 < Q q v v := by
    simpa only [Q,pairedBilinearForm_apply,hI] using
      complexHessian_posDef_paired_positive_two e (hW2 q hq)
        (hpos q.1 hq.2 hq.1.1 q.2 hq.1.2) v hv
  obtain ⟨eps,heps,hmargin⟩ :=
    compact_positive_bilinear_subtraction_margin_of_continuousOn hK Q hQc N hQpos
  refine ⟨eps,heps,?_⟩
  intro t ht hIcc x hx
  have hq : (t,x) ∈ K := ⟨⟨hIcc,hx⟩,ht⟩
  let f : E → ℝ := fun y => w (t,y)
  have hf : ContDiffAt ℝ 2 f x := hW2 (t,x) hq
  let psi : E → ℝ := fun y => f y-eps*‖y‖^2
  have hpsi : ContDiffAt ℝ 2 psi x := hf.sub (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt)
  have hp : (complexHessian e (fun j => Complex.I • e j) psi x).PosDef := by
    apply complexHessian_posDef_of_paired_positive_two e hpsi
    intro v hv
    have hh := hmargin (t,x) hq v hv
    simp only [Q,N,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,pairedBilinearForm_apply,realHessian_norm_square,hI] at hh
    change 0 < realHessian f x v v+realHessian f x (Complex.I • v) (Complex.I • v) -
      eps*(2*inner ℝ v v+2*inner ℝ (Complex.I • v) (Complex.I • v)) at hh
    dsimp only [psi]
    rw [realHessian_sub_at hf (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt),
      realHessian_const_mul]
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,realHessian_norm_square]
    nlinarith only [hh]
  have he : complexHessian e (fun j => Complex.I • e j) psi x =
      complexHessian e (fun j => Complex.I • e j) f x -
        (eps : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    dsimp only [psi]
    have hefun : (fun y : E => f y-eps*‖y‖^2) = (fun y => f y+(-eps)*‖y‖^2) := by
      funext y
      ring
    rw [hefun,complexHessian_add_at hf (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt),
      complexHessian_const_mul_at (contDiff_norm_sq ℝ).contDiffAt,
      norm_square_complexHessian e (fun j => Complex.I • e j) hab]
    simp only [Complex.ofReal_neg,neg_smul,sub_eq_add_neg]
  refine ⟨by rwa [he] at hp,?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    simp
  · have hh := hmargin (t,x) hq v hv
    simp only [Q,N,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,pairedBilinearForm_apply,realHessian_norm_square,hI,
      real_inner_self_eq_norm_sq,norm_smul,Complex.norm_I,one_mul] at hh
    nlinarith only [hh]

end
end PowerConvexity
