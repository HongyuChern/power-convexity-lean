import PowerConvexity.Analysis.CompactPositiveBilinearMargin
import PowerConvexity.Calculus.PairedBilinearContinuity
import PowerConvexity.Calculus.ComplexLeviPairPositiveTwo
import PowerConvexity.Calculus.PairedLeviMatrixTwo
import PowerConvexity.Calculus.QuadraticBallPotential

/-! # A uniform scalar lower margin for an actual strict psh potential

The margin is obtained from compactness and openness of positive actual paired
Hessians. It is independent of any unknown Dirichlet solution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

theorem compact_strictPsh_has_uniform_scalar_margin_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {K : Set E} (hK : IsCompact K) {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hpos : ∀ x ∈ K, (complexHessian e (fun j => Complex.I • e j) w x).PosDef) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ x ∈ K,
      (complexHessian e (fun j => Complex.I • e j) w x-
        (eps : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosDef := by
  letI : FiniteDimensional ℂ E := e.finiteDimensional_of_finite
  let I : E →L[ℝ] E := (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  have hI (v : E) : I v = Complex.I • v := rfl
  let Q := fun x => pairedBilinearForm I (realHessian w x)
  let N := pairedBilinearForm I (realHessian (fun y : E => ‖y‖^2) 0)
  have hHc : Continuous (realHessian w) := continuous_iff_continuousAt.mpr (fun _ =>
    ((hw.contDiffAt.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt)
  have hQc : Continuous Q := (continuous_pairedBilinearForm I).comp hHc
  have hQpos (x : E) (hx : x ∈ K) (v : E) (hv : v ≠ 0) : 0 < Q x v v := by
    simpa only [Q,pairedBilinearForm_apply,hI] using
      complexHessian_posDef_paired_positive_two e hw.contDiffAt (hpos x hx) v hv
  obtain ⟨eps,heps,hmargin⟩ := compact_positive_bilinear_subtraction_margin hK Q hQc N hQpos
  let psi : E → ℝ := fun y => w y-eps*‖y‖^2
  have hpsi : ContDiff ℝ 2 psi := hw.sub (contDiff_const.mul (contDiff_norm_sq ℝ))
  refine ⟨eps,heps,?_⟩
  intro x hx
  have hp : (complexHessian e (fun j => Complex.I • e j) psi x).PosDef := by
    apply complexHessian_posDef_of_paired_positive_two e hpsi.contDiffAt
    intro v hv
    have hh := hmargin x hx v hv
    simp only [Q,N,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,pairedBilinearForm_apply,realHessian_norm_square,hI] at hh
    dsimp only [psi]
    rw [realHessian_sub_at hw.contDiffAt (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt),
      realHessian_const_mul]
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,realHessian_norm_square]
    nlinarith only [hh]
  have he : complexHessian e (fun j => Complex.I • e j) psi x =
      complexHessian e (fun j => Complex.I • e j) w x-
        (eps : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    dsimp only [psi]
    have hefun : (fun y : E => w y-eps*‖y‖^2) = (fun y => w y+(-eps)*‖y‖^2) := by
      funext y
      ring
    rw [hefun,complexHessian_add_at hw.contDiffAt (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt),
      complexHessian_const_mul_at (contDiff_norm_sq ℝ).contDiffAt,
      norm_square_complexHessian e (fun j => Complex.I • e j) hab]
    simp only [Complex.ofReal_neg,neg_smul,sub_eq_add_neg]
  rwa [he] at hp

end PowerConvexity
