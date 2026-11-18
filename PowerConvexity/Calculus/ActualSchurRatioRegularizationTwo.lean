import PowerConvexity.Algebra.QuotientRegularizationTwo
import PowerConvexity.Calculus.ModifiedTraceDetRatioTwo
import PowerConvexity.Calculus.MatrixQuotientRatioHessianBridgeTwo

/-! # The regularized actual Schur field represents the previously audited F_e -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def regularizedModifiedSchurTwo (a b : Fin 2 → E) (u : E → ℝ) (e : ℝ)
    (x : E) : Matrix (Fin 2) (Fin 2) ℂ := modifiedSchur a b u x+(e:ℂ) • modifiedA a b u x

theorem modifiedTraceRatioRegularizedTwo_eq_matrixQuotient
    (a b : Fin 2 → E) (u : E → ℝ) (e : ℝ) {x : E} (hx : u x < 0)
    (hpos : (complexHessian a b u x).PosDef) :
    modifiedTraceRatioRegularizedTwo a b u e x =
      matrixQuotientRatioTwo (regularizedModifiedSchurTwo a b u e) (modifiedA a b u) x := by
  have hA : IsUnit (modifiedA a b u x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (modifiedA_posDef a b hx hpos).det_pos)
  have hh := matrix_quotient_regularized_ratio (modifiedSchur a b u x) (modifiedA a b u x) hA e
  simpa only [modifiedTraceRatioRegularizedTwo,matrixQuotientRatioTwo,regularizedModifiedSchurTwo,
    modifiedTraceTwo,modifiedDetTwo,modifiedK] using hh.symm

theorem modifiedTraceRatioRegularizedTwo_eventually_eq_matrixQuotient
    (a b : Fin 2 → E) {u : E → ℝ} (e : ℝ) {U : Set E} (hU : IsOpen U)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U) :
    modifiedTraceRatioRegularizedTwo a b u e =ᶠ[𝓝 x]
      matrixQuotientRatioTwo (regularizedModifiedSchurTwo a b u e) (modifiedA a b u) := by
  filter_upwards [hU.mem_nhds hx] with y hy
  exact modifiedTraceRatioRegularizedTwo_eq_matrixQuotient a b u e (hneg y hy) (hpos y hy)

theorem modifiedTraceRatioRegularizedTwo_realHessian_eq_matrixQuotient
    (a b : Fin 2 → E) {u : E → ℝ} (e : ℝ) {U : Set E} (hU : IsOpen U)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U) :
    realHessian (modifiedTraceRatioRegularizedTwo a b u e) x =
      realHessian (matrixQuotientRatioTwo (regularizedModifiedSchurTwo a b u e) (modifiedA a b u)) x :=
  (modifiedTraceRatioRegularizedTwo_eventually_eq_matrixQuotient a b e hU hneg hpos hx).fderiv.fderiv_eq

theorem modifiedTraceRatioRegularizedTwo_fderiv_eq_matrixQuotient
    (a b : Fin 2 → E) {u : E → ℝ} (e : ℝ) {U : Set E} (hU : IsOpen U)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U) :
    fderiv ℝ (modifiedTraceRatioRegularizedTwo a b u e) x =
      fderiv ℝ (matrixQuotientRatioTwo (regularizedModifiedSchurTwo a b u e) (modifiedA a b u)) x :=
  (modifiedTraceRatioRegularizedTwo_eventually_eq_matrixQuotient a b e hU hneg hpos hx).fderiv_eq

theorem regularizedModifiedSchurTwo_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hpos : (complexHessian a b u x).PosDef) (e : ℝ) (i j : Fin 2) :
    ContDiffAt ℝ 2 (fun y => regularizedModifiedSchurTwo a b u e y i j) x := by
  exact (modifiedSchur_contDiffAt_two hu hx a b hpos i j).add
    (contDiffAt_const.mul (modifiedA_contDiffAt_two hu hx a b i j))

end PowerConvexity
