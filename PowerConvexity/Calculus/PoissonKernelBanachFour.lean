import PowerConvexity.Calculus.PoissonIntegralFour
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # The actual Poisson kernel as a smooth map into C(unit sphere).
Its denominator is an explicit polynomial with values in the complete
normed algebra of continuous sphere functions. It is a unit at every
interior point. Banach-algebra inversion gives all derivative orders.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "F" => DeGiorgi.AmbientSpace (2+2)
local notation "S" => sphere (0 : F) 1

def unitSphereInnerLinearFour : F →ₗ[ℝ] C(S,ℝ) where
  toFun x := ⟨fun xi => inner ℝ (xi : F) x,by fun_prop⟩
  map_add' x y := by
    ext xi
    change inner ℝ (xi : F) (x+y) = inner ℝ (xi : F) x+inner ℝ (xi : F) y
    exact inner_add_right _ _ _
  map_smul' c x := by
    ext xi
    change inner ℝ (xi : F) (c • x) = c*inner ℝ (xi : F) x
    exact real_inner_smul_right _ _ _

def unitSphereInnerCLMFour : F →L[ℝ] C(S,ℝ) :=
  unitSphereInnerLinearFour.toContinuousLinearMap

def poissonDenominatorMapFour (x : F) : C(S,ℝ) :=
  (1 : C(S,ℝ)) + ‖x‖^2 • (1 : C(S,ℝ)) - (2 : ℝ) • unitSphereInnerCLMFour x

theorem poissonDenominatorMapFour_apply (x : F) (xi : S) :
    poissonDenominatorMapFour x xi = ‖x-(xi : F)‖^2 := by
  have hn : ‖(xi : F)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using xi.property
  change 1+‖x‖^2*1-2*inner ℝ (xi : F) x = ‖x-(xi : F)‖^2
  rw [norm_sub_sq_real,hn,real_inner_comm]
  ring

theorem poissonDenominatorMapFour_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n poissonDenominatorMapFour :=
  (contDiff_const.add ((contDiff_norm_sq ℝ).smul contDiff_const)).sub
    (unitSphereInnerCLMFour.contDiff.const_smul (2 : ℝ))

theorem poissonDenominatorMapFour_isUnit {x : F} (hx : x ∈ ball (0 : F) 1) :
    IsUnit (poissonDenominatorMapFour x) := by
  apply (poissonDenominatorMapFour x).isUnit_iff_forall_ne_zero.mpr
  intro xi
  rw [poissonDenominatorMapFour_apply]
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (unitBall_point_ne_unitSphere_four hx xi)))

def poissonKernelMapFour (x : F) : C(S,ℝ) :=
  (1-‖x‖^2) • (Ring.inverse (poissonDenominatorMapFour x))^2

theorem poissonKernelMapFour_apply {x : F} (hx : x ∈ ball (0 : F) 1) (xi : S) :
    poissonKernelMapFour x xi = poissonKernelFour xi x := by
  have hunit := poissonDenominatorMapFour_isUnit hx
  have hne : ‖x-(xi : F)‖^2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (unitBall_point_ne_unitSphere_four hx xi)))
  have he := congrArg (fun f : C(S,ℝ) => f xi)
    (Ring.inverse_mul_cancel (poissonDenominatorMapFour x) hunit)
  have hinv : (Ring.inverse (poissonDenominatorMapFour x)) xi = (‖x-(xi : F)‖^2)⁻¹ := by
    rw [inv_eq_one_div]
    apply (eq_div_iff hne).mpr
    simpa only [ContinuousMap.mul_apply,ContinuousMap.one_apply,poissonDenominatorMapFour_apply] using he
  simp only [poissonKernelMapFour,ContinuousMap.smul_apply,ContinuousMap.pow_apply,smul_eq_mul,hinv,
    poissonKernelFour,div_eq_mul_inv,inv_pow]

theorem poissonKernelMapFour_contDiffAt {x : F} (hx : x ∈ ball (0 : F) 1) (n : ℕ∞ω) :
    ContDiffAt ℝ n poissonKernelMapFour x := by
  have hunit := poissonDenominatorMapFour_isUnit hx
  have hi : ContDiffAt ℝ n Ring.inverse (poissonDenominatorMapFour x) := by
    simpa only [IsUnit.unit_spec] using (contDiffAt_ringInverse ℝ (n := n) hunit.unit)
  exact (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).smul
    ((hi.comp x (poissonDenominatorMapFour_contDiff n).contDiffAt).pow 2)

end PowerConvexity
