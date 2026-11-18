import PowerConvexity.Calculus.NestedDomainComparisonTwo
import CHS.Calculus.AffinePullback

/-! # The exact physical homothety of a classical constant-density solution -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def dilatedPotential (r : ℝ) (u : E → ℝ) (x : E) : ℝ :=
  r^2*u (r⁻¹ • x)

def dilatedDomain (r : ℝ) (U : Set E) : Set E := (fun x => r⁻¹ • x) ⁻¹' U

theorem dilatedPotential_contDiffAt {u : E → ℝ} {x : E} (r : ℝ) {k : ℕ∞ω}
    (hu : ContDiffAt ℝ k u (r⁻¹ • x)) : ContDiffAt ℝ k (dilatedPotential r u) x :=
  contDiffAt_const.mul (hu.comp x (contDiffAt_const.smul contDiffAt_id))

theorem dilatedPotential_realHessian {u : E → ℝ} {x : E} {r : ℝ} (hr : r ≠ 0)
    (hu : ContDiffAt ℝ 2 u (r⁻¹ • x)) (v w : E) :
    realHessian (dilatedPotential r u) x v w = realHessian u (r⁻¹ • x) v w := by
  unfold dilatedPotential
  rw [realHessian_const_mul]
  have hh := realHessian_comp_affine (r⁻¹ • ContinuousLinearMap.id ℝ E) (0 : E)
    (by simpa using hu) v w
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,zero_add,
    map_smul,_root_.smul_apply,smul_eq_mul] at hh
  change r^2*realHessian (fun y => u (r⁻¹ • y)) x v w = _
  rw [hh]
  field_simp [hr]
  <;> ring

theorem dilatedPotential_complexHessian {u : E → ℝ} {x : E} {r : ℝ} (hr : r ≠ 0)
    (hu : ContDiffAt ℝ 2 u (r⁻¹ • x)) (a b : Fin 2 → E) :
    complexHessian a b (dilatedPotential r u) x = complexHessian a b u (r⁻¹ • x) := by
  ext i j
  rw [complexHessian_real_entry (dilatedPotential_contDiffAt r hu),complexHessian_real_entry hu]
  simp only [dilatedPotential_realHessian hr hu]

theorem dilatedDomain_isOpen {U : Set E} (hU : IsOpen U) (r : ℝ) :
    IsOpen (dilatedDomain r U) := hU.preimage (continuous_const.smul continuous_id)

theorem dilatedDomain_closure {U : Set E} {r : ℝ} (hr : r ≠ 0) :
    closure (dilatedDomain r U) = (fun x => r⁻¹ • x) ⁻¹' closure U := by
  exact (Homeomorph.preimage_closure (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr)) U).symm

theorem dilatedDomain_frontier {U : Set E} {r : ℝ} (hr : r ≠ 0) :
    frontier (dilatedDomain r U) = (fun x => r⁻¹ • x) ⁻¹' frontier U := by
  exact (Homeomorph.preimage_frontier (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr)) U).symm

theorem dilatedDomain_isCompact_closure {U : Set E} (hK : IsCompact (closure U))
    {r : ℝ} (hr : r ≠ 0) : IsCompact (closure (dilatedDomain r U)) := by
  rw [dilatedDomain_closure hr]
  exact (Homeomorph.isCompact_preimage (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr))).mpr hK

theorem dilatedPotential_continuousOn_closure {U : Set E} {u : E → ℝ}
    (huc : ContinuousOn u (closure U)) {r : ℝ} (hr : r ≠ 0) :
    ContinuousOn (dilatedPotential r u) (closure (dilatedDomain r U)) := by
  apply continuousOn_const.mul
  apply huc.comp (continuous_const.smul continuous_id).continuousOn
  intro x hx
  exact (show x ∈ (fun x => r⁻¹ • x) ⁻¹' closure U by rwa [← dilatedDomain_closure hr])

theorem dilatedPotential_contDiffOn {U : Set E} {u : E → ℝ} {k : ℕ∞ω}
    (hu : ContDiffOn ℝ k u U) (r : ℝ) :
    ContDiffOn ℝ k (dilatedPotential r u) (dilatedDomain r U) :=
  contDiffOn_const.mul (hu.comp (contDiffOn_const.smul contDiffOn_id) (fun _ hx => hx))

theorem dilatedPotential_zero_boundary {U : Set E} {u : E → ℝ}
    (hb : ∀ x ∈ frontier U, u x = 0) {r : ℝ} (hr : r ≠ 0) :
    ∀ x ∈ frontier (dilatedDomain r U), dilatedPotential r u x = 0 := by
  intro x hx
  rw [dilatedDomain_frontier hr] at hx
  simp only [dilatedPotential,hb _ hx,mul_zero]

theorem dilatedPotential_zeroExtension (r : ℝ) (U : Set E) (u : E → ℝ) (x : E) :
    (dilatedDomain r U).indicator (dilatedPotential r u) x = r^2*U.indicator u (r⁻¹ • x) := by
  classical
  by_cases hx : r⁻¹ • x ∈ U
  · rw [Set.indicator_of_mem (show x ∈ dilatedDomain r U from hx),Set.indicator_of_mem hx]
    rfl
  · rw [Set.indicator_of_notMem (show x ∉ dilatedDomain r U from hx),Set.indicator_of_notMem hx,mul_zero]

end PowerConvexity
