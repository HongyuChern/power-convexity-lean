import PowerConvexity.Calculus.RealHessianRules
import Mathlib.Topology.Order.Compact

/-! # Classical comparison in the presence of a gradient term -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positivity of a linear contraction on nonnegative quadratic forms. -/
def HessianPositive (L : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ H, (∀ v : E, 0 ≤ H v v) → 0 ≤ L H

theorem hessian_contraction_mono
    {L : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ} (hL : HessianPositive L)
    {H K : E →L[ℝ] E →L[ℝ] ℝ} (hHK : ∀ v, H v v ≤ K v v) : L H ≤ L K := by
  have h := hL (K - H) (fun v => sub_nonneg.mpr (hHK v))
  have he : L (K - H) = L K - L H := map_sub L K H
  rw [he] at h
  exact sub_nonneg.mp h

/-- The strict barrier excludes a negative local minimum of w-epsilon*v.
Both the first- and second-order jets are the actual Frechet derivatives. -/
theorem no_negative_localMin_gradient_barrier {w v : E → ℝ} {x : E}
    (hw : ContDiffAt ℝ 2 w x) (hv : ContDiffAt ℝ 2 v x)
    {L : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ} (hL : HessianPositive L)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hsub : L (realHessian w x) ≤ C * (w x + ‖fderiv ℝ w x‖))
    (hbar : C * (v x + ‖fderiv ℝ v x‖) < L (realHessian v x))
    (hneg : w x < ε * v x)
    (hm : IsLocalMin (fun y => w y - ε * v y) x) : False := by
  have hev : ContDiffAt ℝ 2 (fun y => ε * v y) x := contDiffAt_const.mul hv
  have hD := fderiv_eq_of_isLocalMin_sub (hw.differentiableAt (by norm_num))
    (hev.differentiableAt (by norm_num)) hm
  rw [fderiv_const_mul (hv.differentiableAt (by norm_num))] at hD
  have hnorm : ‖fderiv ℝ w x‖ = ε * ‖fderiv ℝ v x‖ := by
    rw [hD, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have hH := hessian_contraction_mono hL (realHessian_le_of_isLocalMin_sub hw hev hm)
  rw [realHessian_const_mul_at hv, map_smul, smul_eq_mul] at hH
  rw [hnorm] at hsub
  have hle : C * (w x + ε * ‖fderiv ℝ v x‖) ≤
      ε * (C * (v x + ‖fderiv ℝ v x‖)) := by nlinarith
  have hlt := mul_lt_mul_of_pos_left hbar hε
  linarith

/-- A compact-set comparison theorem. The boundary input is stated on
K minus its interior, so it applies directly to a closed annulus. -/
theorem compact_gradient_barrier_comparison {K : Set E} (hK : IsCompact K)
    {w v : E → ℝ} (hwc : ContinuousOn w K) (hvc : ContinuousOn v K)
    (hw : ∀ x ∈ interior K, ContDiffAt ℝ 2 w x)
    (hv : ∀ x ∈ interior K, ContDiffAt ℝ 2 v x)
    (L : E → (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ x ∈ interior K, HessianPositive (L x))
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hsub : ∀ x ∈ interior K,
      L x (realHessian w x) ≤ C * (w x + ‖fderiv ℝ w x‖))
    (hbar : ∀ x ∈ interior K,
      C * (v x + ‖fderiv ℝ v x‖) < L x (realHessian v x))
    (hboundary : ∀ x ∈ K, x ∉ interior K → ε * v x ≤ w x) :
    ∀ x ∈ K, ε * v x ≤ w x := by
  intro x hx
  by_contra! hbad
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn ⟨x, hx⟩
    (hwc.sub ((continuousOn_const (c := ε)).mul hvc))
  have hyneg : w y < ε * v y := by
    have hh := hmin hx
    change w y - ε * v y ≤ w x - ε * v x at hh
    linarith
  have hyi : y ∈ interior K := by
    by_contra hni
    exact (not_lt_of_ge (hboundary y hy hni)) hyneg
  have hm := hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hyi)
  exact no_negative_localMin_gradient_barrier (hw y hyi) (hv y hyi) (hL y hyi)
    hC hε (hsub y hyi) (hbar y hyi) hyneg hm

end PowerConvexity
