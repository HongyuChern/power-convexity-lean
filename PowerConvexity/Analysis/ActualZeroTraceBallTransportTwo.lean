import PowerConvexity.Analysis.ActualWeakL2ScalingTwo

/-! # Actual transport of zero-trace tests to a physical ball.
The H01 approximation proof follows the locked BallScaling construction,
with project proofs of inverse geometry, norm scaling and the chain rule.
No private declaration is referenced by the public project proof.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_inverse_affine_preimage_unitBall_two {x₀ : E} {R : ℝ} (hR : 0 < R) :
    (fun x : E => R⁻¹ • (x-x₀)) ⁻¹' ball (0 : E) 1 = ball x₀ R := by
  ext x
  simp only [mem_preimage,mem_ball,dist_zero_right,dist_eq_norm,sub_zero,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR)]
  constructor
  · intro hx
    have hh := mul_lt_mul_of_pos_left hx hR
    simpa only [← mul_assoc,mul_inv_cancel₀ hR.ne',one_mul,mul_one] using hh
  · intro hx
    have hh := mul_lt_mul_of_pos_left hx (inv_pos.mpr hR)
    simpa only [inv_mul_cancel₀ hR.ne'] using hh

theorem actual_eLpNorm_transport_from_unitBall_two {x₀ : E} {R : ℝ} {f : E → ℝ}
    (hR : 0 < R) :
    eLpNorm (transportFromUnitBall (x₀ := x₀) (R := R) f) 2 (volume.restrict (ball x₀ R)) =
      ENNReal.ofReal (R^2)*eLpNorm f 2 (volume.restrict (ball (0 : E) 1)) := by
  have hh := eLpNorm_rescale_to_unitBall (d := 2+2) (x₀ := x₀) (R := R)
    (f := transportFromUnitBall (x₀ := x₀) (R := R) f) hR
    (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
  have he : (fun z => transportFromUnitBall (x₀ := x₀) (R := R) f (x₀+R • z)) = f := by
    funext z
    simp only [transportFromUnitBall,add_sub_cancel_left,inv_smul_smul₀ hR.ne']
  rw [he] at hh
  norm_num only [Nat.cast_add,Nat.cast_ofNat,ENNReal.toReal_ofNat,show (2+2 : ℝ)/2=2 by norm_num,
    Real.rpow_two] at hh
  have hcoef : ENNReal.ofReal (R^2)*ENNReal.ofReal ((R⁻¹)^2) = 1 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg R),← mul_pow,mul_inv_cancel₀ hR.ne']
    norm_num
  rw [hh,← mul_assoc,hcoef,one_mul]

theorem actual_fderiv_transport_from_unitBall_apply_two {x₀ : E} {R : ℝ} (_hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin (2+2)) :
    ∀ x : E, (fderiv ℝ (transportFromUnitBall (x₀ := x₀) (R := R) u) x)
      (EuclideanSpace.single i 1) =
      R⁻¹*(fderiv ℝ u (R⁻¹ • (x-x₀))) (EuclideanSpace.single i 1) := by
  intro x
  let S : E → E := fun y => R⁻¹ • (y-x₀)
  have hS : HasFDerivAt S (R⁻¹ • ContinuousLinearMap.id ℝ E) x := by
    have hh := (hasFDerivAt_id (𝕜 := ℝ) x).sub (hasFDerivAt_const (𝕜 := ℝ) x₀ x)
    simp only [sub_zero] at hh
    exact hh.const_smul R⁻¹
  have hu_at := ((hu.differentiable (by simp)).differentiableAt (x := S x)).hasFDerivAt
  have hc := hu_at.comp x hS
  rw [show transportFromUnitBall (x₀ := x₀) (R := R) u = u ∘ S from rfl,hc.fderiv]
  simp [S,smul_apply,smul_eq_mul]

theorem actual_memH01_transport_from_unitBall_two
    {x₀ : E} {R : ℝ} {u : E → ℝ}
    (hR : 0 < R)
    (hu : MemW01p 2 u (Metric.ball (0 : E) 1)) :
    MemW01p 2 (DeGiorgi.transportFromUnitBall (d := 2+2) (x₀ := x₀) (R := R) u)
      (Metric.ball x₀ R) := by
  rcases hu with ⟨_, hw, φ, hφ_smooth, hφ_compact, hφ_sub, hφ_fun, hφ_grad⟩
  let ψ : ℕ → E → ℝ := fun n =>
    DeGiorgi.transportFromUnitBall (d := 2+2) (x₀ := x₀) (R := R) (φ n)
  refine ⟨(hw.transportFromUnitBall (d := 2+2) (x₀ := x₀) (R := R) hR).memW1p,
    hw.transportFromUnitBall (d := 2+2) (x₀ := x₀) (R := R) hR, ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    let h : ContDiff ℝ (⊤ : ℕ∞) (ψ n) :=
      (hφ_smooth n).comp
        ((contDiff_const_smul R⁻¹).comp (contDiff_id.sub contDiff_const))
    exact h
  · intro n
    let h : E ≃ₜ E := (Homeomorph.addRight (-x₀)).trans
      (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne'))
    exact (show ψ n = φ n ∘ h from by
      ext x
      have hx : h x = R⁻¹ • (x - x₀) := by
        ext i
        simp [h, Homeomorph.addRight, Homeomorph.smulOfNeZero, sub_eq_add_neg, smul_add]
      simpa [ψ, DeGiorgi.transportFromUnitBall] using congrArg (φ n) hx.symm) ▸
      (hφ_compact n).comp_homeomorph h
  · intro n x hx
    have hcont : Continuous (fun x : E => R⁻¹ • (x - x₀)) :=
      (continuous_const_smul R⁻¹).comp (continuous_id.sub continuous_const)
    have hx' := hφ_sub n ((tsupport_comp_subset_preimage _ hcont) hx)
    have : x ∈ (fun x : E => R⁻¹ • (x - x₀)) ⁻¹' Metric.ball (0 : E) 1 := hx'
    simpa [actual_inverse_affine_preimage_unitBall_two (x₀ := x₀) hR] using this
  · let C : ENNReal := ENNReal.ofReal (R^2)
    have hEq :
        (fun n =>
          eLpNorm (fun x => ψ n x -
              DeGiorgi.transportFromUnitBall (d := 2+2) (x₀ := x₀) (R := R) u x) 2
            (volume.restrict (Metric.ball x₀ R))) =
          (fun n =>
            C * eLpNorm (fun x => φ n x - u x) 2
              (volume.restrict (Metric.ball (0 : E) 1))) := by
      funext n
      have hfun :
          (fun x => ψ n x -
              DeGiorgi.transportFromUnitBall (d := 2+2) (x₀ := x₀) (R := R) u x) =
            DeGiorgi.transportFromUnitBall (d := 2+2) (x₀ := x₀) (R := R)
              (fun x => φ n x - u x) := by
        ext x
        simp [ψ, DeGiorgi.transportFromUnitBall]
      rw [hfun, actual_eLpNorm_transport_from_unitBall_two (x₀ := x₀) (R := R)
        (f := fun x => φ n x - u x) hR]
    rw [hEq]
    have hscaled :
        Filter.Tendsto
          (fun n =>
            C * eLpNorm (fun x => φ n x - u x) 2
              (volume.restrict (Metric.ball (0 : E) 1)))
          Filter.atTop (nhds (C * 0)) :=
      ENNReal.Tendsto.const_mul hφ_fun (Or.inr ENNReal.coe_ne_top)
    simpa using hscaled
  · intro i
    let C : ENNReal := ENNReal.ofReal (R^2)
    let C' : ENNReal := ‖R⁻¹‖ₑ
    have hEq :
        (fun n =>
          eLpNorm
            (fun x =>
              (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) -
                (hw.transportFromUnitBall (d := 2+2) (x₀ := x₀) (R := R) hR).weakGrad x i)
            2 (volume.restrict (Metric.ball x₀ R))) =
          (fun n =>
            C' * (C * eLpNorm
              (fun x =>
                (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              2 (volume.restrict (Metric.ball (0 : E) 1)))) := by
      funext n
      have hfun :
          (fun x =>
            (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) -
              (hw.transportFromUnitBall (d := 2+2) (x₀ := x₀) (R := R) hR).weakGrad x i) =
            R⁻¹ •
              DeGiorgi.transportFromUnitBall (d := 2+2) (x₀ := x₀) (R := R)
                (fun x =>
                  (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) := by
        ext x
        rw [actual_fderiv_transport_from_unitBall_apply_two (x₀ := x₀) (R := R)
          (u := φ n) hR (hφ_smooth n) i x]
        simp [MemW1pWitness.transportFromUnitBall, DeGiorgi.transportFromUnitBall,
          Pi.smul_apply, smul_eq_mul]
        ring
      rw [hfun, eLpNorm_const_smul]
      rw [actual_eLpNorm_transport_from_unitBall_two (x₀ := x₀) (R := R)
        (f := fun x =>
          (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
        hR]
    rw [hEq]
    have hscaled :
        Filter.Tendsto
          (fun n =>
            C' * (C * eLpNorm
              (fun x =>
                (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              2 (volume.restrict (Metric.ball (0 : E) 1))))
          Filter.atTop (nhds (C' * (C * 0))) :=
      ENNReal.Tendsto.const_mul
        (ENNReal.Tendsto.const_mul (hφ_grad i) (Or.inr ENNReal.coe_ne_top))
        (Or.inr ENNReal.coe_ne_top)
    simpa [mul_assoc] using hscaled

end PowerConvexity
