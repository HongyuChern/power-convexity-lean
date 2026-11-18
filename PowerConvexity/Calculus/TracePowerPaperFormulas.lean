import PowerConvexity.Calculus.TracePowerRoot
import PowerConvexity.Algebra.DiagonalTracePowers

/-! # Literal positive-branch B3-4 and B4-1 differential formulas -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus

theorem trace_root_first_coefficient {T p : ℝ} (hT : 0 < T) (hp : p ≠ 0) :
    (p⁻¹ * T^(p⁻¹-1)) * p = (T^((p-1)/p))⁻¹ := by
  have he : p⁻¹-1 = -((p-1)/p) := by field_simp; ring
  rw [he, Real.rpow_neg hT.le]
  field_simp

theorem trace_root_second_coefficient {T p : ℝ} (hT : 0 < T) (hp : p ≠ 0) :
    (p⁻¹ * (p⁻¹-1) * T^(p⁻¹-2)) * p * p = -(p-1) / T^((2*p-1)/p) := by
  have he : p⁻¹-2 = -((2*p-1)/p) := by field_simp; ring
  rw [he, Real.rpow_neg hT.le]
  field_simp
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tracePowerRoot_dz {K : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hK : ∀ i j, ContDiffOn ℝ 2 (fun y => K y i j) U)
    {x : E} (hx : x ∈ U) (n : ℕ)
    (hreal : ∀ y ∈ U, (K y ^ (n+1)).trace.im = 0)
    (hpos : 0 < (K x ^ (n+1)).trace.re) (a b : E) :
    dz a b (fun y => (tracePowerRoot K (n+1) y : ℂ)) x =
      (K x ^ n * matrixDZ a b K x).trace /
        (((K x ^ (n+1)).trace.re ^ ((n:ℝ)/(n+1)) : ℝ) : ℂ) := by
  have hKx := fun i j => (hK i j).contDiffAt (hU.mem_nhds hx)
  have hKd : MatrixDifferentiableAt K x := fun i j => (hKx i j).differentiableAt (by norm_num)
  have he : (fun y => ((K y ^ (n+1)).trace.re : ℂ)) =ᶠ[𝓝 x]
      (fun y => (K y ^ (n+1)).trace) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact Complex.ext (by simp) (by simpa using (hreal y hy).symm)
  have h := dz_real_rpow
    ((tracePower_real_contDiffAt hKx (n+1)).differentiableAt (by norm_num))
    (ne_of_gt hpos) (1/((n+1:ℕ):ℝ)) a b
  rw [dz_congr_nhds he a b, dz_trace_power hKd] at h
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, one_div] at h
  have hp : (n:ℝ)+1 ≠ 0 := by positivity
  have hc := trace_root_first_coefficient hpos hp
  simp only [add_sub_cancel_right] at hc
  have hcC : (((((n:ℝ)+1)⁻¹ * (K x^(n+1)).trace.re^(((n:ℝ)+1)⁻¹-1)) : ℝ):ℂ) *
      ((n:ℂ)+1) = (((K x^(n+1)).trace.re^((n:ℝ)/(n+1))) : ℝ)⁻¹ := by
    exact_mod_cast hc
  simp only [tracePowerRoot, Nat.cast_add, Nat.cast_one, one_div]
  rw [h, ← mul_assoc, hcC]
  simp only [Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem paper_B4_1_tracePowerRoot {K : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hK : ∀ i j, ContDiffOn ℝ 2 (fun y => K y i j) U)
    {x : E} (hx : x ∈ U) (n : ℕ)
    (hreal : ∀ y ∈ U, (K y ^ (n+1)).trace.im = 0)
    (hpos : 0 < (K x ^ (n+1)).trace.re) (a b c d : E) :
    let T : ℝ := (K x^(n+1)).trace.re
    dz c d (dz a b (fun y => (tracePowerRoot K (n+1) y : ℂ))) x =
      (K x ^ n * matrixDZ c d (matrixDZ a b K) x).trace / ((T ^ ((n:ℝ)/(n+1)) : ℝ) : ℂ) +
      (∑ j ∈ Finset.range n,
        (K x ^ j * matrixDZ c d K x * K x ^ (n-1-j) * matrixDZ a b K x).trace) /
          ((T ^ ((n:ℝ)/(n+1)) : ℝ) : ℂ) -
      (n:ℂ) * (K x ^ n * matrixDZ a b K x).trace * (K x ^ n * matrixDZ c d K x).trace /
        ((T ^ ((2*((n:ℝ)+1)-1)/((n:ℝ)+1)) : ℝ) : ℂ) := by
  let T : ℝ := (K x^(n+1)).trace.re
  let p : ℝ := (n:ℝ)+1
  have hp : p ≠ 0 := by dsimp [p]; positivity
  have h1 : (((p⁻¹*T^(p⁻¹-1) : ℝ):ℂ) * (p:ℂ)) = ((T^((p-1)/p))⁻¹ : ℝ) := by
    exact_mod_cast trace_root_first_coefficient hpos hp
  have h2 : (((p⁻¹*(p⁻¹-1)*T^(p⁻¹-2) : ℝ):ℂ) * (p:ℂ) * (p:ℂ)) =
      ((-(p-1)/T^((2*p-1)/p) : ℝ):ℂ) := by
    exact_mod_cast trace_root_second_coefficient hpos hp
  have h := tracePowerRoot_dz_mixed hU hK hx n hreal hpos a b c d
  change _ = ((p⁻¹*T^(p⁻¹-1) : ℝ):ℂ) * (p:ℂ) * _ +
    ((p⁻¹*(p⁻¹-1)*T^(p⁻¹-2) : ℝ):ℂ) * ((p:ℂ)*_) * ((p:ℂ)*_) at h
  rw [h]
  calc
    _ = (((p⁻¹*T^(p⁻¹-1) : ℝ):ℂ) * (p:ℂ)) *
        ((K x ^ n * matrixDZ c d (matrixDZ a b K) x).trace +
          ∑ j ∈ Finset.range n,
            (K x ^ j * matrixDZ c d K x * K x ^ (n-1-j) * matrixDZ a b K x).trace) +
        (((p⁻¹*(p⁻¹-1)*T^(p⁻¹-2) : ℝ):ℂ) * (p:ℂ) * (p:ℂ)) *
          (K x ^ n * matrixDZ a b K x).trace * (K x ^ n * matrixDZ c d K x).trace := by ring
    _ = _ := by
      rw [h1, h2]
      dsimp only [p, T]
      push_cast
      simp only [add_sub_cancel_right, Complex.ofReal_inv, Complex.ofReal_div,
        Complex.ofReal_neg, Complex.ofReal_natCast, div_eq_mul_inv, Complex.ofReal_mul]
      ring

end PowerConvexity
