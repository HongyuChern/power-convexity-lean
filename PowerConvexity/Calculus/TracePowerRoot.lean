import PowerConvexity.Calculus.TracePowers
import PowerConvexity.Calculus.PowerTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Actual first and second derivatives of the positive trace-power root -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dz_real_rpow {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (h0 : f x ≠ 0) (α : ℝ) (a b : E) :
    dz a b (fun y => ((f y ^ α : ℝ) : ℂ)) x =
      ((α * f x ^ (α-1) : ℝ) : ℂ) * dz a b (fun y => (f y : ℂ)) x := by
  have hd := hf.hasFDerivAt.rpow_const (p := α) (Or.inl h0)
  have h1 := complexGradient_real_entry hd.differentiableAt
    (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) 0
  have h2 := complexGradient_real_entry hf
    (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) 0
  change dz a b (fun y => ((f y ^ α : ℝ) : ℂ)) x = _ at h1
  change dz a b (fun y => (f y : ℂ)) x = _ at h2
  rw [h1, h2, hd.fderiv]
  simp only [smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem dz_mixed_real_rpow {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (h0 : f x ≠ 0) (α : ℝ) (a b c d : E) :
    dz c d (dz a b (fun y => ((f y ^ α : ℝ) : ℂ))) x =
      ((α * f x ^ (α-1) : ℝ) : ℂ) *
        dz c d (dz a b (fun y => (f y : ℂ))) x +
      ((α * (α-1) * f x ^ (α-2) : ℝ) : ℂ) *
        dz a b (fun y => (f y : ℂ)) x * dz c d (fun y => (f y : ℂ)) x := by
  have hf1 := hf.differentiableAt (by norm_num)
  have he : dz a b (fun y => ((f y ^ α : ℝ) : ℂ)) =ᶠ[𝓝 x]
      (fun y => ((α * f y ^ (α-1) : ℝ) : ℂ) * dz a b (fun z => (f z : ℂ)) y) := by
    filter_upwards [(hf.of_le (m := 1) (by norm_num)).eventually (by simp),
      hf.continuousAt.eventually_ne h0] with y hy hy0
    exact dz_real_rpow (hy.differentiableAt (by norm_num)) hy0 α a b
  have hR : DifferentiableAt ℝ (fun y => ((f y ^ (α-1) : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x (hf1.rpow_const (Or.inl h0))
  have hC : DifferentiableAt ℝ (fun y => ((α * f y ^ (α-1) : ℝ) : ℂ)) x := by
    exact Complex.ofRealCLM.differentiableAt.comp x
      ((differentiableAt_const α).fun_mul (hf1.rpow_const (Or.inl h0)))
  have hfc : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  have hD := (dz_contDiffAt_one hfc a b).differentiableAt (by norm_num)
  rw [dz_congr_nhds he c d, dz_mul_at hC hD c d]
  have hcoef : dz c d (fun y => ((α * f y ^ (α-1) : ℝ) : ℂ)) x =
      (α:ℂ) * (((α-1) * f x ^ (α-2) : ℝ) : ℂ) * dz c d (fun y => (f y:ℂ)) x := by
    simp only [Complex.ofReal_mul]
    rw [dz_mul_at (differentiableAt_const (α:ℂ)) hR c d, dz_const,
      zero_mul, zero_add, dz_real_rpow hf1 h0 (α-1) c d]
    rw [show α-1-1=α-2 by ring]
    simp only [Complex.ofReal_mul]
    ring
  rw [hcoef]
  simp only [Complex.ofReal_mul]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_power_contDiffAt {K : E → Matrix ι ι ℂ} {x : E} {k : ℕ∞ω}
    (hK : ∀ i j, ContDiffAt ℝ k (fun y => K y i j) x) (n : ℕ) :
    ∀ i j, ContDiffAt ℝ k (fun y => (K y ^ n) i j) x := by
  induction n with
  | zero => intro i j; simpa using (contDiffAt_const : ContDiffAt ℝ k (fun _ : E => (1 : Matrix ι ι ℂ) i j) x)
  | succ n ih => simpa only [pow_succ] using matrix_product_contDiffAt ih hK

noncomputable def tracePowerRoot (K : E → Matrix ι ι ℂ) (p : ℕ) (x : E) : ℝ :=
  ((K x ^ p).trace.re) ^ (1/(p:ℝ))

theorem tracePower_real_contDiffAt {K : E → Matrix ι ι ℂ} {x : E} {k : ℕ∞ω}
    (hK : ∀ i j, ContDiffAt ℝ k (fun y => K y i j) x) (n : ℕ) :
    ContDiffAt ℝ k (fun y => (K y ^ n).trace.re) x := by
  apply Complex.reCLM.contDiff.contDiffAt.comp x
  exact ContDiffAt.sum (fun i _ => matrix_power_contDiffAt hK n i i)

/-- B4-1 before cancellation of the scalar factors p. This already uses the
actual first and mixed second trace-power derivatives, not derivative data. -/
theorem tracePowerRoot_dz_mixed {K : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hK : ∀ i j, ContDiffOn ℝ 2 (fun y => K y i j) U)
    {x : E} (hx : x ∈ U) (n : ℕ)
    (hreal : ∀ y ∈ U, (K y ^ (n+1)).trace.im = 0)
    (hpos : 0 < (K x ^ (n+1)).trace.re) (a b c d : E) :
    let p : ℝ := n+1
    let T : ℝ := (K x ^ (n+1)).trace.re
    dz c d (dz a b (fun y => (tracePowerRoot K (n+1) y : ℂ))) x =
      ((p⁻¹ * T ^ (p⁻¹-1) : ℝ) : ℂ) * (p:ℂ) *
        ((K x ^ n * matrixDZ c d (matrixDZ a b K) x).trace +
          ∑ j ∈ Finset.range n,
            (K x ^ j * matrixDZ c d K x * K x ^ (n-1-j) * matrixDZ a b K x).trace) +
      ((p⁻¹ * (p⁻¹-1) * T ^ (p⁻¹-2) : ℝ) : ℂ) *
        ((p:ℂ) * (K x ^ n * matrixDZ a b K x).trace) *
        ((p:ℂ) * (K x ^ n * matrixDZ c d K x).trace) := by
  have hKx := fun i j => (hK i j).contDiffAt (hU.mem_nhds hx)
  have hKd : MatrixDifferentiableAt K x := fun i j => (hKx i j).differentiableAt (by norm_num)
  have he : (fun y => ((K y ^ (n+1)).trace.re : ℂ)) =ᶠ[𝓝 x]
      (fun y => (K y ^ (n+1)).trace) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact Complex.ext (by simp) (by simpa using (hreal y hy).symm)
  have h1 := dz_mixed_real_rpow (tracePower_real_contDiffAt hKx (n+1))
    (ne_of_gt hpos) (1/((n+1 : ℕ):ℝ)) a b c d
  have he1 := dz_congr_nhds he a b
  have he2 := dz_congr_nhds he c d
  have he12 : dz c d (dz a b (fun y => ((K y ^ (n+1)).trace.re : ℂ))) x =
      dz c d (dz a b (fun y => (K y ^ (n+1)).trace)) x := by
    exact dz_congr_nhds (he.eventuallyEq_nhds.mono fun y hy => dz_congr_nhds hy a b) c d
  rw [he1, he2, he12, dz_trace_power hKd, dz_trace_power hKd,
    dz_mixed_trace_power hU hK hx] at h1
  simpa [tracePowerRoot, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, one_div, mul_assoc] using h1

end PowerConvexity
