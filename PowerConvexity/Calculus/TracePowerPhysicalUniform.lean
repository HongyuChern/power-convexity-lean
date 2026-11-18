import PowerConvexity.Calculus.TracePowerFrozenFrames
import PowerConvexity.Analysis.TracePowerGeometricRate

/-! # Uniform second-derivative limits for a single physical matrix field

The frame Q(x) is selected pointwise and is constant in every derivative.
The statement makes all local bounds explicit; it does not presume that a
pointwise spectral gap is already a uniform gap.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
open Filter
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem tracePowerRoot_second_tendstoUniformlyOn_frozen_frames
    {K : E → Matrix ι ι ℂ} {U S : Set E}
    (hU : IsOpen U) (hK : ∀ i j, ContDiffOn ℝ 2 (fun y => K y i j) U)
    (hSU : S ⊆ U) (Q : E → Matrix ι ι ℂ) (k : E → ι → ℝ) (i : ι)
    (hQ : ∀ x ∈ S, IsUnit (Q x).det)
    (hdiag : ∀ x ∈ S, Q x*K x*(Q x)⁻¹ = Matrix.diagonal (fun j => (k x j : ℂ)))
    (h0 : ∀ x ∈ S, ∀ j, 0 ≤ k x j) {q δ B M1 M2 : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hδ : 0 < δ)
    (hki : ∀ x ∈ S, δ ≤ k x i) (hB : 0 ≤ B) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hQB : ∀ x ∈ S, ∀ l m, ‖Q x l m‖ ≤ B)
    (hQiB : ∀ x ∈ S, ∀ l m, ‖(Q x)⁻¹ l m‖ ≤ B)
    (hr : ∀ x ∈ S, ∀ j, j ≠ i → k x j/k x i ≤ q)
    (htrace : ∀ n : ℕ, ∀ y ∈ U, (K y^(n+2)).trace.im = 0)
    (hspec : ∀ y ∈ U, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im = 0)
    (a b c d : E)
    (hX : ∀ x ∈ S, ∀ l m, ‖matrixDZ a b K x l m‖ ≤ M1)
    (hY : ∀ x ∈ S, ∀ l m, ‖matrixDZ c d K x l m‖ ≤ M1)
    (hZ : ∀ x ∈ S, ∀ l m, ‖matrixDZ c d (matrixDZ a b K) x l m‖ ≤ M2) :
    TendstoUniformlyOn
      (fun n x => dz c d (dz a b (fun y => (tracePowerRoot K (n+2) y : ℂ))) x)
      (fun x => dz c d (dz a b (fun y => (largestRealEigenvalue (K y) : ℂ))) x) atTop S := by
  have ht : Tendsto (fun n : ℕ =>
      traceRootSecondErrorConstant (Fintype.card ι) q δ
        ((Fintype.card ι : ℝ)^2*B^2*M1) ((Fintype.card ι : ℝ)^2*B^2*M2)*((n : ℝ)+1)*q^n)
      atTop (𝓝 0) := by
    have hv := (geometric_polynomial_uniform_rate hq0 hq1).const_mul
      (traceRootSecondErrorConstant (Fintype.card ι) q δ
        ((Fintype.card ι : ℝ)^2*B^2*M1) ((Fintype.card ι : ℝ)^2*B^2*M2))
    rw [mul_zero] at hv
    convert hv using 1
    funext n
    ring
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  intro x hx
  rw [dist_eq_norm, norm_sub_rev]
  apply (tracePowerRoot_second_uniform_error_frozen_frame hU hK (hSU hx) (Q x) (hQ x hx)
    (k x) i (hdiag x hx) (h0 x hx) hq0 hq1 hδ (hki x hx) hB hM1 hM2
    (hQB x hx) (hQiB x hx) (hr x hx) htrace _ a b c d (hX x hx) (hY x hx) (hZ x hx) n).trans_lt hn
  filter_upwards [hU.mem_nhds (hSU hx)] with y hy
  exact hspec y hy

/-- A common absolute gap and top-eigenvalue upper bound give a common
ratio. This separates the spectral hypotheses from the analytic bounds. -/
theorem uniform_spectral_ratio_of_absolute_gap
    {α : Type*} {S : Set α} (k : α → ι → ℝ) (i : ι)
    {δ γ L : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) (hγL : γ ≤ L)
    (hki : ∀ x ∈ S, δ ≤ k x i) (hL : ∀ x ∈ S, k x i ≤ L)
    (hgap : ∀ x ∈ S, ∀ j, j ≠ i → γ ≤ k x i-k x j) :
    0 ≤ 1-γ/L ∧ 1-γ/L < 1 ∧
      ∀ x ∈ S, ∀ j, j ≠ i → k x j/k x i ≤ 1-γ/L := by
  have hLp : 0 < L := hγ.trans_le hγL
  refine ⟨?_,?_,?_⟩
  · have h := (div_le_one hLp).mpr hγL
    linarith
  · have h := div_pos hγ hLp
    linarith
  · intro x hx j hj
    exact spectral_ratio_le_of_gap (hδ.trans_le (hki x hx)) (hL x hx) hγ (hgap x hx j hj)

/-- The uniform theorem applied to the actual modified field. Smoothness,
real traces and the real-spectrum condition are discharged by the actual
C4 potential; the local spectral/frame/derivative bounds remain explicit. -/
theorem modifiedK_tracePowerRoot_second_tendstoUniformlyOn
    {u : E → ℝ} {U S : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) (hSU : S ⊆ U)
    (Q : E → Matrix ι ι ℂ) (k : E → ι → ℝ) (i : ι)
    (hQ : ∀ x ∈ S, IsUnit (Q x).det)
    (hdiag : ∀ x ∈ S, Q x*modifiedK a b u x*(Q x)⁻¹ =
      Matrix.diagonal (fun j => (k x j : ℂ)))
    (h0 : ∀ x ∈ S, ∀ j, 0 ≤ k x j) {q δ B M1 M2 : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hδ : 0 < δ)
    (hki : ∀ x ∈ S, δ ≤ k x i) (hB : 0 ≤ B) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hQB : ∀ x ∈ S, ∀ l m, ‖Q x l m‖ ≤ B)
    (hQiB : ∀ x ∈ S, ∀ l m, ‖(Q x)⁻¹ l m‖ ≤ B)
    (hr : ∀ x ∈ S, ∀ j, j ≠ i → k x j/k x i ≤ q)
    (v w s t : E)
    (hX : ∀ x ∈ S, ∀ l m, ‖matrixDZ v w (modifiedK a b u) x l m‖ ≤ M1)
    (hY : ∀ x ∈ S, ∀ l m, ‖matrixDZ s t (modifiedK a b u) x l m‖ ≤ M1)
    (hZ : ∀ x ∈ S, ∀ l m, ‖matrixDZ s t (matrixDZ v w (modifiedK a b u)) x l m‖ ≤ M2) :
    TendstoUniformlyOn
      (fun n x => dz s t (dz v w (fun y => (tracePowerRoot (modifiedK a b u) (n+2) y : ℂ))) x)
      (fun x => dz s t (dz v w (fun y => (largestRealEigenvalue (modifiedK a b u y) : ℂ))) x) atTop S := by
  apply tracePowerRoot_second_tendstoUniformlyOn_frozen_frames hU _ hSU Q k i
    hQ hdiag h0 hq0 hq1 hδ hki hB hM1 hM2 hQB hQiB hr _ _ v w s t hX hY hZ
  · intro l m y hy
    exact (modifiedK_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hy)) (hneg y hy) a b
      (hA y hy) l m).contDiffWithinAt
  · intro n y hy
    exact modifiedK_trace_power_real ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))
      (hneg y hy) a b (hA y hy) (n+2)
  · intro y hy z hz
    exact modifiedK_hasEigenvalue_real ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))
      a b (modifiedA_posDef a b (hneg y hy) (hA y hy)) hz

end PowerConvexity
