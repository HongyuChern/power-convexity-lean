import PowerConvexity.Calculus.DirectionalHessianBoundaryMaximum

/-! # Full real Hessian entries from a one-sided quadratic bound

The complex diagonal controls the sum of the two paired real diagonal
entries. Combining this with the upper quadratic bound controls each lower
diagonal entry; polarization then controls the off-diagonal entries. Real
convexity of u is not assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Matrix
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem paired_realHessian_diagonal_nonneg
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (a b : ι → E) (hpos : (complexHessian a b u x).PosSemidef) (i : ι) :
    0 ≤ realHessian u x (a i) (a i) + realHessian u x (b i) (b i) := by
  have hh := (Complex.nonneg_iff.mp (hpos.diag_nonneg (i := i))).1
  rw [complexHessian_real_entry hu a b i i] at hh
  norm_num [Complex.mul_re,Complex.add_re,Complex.sub_re,Complex.mul_im] at hh
  linarith

theorem realBlockHessian_abs_le_of_quadratic_upper
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (a b : ι → E) (hnorm : ∀ i : ι ⊕ ι, ‖Sum.elim a b i‖ ≤ 1)
    (hpos : (complexHessian a b u x).PosSemidef)
    {M : ℝ} (hM : 0 ≤ M)
    (hupper : ∀ v : E, realHessian u x v v ≤ M * ‖v‖^2) :
    ∀ i j : ι ⊕ ι, |realBlockHessian a b u x i j| ≤ 3 * M := by
  let e : ι ⊕ ι → E := Sum.elim a b
  have hdiag (i : ι ⊕ ι) : realHessian u x (e i) (e i) ≤ M := by
    have hn : ‖e i‖^2 ≤ 1 := by nlinarith [hnorm i,norm_nonneg (e i)]
    exact (hupper (e i)).trans (by nlinarith [mul_le_mul_of_nonneg_left hn hM])
  have hlow (i : ι ⊕ ι) : -M ≤ realHessian u x (e i) (e i) := by
    cases i with
    | inl k =>
      have hp := paired_realHessian_diagonal_nonneg hu a b hpos k
      have hd := hdiag (.inr k)
      change realHessian u x (b k) (b k) ≤ M at hd
      change -M ≤ realHessian u x (a k) (a k)
      linarith
    | inr k =>
      have hp := paired_realHessian_diagonal_nonneg hu a b hpos k
      have hd := hdiag (.inl k)
      change realHessian u x (a k) (a k) ≤ M at hd
      change -M ≤ realHessian u x (b k) (b k)
      linarith
  intro i j
  have hnadd : ‖e i + e j‖^2 ≤ 4 := by
    have h := norm_add_le (e i) (e j)
    nlinarith [hnorm i,hnorm j,norm_nonneg (e i+e j)]
  have hnsub : ‖e i - e j‖^2 ≤ 4 := by
    have h := norm_sub_le (e i) (e j)
    nlinarith [hnorm i,hnorm j,norm_nonneg (e i-e j)]
  have hadd : realHessian u x (e i+e j) (e i+e j) ≤ 4*M :=
    (hupper _).trans (by nlinarith [mul_le_mul_of_nonneg_left hnadd hM])
  have hsub : realHessian u x (e i-e j) (e i-e j) ≤ 4*M :=
    (hupper _).trans (by nlinarith [mul_le_mul_of_nonneg_left hnsub hM])
  have hsym := realHessian_symm hu (e i) (e j)
  simp only [map_add,ContinuousLinearMap.add_apply] at hadd
  simp only [map_sub,ContinuousLinearMap.sub_apply] at hsub
  change |realHessian u x (e i) (e j)| ≤ 3*M
  exact abs_le.mpr ⟨by linarith [hlow i,hlow j],by linarith [hlow i,hlow j]⟩

variable [Nonempty ι]

theorem realBlockHessian_abs_le_of_boundary_quadratic_upper
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : ι → E) (hnorm : ∀ i : ι ⊕ ι, ‖Sum.elim a b i‖ ≤ 1)
    (hpos : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hboundary : ∀ x ∈ frontier U, ∀ v : E, J.hessian x v v ≤ M * ‖v‖^2) :
    ∀ x ∈ U, ∀ i j : ι ⊕ ι, |realBlockHessian a b u x i j| ≤ 3*M := by
  intro x hx
  apply realBlockHessian_abs_le_of_quadratic_upper
    ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)) a b hnorm (hpos x hx).posSemidef hM
  intro v
  have hh := directionalHessian_le_boundary_bound hU hK hu J hb a b hpos hdet v
    (fun z hz => hboundary z hz v) x (subset_closure hx)
  simpa only [J.hessian_eq hx,realHessian] using hh

end PowerConvexity
