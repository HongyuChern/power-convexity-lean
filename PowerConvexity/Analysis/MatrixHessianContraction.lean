import PowerConvexity.Analysis.GradientStrongMinimum
import PowerConvexity.Algebra.SchurSpectrum

/-! # Positive real matrix coefficients as actual Hessian contractions -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology MatrixOrder

namespace PowerConvexity
open CHS.Calculus Matrix
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def matrixHessianContraction (e : κ → E) (C : Matrix κ κ ℝ) :
    (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun H := ∑ i, ∑ j, C i j * H (e j) (e i)
  map_add' H K := by simp [Finset.sum_add_distrib, mul_add]
  map_smul' c H := by
    simp only [RingHom.id_apply, _root_.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem matrixHessianContraction_gram (e : κ → E) (Q : Matrix κ κ ℝ)
    (H : E →L[ℝ] E →L[ℝ] ℝ) :
    matrixHessianContraction e (Q.transpose * Q) H =
      ∑ k, H (∑ j, Q k j • e j) (∑ i, Q k i • e i) := by
  simp only [matrixHessianContraction, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
    map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ k, ∑ j, (Q k i * Q k j) * H (e j) (e i) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, (Q k i * Q k j) * H (e j) (e i) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem matrixHessianContraction_positive (e : κ → E) {C : Matrix κ κ ℝ}
    (hC : C.PosSemidef) : HessianPositive (matrixHessianContraction e C) := by
  let Q := CFC.sqrt C
  have hQ : Q.PosSemidef := (CFC.sqrt_nonneg C).posSemidef
  have hQt : Q.transpose = Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian.eq
  have hQsq : Q * Q = C := by
    simpa only [pow_two] using CFC.sq_sqrt C hC.nonneg
  have hgram : C = Q.transpose * Q := by rw [hQt, hQsq]
  intro H hH
  rw [hgram, matrixHessianContraction_gram]
  exact Finset.sum_nonneg fun k _ => hH _


theorem matrixHessianContraction_rankOne (e : κ → E) (C : Matrix κ κ ℝ) (v : E) :
    matrixHessianContraction e C (realRankOneForm v) =
      (fun i => inner ℝ v (e i)) ⬝ᵥ C.mulVec (fun i => inner ℝ v (e i)) := by
  simp only [matrixHessianContraction, LinearMap.coe_mk, AddHom.coe_mk,
    realRankOneForm, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    _root_.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem basis_inner_coordinates_ne_zero (e : Module.Basis κ ℝ E) {v : E} (hv : v ≠ 0) :
    (fun i => inner ℝ v (e i)) ≠ 0 := by
  intro he
  have hsum : inner ℝ v (∑ i, e.repr v i • e i) = 0 := by
    simp only [inner_sum, real_inner_smul_right]
    have hi (i : κ) : inner ℝ v (e i) = 0 := congrFun he i
    simp only [hi, mul_zero, Finset.sum_const_zero]
  rw [e.sum_repr, real_inner_self_eq_norm_sq] at hsum
  have hn : ‖v‖ = 0 := (sq_eq_zero_iff).mp hsum
  exact hv (norm_eq_zero.mp hn)

theorem matrixHessianContraction_rankOne_pos (e : Module.Basis κ ℝ E)
    {C : Matrix κ κ ℝ} (hC : C.PosDef) {v : E} (hv : v ≠ 0) :
    0 < matrixHessianContraction e C (realRankOneForm v) := by
  rw [matrixHessianContraction_rankOne]
  simpa only [star_trivial] using hC.dotProduct_mulVec_pos (basis_inner_coordinates_ne_zero e hv)

theorem realRankOneForm_smul (c : ℝ) (v : E) :
    realRankOneForm (c • v) = c^2 • realRankOneForm v := by
  ext x y
  simp only [realRankOneForm, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    _root_.smul_apply, smul_eq_mul, real_inner_smul_left]
  ring

end PowerConvexity
