import PowerConvexity.Analysis.MatrixHessianContraction

/-! # A zero elliptic contraction of a nonnegative symmetric bilinear form -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators MatrixOrder
namespace PowerConvexity
open Matrix
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem bilinear_basis_matrix_posSemidef (e : κ → E)
    (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ v w, H v w = H w v) (hn : ∀ v, 0 ≤ H v v) :
    Matrix.PosSemidef (fun i j => H (e i) (e j) : Matrix κ κ ℝ) := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using hs (e j) (e i)
  · intro z
    calc
      0 ≤ H (∑ i, z i • e i) (∑ i, z i • e i) := hn _
      _ = _ := by
        simp only [dotProduct,Matrix.mulVec,star_trivial,map_sum,map_smul,
          Finset.mul_sum,Finset.sum_mul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hs (e j) (e i)]
        ring

theorem bilinear_eq_zero_of_basis_matrix_zero (e : Module.Basis κ ℝ E)
    (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hz : (fun i j => H (e i) (e j) : Matrix κ κ ℝ) = 0) : H = 0 := by
  ext v w
  have hij (i j : κ) : H (e i) (e j) = 0 := congrArg (fun M : Matrix κ κ ℝ => M i j) hz
  rw [← e.sum_repr v,← e.sum_repr w]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul,hij,
    mul_zero,Finset.sum_const_zero,ContinuousLinearMap.zero_apply]

theorem matrixHessianContraction_eq_zero_iff (e : Module.Basis κ ℝ E)
    {C : Matrix κ κ ℝ} (hC : C.PosDef)
    (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ v w, H v w = H w v) (hn : ∀ v, 0 ≤ H v v) :
    matrixHessianContraction e C H = 0 ↔ H = 0 := by
  constructor
  · intro hz
    let D : Matrix κ κ ℝ := fun i j => H (e i) (e j)
    have hD : D.PosSemidef := bilinear_basis_matrix_posSemidef e H hs hn
    let Q := CFC.sqrt C
    have hQ : Q.PosSemidef := (CFC.sqrt_nonneg C).posSemidef
    have hQt : Q.transpose = Q := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian.eq
    have hQsq : Q*Q = C := by
      simpa only [pow_two] using CFC.sq_sqrt C hC.posSemidef.nonneg
    have hdetQ : IsUnit Q.det := by
      apply isUnit_iff_ne_zero.mpr
      intro h0
      have hh := congrArg Matrix.det hQsq
      rw [Matrix.det_mul,h0,zero_mul] at hh
      exact (ne_of_gt hC.det_pos) hh.symm
    have htrace : (C*D).trace = 0 := by
      simpa only [matrixHessianContraction,LinearMap.coe_mk,AddHom.coe_mk,
        Matrix.trace,Matrix.diag,Matrix.mul_apply,D] using hz
    have hQD : (Q*D*Q).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,hQt] using hD.mul_mul_conjTranspose_same Q
    have htrQ : (Q*D*Q).trace = 0 := by
      rw [Matrix.trace_mul_cycle,hQsq]
      exact htrace
    have hzero : Q*D*Q = 0 := hQD.trace_eq_zero_iff.mp htrQ
    have hDz := congrArg (fun M : Matrix κ κ ℝ => Q⁻¹*M*Q⁻¹) hzero
    have hDz' : D = 0 := by
      simpa only [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hdetQ,
        Matrix.mul_one,Matrix.nonsing_inv_mul_cancel_left _ _ hdetQ,
        Matrix.mul_zero,Matrix.zero_mul] using hDz
    exact bilinear_eq_zero_of_basis_matrix_zero e H hDz'
  · intro h
    simp [h]

end PowerConvexity
