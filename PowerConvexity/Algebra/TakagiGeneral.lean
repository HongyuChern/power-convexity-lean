import PowerConvexity.Algebra.UnitaryCompletionGeneral
import PowerConvexity.Algebra.EigenvalueSchur
import PowerConvexity.Algebra.NormalizeTakagiVector

/-! # Arbitrary-dimensional Autonne--Takagi congruence

The construction is pointwise. It imposes no continuity on a chosen frame.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
universe u
namespace PowerConvexity
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem unitary_product {P Q : Matrix ι ι ℂ}
    (hP : P*P.conjTranspose = 1) (hQ : Q*Q.conjTranspose = 1) :
    (P*Q)*(P*Q).conjTranspose = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc
    _ = P*(Q*Q.conjTranspose)*P.conjTranspose := by noncomm_ring
    _ = 1 := by rw [hQ,Matrix.mul_one,hP]

theorem congruence_diagonal_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (B : Matrix ι ι ℂ) (Q : Matrix κ κ ℂ) (d : κ → ℂ)
    (hQ : Q*Q.conjTranspose = 1)
    (hd : Q*(B.submatrix e e)*Q.transpose = Matrix.diagonal d) :
    let P := Q.submatrix e.symm e.symm
    P*P.conjTranspose = 1 ∧ P*B*P.transpose = Matrix.diagonal (d ∘ e.symm) := by
  dsimp only
  constructor
  · rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,hQ,
      Matrix.submatrix_one_equiv]
  · have hB : B = (B.submatrix e e).submatrix e.symm e.symm := by
      ext i j
      simp
    conv_lhs => arg 1; arg 2; rw [hB]
    rw [Matrix.submatrix_mul_equiv,Matrix.transpose_submatrix,
      Matrix.submatrix_mul_equiv,hd,Matrix.submatrix_diagonal_equiv]

theorem exists_unitary_complex_diagonal_congruence {B : Matrix ι ι ℂ}
    (hB : B.transpose = B) :
    ∃ (Q : Matrix ι ι ℂ) (d : ι → ℂ), Q*Q.conjTranspose = 1 ∧
      Q*B*Q.transpose = Matrix.diagonal d := by
  classical
  have aux : ∀ n : ℕ, ∀ (κ : Type u) [Fintype κ] [DecidableEq κ],
      Fintype.card κ = n → ∀ (B : Matrix κ κ ℂ), B.transpose = B →
      ∃ (Q : Matrix κ κ ℂ) (d : κ → ℂ), Q*Q.conjTranspose = 1 ∧
        Q*B*Q.transpose = Matrix.diagonal d := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro κ _ _ hc B hB
      by_cases hz : B = 0
      · exact ⟨1,0,by simp,by simp [hz]⟩
      haveI : Nonempty κ := by
        by_contra h
        haveI : IsEmpty κ := not_nonempty_iff.mp h
        apply hz
        ext i
        exact isEmptyElim i
      let i : κ := Classical.choice inferInstance
      obtain ⟨v,t,_,hv,he⟩ := exists_unit_antilinear_vector hB hz
      obtain ⟨P,hP,hrow⟩ := exists_unitary_with_row v hv i
      let C := P*B*P.transpose
      have hC : C.transpose = C := by
        simp only [C,Matrix.transpose_mul,Matrix.transpose_transpose,hB]
        noncomm_ring
      have hcol (j : κ) : C j i = (t:ℂ)*(if j=i then 1 else 0) :=
        unitary_antilinear_first_column i v t hP hrow he j
      let J := {j : κ // j ≠ i}
      let D : Matrix J J ℂ := C.submatrix Subtype.val Subtype.val
      have hD : D.transpose = D := by
        dsimp only [D]
        rw [Matrix.transpose_submatrix,hC]
      have hcard : Fintype.card J < n := by
        rw [← hc]
        exact Fintype.card_subtype_lt (x := i) (by simp)
      obtain ⟨R,d,hR,hd⟩ := ih (Fintype.card J) hcard J rfl D hD
      let e := distinguishedIndexEquiv i
      let R₀ : Matrix (Unit ⊕ J) (Unit ⊕ J) ℂ := Matrix.fromBlocks 1 0 0 R
      have hR₀ : R₀*R₀.conjTranspose = 1 := by
        simp [R₀,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,hR]
      have hblock : C.submatrix e e = Matrix.fromBlocks
          (Matrix.diagonal (fun _ : Unit => (t:ℂ))) 0 0 D := by
        ext (⟨⟩|j) (⟨⟩|k)
        · simpa [e,distinguishedIndexEquiv] using hcol i
        · have hs : C i k = C k i := (congrFun (congrFun hC i) k).symm
          simpa [e,distinguishedIndexEquiv,hs,k.property] using hcol k
        · simpa [e,distinguishedIndexEquiv,j.property] using hcol j
        · rfl
      have hdiag : R₀*(C.submatrix e e)*R₀.transpose =
          Matrix.diagonal (Sum.elim (fun _ : Unit => (t:ℂ)) d) := by
        rw [hblock]
        simp [R₀,Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply,hd]
      obtain ⟨hS,hSd⟩ := congruence_diagonal_reindex e C R₀ _ hR₀ hdiag
      refine ⟨(R₀.submatrix e.symm e.symm)*P,
        (Sum.elim (fun _ : Unit => (t:ℂ)) d) ∘ e.symm,unitary_product hS hP,?_⟩
      rw [Matrix.transpose_mul]
      calc
        _ = (R₀.submatrix e.symm e.symm)*C*(R₀.submatrix e.symm e.symm).transpose := by
          dsimp [C]
          noncomm_ring
        _ = _ := hSd
  exact aux (Fintype.card ι) ι rfl B hB

theorem exists_takagi {B : Matrix ι ι ℂ} (hB : B.transpose = B) :
    ∃ (Q : Matrix ι ι ℂ) (d : ι → ℝ), IsUnit Q.det ∧ Q*Q.conjTranspose = 1 ∧
      (∀ i, 0 ≤ d i) ∧ Q*B*Q.transpose = Matrix.diagonal (fun i => (d i:ℂ)) := by
  classical
  obtain ⟨P,d,hP,hd⟩ := exists_unitary_complex_diagonal_congruence hB
  choose a ha had using fun i => exists_unit_phase_square (d i)
  let D := Matrix.diagonal a
  have hD : D*D.conjTranspose = 1 := by
    simp only [D,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    simpa only [Pi.star_apply,Complex.star_def,Complex.mul_conj,ha,Complex.ofReal_one]
  have hDP : (D*P)*(D*P).conjTranspose = 1 := unitary_product hD hP
  refine ⟨D*P,fun i => ‖d i‖,Matrix.isUnit_det_of_right_inverse hDP,hDP,
    fun _ => norm_nonneg _,?_⟩
  rw [Matrix.transpose_mul]
  calc
    _ = D*(P*B*P.transpose)*D.transpose := by noncomm_ring
    _ = Matrix.diagonal (fun i => a i^2*d i) := by
      rw [hd]
      simp only [D,Matrix.diagonal_transpose,Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      ring
    _ = _ := by simp only [had]

end PowerConvexity
