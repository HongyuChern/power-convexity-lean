import PowerConvexity.Calculus.UniformNormalizedJetsTwo
import PowerConvexity.Calculus.FrameReindexSecond

/-! # One local jet constant for both Schur rows and all normalizing frames -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complexFrameReal_reindex_rows_two (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin 2 → E) (e : Equiv.Perm (Fin 2)) :
    complexFrameReal (Q.submatrix e id) a b = (complexFrameReal Q a b) ∘ e := rfl

theorem complexFrameImag_reindex_rows_two (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin 2 → E) (e : Equiv.Perm (Fin 2)) :
    complexFrameImag (Q.submatrix e id) a b = (complexFrameImag Q a b) ∘ e := rfl

theorem matrix_reindex_rows_isUnit_det_two (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (hQ : IsUnit Q.det) (e : Equiv.Perm (Fin 2)) : IsUnit (Q.submatrix e id).det := by
  rw [Matrix.det_permute]
  exact ((Units.isUnit (Equiv.Perm.sign e)).map (Int.castRingHom ℂ)).mul hQ

theorem exists_uniform_normalized_all_rows_two
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0)
    (a b : Fin 2 → E) (hpos : (complexHessian a b u x).PosDef) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ y in 𝓝 x,
      ∀ (Q : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℝ), IsUnit Q.det →
      modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u y = 1 →
      modifiedB (complexFrameReal Q a b) (complexFrameImag Q a b) u y =
        Matrix.diagonal (fun i => (d i:ℂ)) →
      (∀ i, 0 ≤ d i ∧ d i ≤ 1) →
      (∀ p, (‖complexFrameReal Q a b p‖+‖complexFrameImag Q a b p‖)/2 ≤ B) ∧
      ∀ k, normalizedSpectralJetBoundTwo
        ((complexFrameReal Q a b) ∘ Equiv.swap (0:Fin 2) k)
        ((complexFrameImag Q a b) ∘ Equiv.swap (0:Fin 2) k) u y B := by
  obtain ⟨B,hB,hjets⟩ := exists_uniform_normalizedSpectralJetBoundTwo hu hx a b hpos
  refine ⟨B,hB,?_⟩
  filter_upwards [hjets] with y hj
  intro Q d hQ hI hD hd
  have hbase := hj Q d hQ hI hD (hd 0).1 (hd 0).2
  obtain ⟨_,_,_,_,_,_,_,_,hdir⟩ := hbase
  refine ⟨hdir,?_⟩
  intro k
  let e : Equiv.Perm (Fin 2) := Equiv.swap (0:Fin 2) k
  let Q' := Q.submatrix e id
  have hQ' : IsUnit Q'.det := matrix_reindex_rows_isUnit_det_two Q hQ e
  have hI' : modifiedA (complexFrameReal Q' a b) (complexFrameImag Q' a b) u y = 1 := by
    rw [complexFrameReal_reindex_rows_two,complexFrameImag_reindex_rows_two,
      modifiedA_frame_reindex,hI,Matrix.submatrix_one_equiv]
  have hD' : modifiedB (complexFrameReal Q' a b) (complexFrameImag Q' a b) u y =
      Matrix.diagonal (fun i => (d (e i):ℂ)) := by
    rw [complexFrameReal_reindex_rows_two,complexFrameImag_reindex_rows_two,
      modifiedB_frame_reindex,hD,Matrix.submatrix_diagonal_equiv]
    rfl
  have hh := hj Q' (d ∘ e) hQ' hI' hD' (hd (e 0)).1 (hd (e 0)).2
  simpa only [Q',complexFrameReal_reindex_rows_two,complexFrameImag_reindex_rows_two,e] using hh

end PowerConvexity
