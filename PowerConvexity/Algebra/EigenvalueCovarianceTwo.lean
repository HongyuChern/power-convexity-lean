import PowerConvexity.Calculus.EigenvalueFieldTwo

/-! # Exact ordered-root covariance for the actual Schur quotient -/
set_option autoImplicit false
open scoped ContDiff
namespace PowerConvexity

theorem trace_det_eq_of_charpoly_eq_two {K L : Matrix (Fin 2) (Fin 2) ℂ}
    (h : K.charpoly = L.charpoly) : K.trace = L.trace ∧ K.det = L.det := by
  rw [Matrix.charpoly_fin_two,Matrix.charpoly_fin_two] at h
  have h0 := congrArg (fun p : Polynomial ℂ => p.coeff 0) h
  have h1 := congrArg (fun p : Polynomial ℂ => p.coeff 1) h
  simp at h0 h1
  constructor
  · exact h1
  · exact h0

theorem eigenDiscriminantTwo_eq_of_charpoly_eq {K L : Matrix (Fin 2) (Fin 2) ℂ}
    (h : K.charpoly = L.charpoly) : eigenDiscriminantTwo K = eigenDiscriminantTwo L := by
  obtain ⟨ht,hd⟩ := trace_det_eq_of_charpoly_eq_two h
  simp only [eigenDiscriminantTwo,ht,hd]

theorem lowerEigenvalueTwo_eq_of_charpoly_eq {K L : Matrix (Fin 2) (Fin 2) ℂ}
    (h : K.charpoly = L.charpoly) : lowerEigenvalueTwo K = lowerEigenvalueTwo L := by
  rw [lowerEigenvalueTwo,lowerEigenvalueTwo,(trace_det_eq_of_charpoly_eq_two h).1,
    eigenDiscriminantTwo_eq_of_charpoly_eq h]

theorem upperEigenvalueTwo_eq_of_charpoly_eq {K L : Matrix (Fin 2) (Fin 2) ℂ}
    (h : K.charpoly = L.charpoly) : upperEigenvalueTwo K = upperEigenvalueTwo L := by
  rw [upperEigenvalueTwo,upperEigenvalueTwo,(trace_det_eq_of_charpoly_eq_two h).1,
    eigenDiscriminantTwo_eq_of_charpoly_eq h]

open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedSigmaTwo_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : IsUnit Q.det) (a b : Fin 2 → E) :
    modifiedSigmaTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
      modifiedSigmaTwo a b u x := by
  unfold modifiedSigmaTwo modifiedK
  rw [modifiedSchur_quotient_complexFrame hu hx Q hQ]
  exact lowerEigenvalueTwo_eq_of_charpoly_eq (charpoly_complex_similarity Q _ hQ)

theorem modifiedSigmaTwo_gap_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : IsUnit Q.det) (a b : Fin 2 → E) :
    eigenDiscriminantTwo (modifiedK (complexFrameReal Q a b) (complexFrameImag Q a b) u x) =
      eigenDiscriminantTwo (modifiedK a b u x) := by
  unfold modifiedK
  rw [modifiedSchur_quotient_complexFrame hu hx Q hQ]
  exact eigenDiscriminantTwo_eq_of_charpoly_eq (charpoly_complex_similarity Q _ hQ)

end PowerConvexity
