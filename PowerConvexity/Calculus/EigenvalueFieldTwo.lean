import PowerConvexity.Algebra.EigenvaluesTwo
import PowerConvexity.Calculus.ImplicitEigenvalueTwo
import PowerConvexity.Calculus.ModifiedSpectrum

/-! # The actual lowest-root field and its C2 branch on the positive-gap locus -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eigenDiscriminantTwo_contDiffAt {K : E → Matrix (Fin 2) (Fin 2) ℂ}
    {x : E} {k : WithTop ℕ∞}
    (hK : ∀ i j, ContDiffAt ℝ k (fun y => K y i j) x) :
    ContDiffAt ℝ k (fun y => eigenDiscriminantTwo (K y)) x := by
  have ht : ContDiffAt ℝ k (fun y => (K y).trace.re) x := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    exact Complex.reCLM.contDiff.contDiffAt.comp x ((hK 0 0).add (hK 1 1))
  have hd : ContDiffAt ℝ k (fun y => (K y).det.re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x (field_det_contDiffAt hK)
  exact (ht.pow 2).sub (contDiffAt_const.mul hd)

theorem lowerEigenvalueTwo_contDiffAt {K : E → Matrix (Fin 2) (Fin 2) ℂ}
    {x : E} {k : WithTop ℕ∞}
    (hK : ∀ i j, ContDiffAt ℝ k (fun y => K y i j) x)
    (hgap : 0 < eigenDiscriminantTwo (K x)) :
    ContDiffAt ℝ k (fun y => lowerEigenvalueTwo (K y)) x := by
  have ht : ContDiffAt ℝ k (fun y => (K y).trace.re) x := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    exact Complex.reCLM.contDiff.contDiffAt.comp x ((hK 0 0).add (hK 1 1))
  exact (ht.sub ((eigenDiscriminantTwo_contDiffAt hK).sqrt (ne_of_gt hgap))).div_const 2

theorem charpoly_root_equation_two (K : Matrix (Fin 2) (Fin 2) ℂ) (ell : ℂ)
    (h : K.charpoly.IsRoot ell) :
    (K 0 0 - ell) * (K 1 1 - ell) - K 0 1 * K 1 0 = 0 := by
  rw [Matrix.charpoly_fin_two] at h
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.det_fin_two] at h
  linear_combination h

noncomputable def modifiedSigmaTwo (a b : Fin 2 → E) (u : E → ℝ) (x : E) : ℝ :=
  lowerEigenvalueTwo (modifiedK a b u x)

theorem modifiedSigmaTwo_is_min_root {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hA : (complexHessian a b u x).PosDef) :
    (modifiedK a b u x).charpoly.IsRoot (modifiedSigmaTwo a b u x : ℂ) ∧
      ∀ t : ℝ, (modifiedK a b u x).charpoly.IsRoot (t : ℂ) →
        modifiedSigmaTwo a b u x ≤ t :=
  schur_quotient_lower_is_min_root (modifiedA_posDef a b hx hA)
    (modifiedB_transpose hu a b)

theorem modifiedSigmaTwo_discriminant_nonneg {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hA : (complexHessian a b u x).PosDef) :
    0 ≤ eigenDiscriminantTwo (modifiedK a b u x) :=
  schur_quotient_discriminant_nonneg (modifiedA_posDef a b hx hA)
    (modifiedB_transpose hu a b)

theorem modifiedSigmaTwo_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hA : (complexHessian a b u x).PosDef)
    (hgap : 0 < eigenDiscriminantTwo (modifiedK a b u x)) :
    ContDiffAt ℝ 2 (modifiedSigmaTwo a b u) x :=
  lowerEigenvalueTwo_contDiffAt (modifiedK_contDiffAt_two hu hx a b hA) hgap

theorem modifiedSigmaTwo_local_characteristic_equation {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U) :
    (fun y => (modifiedK a b u y 0 0 - (modifiedSigmaTwo a b u y : ℂ)) *
      (modifiedK a b u y 1 1 - (modifiedSigmaTwo a b u y : ℂ)) -
      modifiedK a b u y 0 1 * modifiedK a b u y 1 0) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
  filter_upwards [hU.mem_nhds hx] with y hy
  exact charpoly_root_equation_two _ _
    (modifiedSigmaTwo_is_min_root (hu.contDiffAt (hU.mem_nhds hy))
      (hneg y hy) a b (hA y hy)).1

/-- `B2-1` applied to the actual lowest eigenvalue of the actual Schur quotient. -/
theorem modifiedSigmaTwo_dz {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (hgap : 0 < eigenDiscriminantTwo (modifiedK a b u x))
    (h00 : modifiedK a b u x 0 0 = (modifiedSigmaTwo a b u x : ℂ))
    (h01 : modifiedK a b u x 0 1 = 0) (h10 : modifiedK a b u x 1 0 = 0)
    (hden : modifiedK a b u x 1 1 - (modifiedSigmaTwo a b u x : ℂ) ≠ 0)
    (v w : E) :
    dz v w (fun y => (modifiedSigmaTwo a b u y : ℂ)) x =
      dz v w (fun y => modifiedK a b u y 0 0) x := by
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hK := modifiedK_contDiffAt_two hu4 (hneg x hx) a b (hA x hx)
  have hσ := modifiedSigmaTwo_contDiffAt_two hu4 (hneg x hx) a b (hA x hx) hgap
  exact simple_eigenvalueTwo_dz (fun i j => (hK i j).differentiableAt (by norm_num))
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp x hσ).differentiableAt (by norm_num))
    (modifiedSigmaTwo_local_characteristic_equation hU (hu.of_le (by norm_num))
      a b hneg hA hx) h00 h01 h10 hden v w

/-- `B2-2` and `3.2-1` for the actual lowest-eigenvalue field, in dimension two. -/
theorem modifiedSigmaTwo_mixed {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (hgap : 0 < eigenDiscriminantTwo (modifiedK a b u x))
    (h00 : modifiedK a b u x 0 0 = (modifiedSigmaTwo a b u x : ℂ))
    (h01 : modifiedK a b u x 0 1 = 0) (h10 : modifiedK a b u x 1 0 = 0)
    (hden : modifiedK a b u x 1 1 - (modifiedSigmaTwo a b u x : ℂ) ≠ 0)
    (v w s t : E) :
    dz s t (dz v w (fun y => (modifiedSigmaTwo a b u y : ℂ))) x =
      dz s t (dz v w (fun y => modifiedK a b u y 0 0)) x -
      (dz v w (fun y => modifiedK a b u y 0 1) x *
          dz s t (fun y => modifiedK a b u y 1 0) x +
        dz s t (fun y => modifiedK a b u y 0 1) x *
          dz v w (fun y => modifiedK a b u y 1 0) x) /
      (modifiedK a b u x 1 1 - (modifiedSigmaTwo a b u x : ℂ)) := by
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hK := modifiedK_contDiffAt_two hu4 (hneg x hx) a b (hA x hx)
  have hσ := modifiedSigmaTwo_contDiffAt_two hu4 (hneg x hx) a b (hA x hx) hgap
  exact simple_eigenvalueTwo_mixed hK
    (Complex.ofRealCLM.contDiff.contDiffAt.comp x hσ)
    (modifiedSigmaTwo_local_characteristic_equation hU (hu.of_le (by norm_num))
      a b hneg hA hx) h00 h01 h10 hden v w s t

end PowerConvexity
