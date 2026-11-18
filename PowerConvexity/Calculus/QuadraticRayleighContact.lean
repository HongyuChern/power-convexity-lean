import PowerConvexity.Calculus.QuadraticModifiedParameter
import PowerConvexity.Calculus.CenteredQuadraticParameters
import PowerConvexity.Algebra.TakagiSchurSpectrumTwo
import PowerConvexity.Analysis.RayleighContactMinimum

/-! # Actual Rayleigh contacts on a linear family of quadratic functions -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

noncomputable def modifiedRayleighDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → E) (u : E → ℝ) (x : E) (i : ι) : ℝ :=
  (modifiedSchur a b u x i i).re / (modifiedA a b u x i i).re

theorem modifiedSigmaTwo_le_rayleigh {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : Fin 2 → E)
    (hA : (modifiedA a b u x).PosDef) (i : Fin 2) :
    modifiedSigmaTwo a b u x ≤ modifiedRayleighDiagonal a b u x i :=
  schur_lower_le_diagonal_ratio hA (modifiedB_transpose hu a b) i

theorem quadraticFamily_add_linear_path (F : P →ₗ[ℝ] quadraticSubmodule E)
    (u : E → ℝ) (q h : P) (t : ℝ) :
    (fun y => u y+(F (q+t • h)).val y) =
      (fun y => (u y+(F q).val y)+t*(F h).val y) := by
  funext y
  rw [map_add,map_smul]
  change u y+((F q).val y+t*(F h).val y) = (u y+(F q).val y)+t*(F h).val y
  ring

theorem quadraticFamily_rayleigh_linear_hasDerivAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : Fin 2 → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (q h : P)
    (h0 : (F h).val x = 0) (h1 : fderiv ℝ (F h).val x = 0)
    (h2 : complexHessian a b (F h).val x = 0)
    (d s : Fin 2 → ℝ)
    (hA : modifiedA a b (fun y => u y+(F q).val y) x = 1)
    (hB : modifiedB a b (fun y => u y+(F q).val y) x =
      Matrix.diagonal (fun i => (d i:ℂ)))
    (hH : pureHessian a b (F h).val x = Matrix.diagonal (fun i => (s i:ℂ))) (i : Fin 2) :
    HasDerivAt (fun t : ℝ => modifiedRayleighDiagonal a b
      (fun y => u y+(F (q+t • h)).val y) x i) (-2*d i*s i) 0 := by
  simp_rw [quadraticFamily_add_linear_path]
  exact modifiedRayleigh_centered_diagonal_hasDerivAt
    (hu.add (IsQuadraticPolynomial_contDiff (F q).property 2).contDiffAt)
    (IsQuadraticPolynomial_contDiff (F h).property 2).contDiffAt
    a b h0 h1 h2 d s hA hB hH i

theorem quadraticFamily_repeated_positive_not_minimum
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : Fin 2 → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {ε d : ℝ}
    (hε : 0 < ε) (hd : 0 < d) (q h : P) (hq : ‖q‖^2 ≤ ε)
    (hneg : ∀ p : P, ‖p‖^2 ≤ ε → u x+(F p).val x < 0)
    (hpos : ∀ p : P, ‖p‖^2 ≤ ε → (modifiedA a b (fun y => u y+(F p).val y) x).PosDef)
    (h0 : (F h).val x = 0) (h1 : fderiv ℝ (F h).val x = 0)
    (h2 : complexHessian a b (F h).val x = 0)
    (hA : modifiedA a b (fun y => u y+(F q).val y) x = 1)
    (hB : modifiedB a b (fun y => u y+(F q).val y) x =
      Matrix.diagonal (fun _ => (d:ℂ)))
    (hH : pureHessian a b (F h).val x =
      Matrix.diagonal (fun i => ((if i=0 then 1 else -1:ℝ):ℂ)))
    (hmin : ∀ p : P, ‖p‖^2 ≤ ε →
      modifiedSigmaTwo a b (fun y => u y+(F q).val y) x ≤
        modifiedSigmaTwo a b (fun y => u y+(F p).val y) x) : False := by
  let f : P → ℝ := fun p => modifiedRayleighDiagonal a b (fun y => u y+(F p).val y) x 0
  let g : P → ℝ := fun p => modifiedRayleighDiagonal a b (fun y => u y+(F p).val y) x 1
  have hjet (p : P) : ContDiffAt ℝ 2 (fun y => u y+(F p).val y) x :=
    hu.add (IsQuadraticPolynomial_contDiff (F p).property 2).contDiffAt
  have hf : DifferentiableAt ℝ f q :=
    (quadraticFamily_rayleigh_contDiffAt F a b hu (hneg q hq) (hpos q hq) 0 1).differentiableAt
      (by norm_num)
  have hd0 : HasDerivAt (fun t : ℝ => f (q+t • h)) (-2*d) 0 := by
    simpa [f] using quadraticFamily_rayleigh_linear_hasDerivAt F a b hu q h h0 h1 h2
      (fun _ => d) (fun i => if i=0 then 1 else -1) hA hB hH 0
  have hd1 : HasDerivAt (fun t : ℝ => g (q+t • h)) (-(-2*d)) 0 := by
    convert quadraticFamily_rayleigh_linear_hasDerivAt F a b hu q h h0 h1 h2
      (fun _ => d) (fun i => if i=0 then 1 else -1) hA hB hH 1 using 1 <;> try rfl
    all_goals norm_num <;> ring
  have hM : modifiedSchur a b (fun y => u y+(F q).val y) x =
      Matrix.diagonal (fun _ : Fin 2 => ((1-d^2:ℝ):ℂ)) := by
    unfold modifiedSchur
    rw [hA,hB]
    exact matrixSchur_one_real_diagonal _
  have hs : modifiedSigmaTwo a b (fun y => u y+(F q).val y) x = 1-d^2 := by
    unfold modifiedSigmaTwo modifiedK
    rw [hM,hA,inv_one,Matrix.mul_one,lowerEigenvalueTwo_real_diagonal]
    exact min_self _
  have hfq : f q = modifiedSigmaTwo a b (fun y => u y+(F q).val y) x := by
    dsimp only [f,modifiedRayleighDiagonal]
    rw [hM,hA,hs]
    simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq,Complex.ofReal_re,Complex.one_re,div_one]
  have hgq : g q = modifiedSigmaTwo a b (fun y => u y+(F q).val y) x := by
    dsimp only [g,modifiedRayleighDiagonal]
    rw [hM,hA,hs]
    simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq,Complex.ofReal_re,Complex.one_re,div_one]
  apply no_common_ball_minimum_of_opposite_derivatives hε hq (by linarith : -2*d < 0)
    hf hd0 hd1
  · intro p hp
    rw [hfq]
    exact (hmin p hp).trans (modifiedSigmaTwo_le_rayleigh (hjet p) a b (hpos p hp) 0)
  · intro p hp
    rw [hgq]
    exact (hmin p hp).trans (modifiedSigmaTwo_le_rayleigh (hjet p) a b (hpos p hp) 1)

end PowerConvexity
