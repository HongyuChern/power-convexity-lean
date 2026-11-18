import PowerConvexity.Calculus.QuadraticRayleighContact
import PowerConvexity.Algebra.TakagiSchurSpectrumGeneral

/-! # Actual minimum-eigenvalue Rayleigh contacts in every dimension -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def modifiedSigma (a b : ι → E) (u : E → ℝ) (x : E) : ℝ :=
  smallestRealEigenvalue (modifiedK a b u x)

theorem modifiedSigma_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (Q : Matrix ι ι ℂ)
    (hQ : IsUnit Q.det) (a b : ι → E) :
    modifiedSigma (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
      modifiedSigma a b u x := by
  unfold modifiedSigma modifiedK
  rw [modifiedSchur_quotient_complexFrame hu hx Q hQ]
  exact smallestRealEigenvalue_of_charpoly_eq (charpoly_complex_similarity Q _ hQ)

theorem modifiedSigma_le_rayleigh {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hA : (modifiedA a b u x).PosDef) (i : ι) :
    modifiedSigma a b u x ≤ modifiedRayleighDiagonal a b u x i :=
  schur_minimum_le_diagonal_ratio hA (modifiedB_transpose hu a b) i

theorem quadraticFamily_rayleigh_linear_hasDerivAt_general
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (q h : P)
    (h0 : (F h).val x = 0) (h1 : fderiv ℝ (F h).val x = 0)
    (h2 : complexHessian a b (F h).val x = 0)
    (d s : ι → ℝ)
    (hA : modifiedA a b (fun y => u y+(F q).val y) x = 1)
    (hB : modifiedB a b (fun y => u y+(F q).val y) x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hH : pureHessian a b (F h).val x = Matrix.diagonal (fun i => (s i:ℂ))) (i : ι) :
    HasDerivAt (fun t : ℝ => modifiedRayleighDiagonal a b
      (fun y => u y+(F (q+t • h)).val y) x i) (-2*d i*s i) 0 := by
  simp_rw [quadraticFamily_add_linear_path]
  exact modifiedRayleigh_centered_diagonal_hasDerivAt
    (hu.add (IsQuadraticPolynomial_contDiff (F q).property 2).contDiffAt)
    (IsQuadraticPolynomial_contDiff (F h).property 2).contDiffAt
    a b h0 h1 h2 d s hA hB hH i

theorem quadraticFamily_repeated_positive_not_minimum_general
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {ε : ℝ}
    (hε : 0 < ε) (d : ι → ℝ) (hd : ∀ k, 0 ≤ d k) (i j : ι) (hij : i ≠ j)
    (hi : ∀ k, d k ≤ d i) (heq : d j = d i) (hdi : 0 < d i)
    (q h : P) (hq : ‖q‖^2 ≤ ε)
    (hneg : ∀ p : P, ‖p‖^2 ≤ ε → u x+(F p).val x < 0)
    (hpos : ∀ p : P, ‖p‖^2 ≤ ε → (modifiedA a b (fun y => u y+(F p).val y) x).PosDef)
    (h0 : (F h).val x = 0) (h1 : fderiv ℝ (F h).val x = 0)
    (h2 : complexHessian a b (F h).val x = 0)
    (hA : modifiedA a b (fun y => u y+(F q).val y) x = 1)
    (hB : modifiedB a b (fun y => u y+(F q).val y) x = Matrix.diagonal (fun k => (d k:ℂ)))
    (hH : pureHessian a b (F h).val x =
      Matrix.diagonal (fun k => (((if k=i then 1 else 0)-(if k=j then 1 else 0):ℝ):ℂ)))
    (hmin : ∀ p : P, ‖p‖^2 ≤ ε →
      modifiedSigma a b (fun y => u y+(F q).val y) x ≤
        modifiedSigma a b (fun y => u y+(F p).val y) x) : False := by
  let f : P → ℝ := fun p => modifiedRayleighDiagonal a b (fun y => u y+(F p).val y) x i
  let g : P → ℝ := fun p => modifiedRayleighDiagonal a b (fun y => u y+(F p).val y) x j
  have hjet (p : P) : ContDiffAt ℝ 2 (fun y => u y+(F p).val y) x :=
    hu.add (IsQuadraticPolynomial_contDiff (F p).property 2).contDiffAt
  have hf : DifferentiableAt ℝ f q :=
    (quadraticFamily_rayleigh_contDiffAt F a b hu (hneg q hq) (hpos q hq) i 1).differentiableAt
      (by norm_num)
  have hd0 : HasDerivAt (fun t : ℝ => f (q+t • h)) (-2*d i) 0 := by
    simpa only [f,ite_true,if_neg hij,sub_zero,mul_one] using
      quadraticFamily_rayleigh_linear_hasDerivAt_general F a b hu q h h0 h1 h2 d
        (fun k => (if k=i then 1 else 0)-(if k=j then 1 else 0)) hA hB hH i
  have hd1 : HasDerivAt (fun t : ℝ => g (q+t • h)) (-(-2*d i)) 0 := by
    convert quadraticFamily_rayleigh_linear_hasDerivAt_general F a b hu q h h0 h1 h2 d
      (fun k => (if k=i then 1 else 0)-(if k=j then 1 else 0)) hA hB hH j using 1
    simp [Ne.symm hij,heq]
  have hM : modifiedSchur a b (fun y => u y+(F q).val y) x =
      Matrix.diagonal (fun k => ((1-d k^2:ℝ):ℂ)) := by
    unfold modifiedSchur
    rw [hA,hB]
    exact matrixSchur_one_real_diagonal _
  have hs : modifiedSigma a b (fun y => u y+(F q).val y) x = 1-d i^2 := by
    unfold modifiedSigma modifiedK
    rw [hM,hA,inv_one,Matrix.mul_one]
    apply smallestRealEigenvalue_diagonal
    intro k
    nlinarith [hi k,hd k,hd i]
  have hfq : f q = modifiedSigma a b (fun y => u y+(F q).val y) x := by
    dsimp only [f,modifiedRayleighDiagonal]
    rw [hM,hA,hs]
    simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq,Complex.ofReal_re,Complex.one_re,div_one]
  have hgq : g q = modifiedSigma a b (fun y => u y+(F q).val y) x := by
    dsimp only [g,modifiedRayleighDiagonal]
    rw [hM,hA,hs]
    simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq,Complex.ofReal_re,Complex.one_re,div_one,heq]
  apply no_common_ball_minimum_of_opposite_derivatives hε hq (by linarith : -2*d i < 0)
    hf hd0 hd1
  · intro p hp
    rw [hfq]
    exact (hmin p hp).trans (modifiedSigma_le_rayleigh (hjet p) a b (hpos p hp) i)
  · intro p hp
    rw [hgq]
    exact (hmin p hp).trans (modifiedSigma_le_rayleigh (hjet p) a b (hpos p hp) j)

end PowerConvexity
