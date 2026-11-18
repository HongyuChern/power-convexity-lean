import PowerConvexity.Calculus.ConvexPowerStrictnessGapTwo
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # The literal standard complex two-dimensional coordinate frame -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ComplexConjugate
namespace PowerConvexity

noncomputable def standardComplexTwoBasis : Module.Basis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis

theorem standardComplexTwoBasis_apply (i : Fin 2) :
    standardComplexTwoBasis i = EuclideanSpace.single i 1 := by
  exact EuclideanSpace.basisFun_apply (𝕜 := ℂ) (ι := Fin 2) i

theorem standardComplexTwoBasis_real_orthonormal :
    Orthonormal ℝ (Sum.elim (standardComplexTwoBasis : Fin 2 → EuclideanSpace ℂ (Fin 2))
      (fun j => Complex.I • standardComplexTwoBasis j)) := by
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      fin_cases i <;> fin_cases j <;>
        norm_num [standardComplexTwoBasis_apply,PiLp.inner_apply,Fin.sum_univ_two,Complex.inner] <;> simp [norm_smul]
    | inr j =>
      fin_cases i <;> fin_cases j <;>
        norm_num [standardComplexTwoBasis_apply,PiLp.inner_apply,Fin.sum_univ_two,Complex.inner] <;> simp [norm_smul]
  | inr i =>
    cases j with
    | inl j =>
      fin_cases i <;> fin_cases j <;>
        norm_num [standardComplexTwoBasis_apply,PiLp.inner_apply,Fin.sum_univ_two,Complex.inner] <;> simp [norm_smul]
    | inr j =>
      fin_cases i <;> fin_cases j <;>
        norm_num [standardComplexTwoBasis_apply,PiLp.inner_apply,Fin.sum_univ_two,Complex.inner] <;> simp [norm_smul]

end PowerConvexity
