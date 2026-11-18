import PowerConvexity.Calculus.ExtremalEigenvalueDerivatives
import PowerConvexity.Calculus.ModifiedSpectrum
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-! # The real-spectrum condition is proved for the paper's actual Schur quotient -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Topology ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem schur_quotient_hasEigenvalue_real {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) {z : ℂ}
    (hz : Module.End.HasEigenvalue (matrixSchur A B * A⁻¹).toLin' z) : z.im = 0 := by
  have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp hz
  rw [Matrix.charpoly_toLin',schur_quotient_charpoly_real_factors hA hB] at he
  change Polynomial.eval z _ = 0 at he
  simp only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] at he
  obtain ⟨j,_,hj⟩ := Finset.prod_eq_zero_iff.mp he
  rw [sub_eq_zero.mp hj]
  exact Complex.ofReal_im _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedK_hasEigenvalue_real {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hA : (modifiedA a b u x).PosDef) {z : ℂ}
    (hz : Module.End.HasEigenvalue (modifiedK a b u x).toLin' z) : z.im = 0 :=
  schur_quotient_hasEigenvalue_real hA (modifiedB_transpose hu a b) hz

theorem modifiedK_smallestRealEigenvalue_jet [CompleteSpace E]
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hneg : ∀ y ∈ U, u y < 0)
    (hpsh : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ)
    (hdiag : modifiedK a b u x = Matrix.diagonal (fun j => (d j:ℂ)))
    (hmin : ∀ j, j ≠ i → d i < d j) :
    SimpleRealEigenvalueJet (modifiedK a b u)
      (fun y => smallestRealEigenvalue (modifiedK a b u y)) x i d := by
  apply smallestRealEigenvalue_jet
    (modifiedK_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) a b (hpsh x hx))
    i d hdiag hmin
  filter_upwards [hU.mem_nhds hx] with y hy z hz
  exact modifiedK_hasEigenvalue_real
    ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) a b
    (modifiedA_posDef a b (hneg y hy) (hpsh y hy)) hz

end PowerConvexity
