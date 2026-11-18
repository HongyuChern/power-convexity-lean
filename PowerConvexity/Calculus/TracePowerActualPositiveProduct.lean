import PowerConvexity.Calculus.TracePowerLocalMetric
import PowerConvexity.Calculus.ModifiedPencilGeneral

/-! # Fully automatic local Appendix-B convergence for the actual positive product

I - modifiedK is the actual BB*/A product. Takagi normalization proves its
nonnegative spectrum in the same positive metric modifiedA. Thus all local
spectral, frame and second-jet inputs are discharged from the actual C4
potential and one simple positive top root at the base point.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Filter
open scoped BigOperators Topology ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def modifiedPositiveProduct (a b : ι → E) (u : E → ℝ) (y : E) : Matrix ι ι ℂ :=
  1-modifiedK a b u y

theorem modifiedPositiveProduct_metric_diagonalization
    {u : E → ℝ} {y : E} (hu : ContDiffAt ℝ 2 u y) (hy : u y < 0)
    (a b : ι → E) (hpos : (complexHessian a b u y).PosDef) :
    ∃ (Q : Matrix ι ι ℂ) (k : ι → ℝ), IsUnit Q.det ∧
      Q*modifiedA a b u y*Q.conjTranspose=1 ∧
      Q*modifiedPositiveProduct a b u y*Q⁻¹=Matrix.diagonal (fun j => (k j : ℂ)) ∧ ∀ j, 0 ≤ k j := by
  obtain ⟨Q,d,hQ,hA,hd,hB⟩ := exists_simultaneous_takagi
    (modifiedA_posDef a b hy hpos) (modifiedB_transpose hu a b)
  have hs := schur_quotient_complex_similarity Q (modifiedA a b u y) (modifiedB a b u y) hQ
  rw [hA,hB,matrixSchur_one_real_diagonal,inv_one,Matrix.mul_one] at hs
  change Matrix.diagonal (fun j => ((1-d j^2 : ℝ) : ℂ))=Q*modifiedK a b u y*Q⁻¹ at hs
  refine ⟨Q,(fun j => d j^2),hQ,hA,?_,fun j => sq_nonneg _⟩
  unfold modifiedPositiveProduct
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.mul_nonsing_inv Q hQ,← hs]
  ext l m
  by_cases hlm : l=m
  · subst m; simp
  · simp [Matrix.diagonal_apply,Matrix.one_apply,hlm]

theorem modifiedPositiveProduct_normalized_diagonal (a b : ι → E) (u : E → ℝ) (x : E)
    (d : ι → ℝ) (hI : modifiedA a b u x=1)
    (hD : modifiedB a b u x=Matrix.diagonal (fun j => (d j : ℂ))) :
    modifiedPositiveProduct a b u x=Matrix.diagonal (fun j => ((d j^2 : ℝ) : ℂ)) := by
  unfold modifiedPositiveProduct
  rw [modifiedK_normalized_diagonal_general a b d hI hD]
  ext l m
  by_cases hlm : l=m
  · subst m; simp
  · simp [Matrix.diagonal_apply,Matrix.one_apply,hlm]

variable [CompleteSpace E]

theorem modifiedPositiveProduct_tracePower_second_local_uniform
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d0 : ι → ℝ) (hI0 : modifiedA a b u x=1)
    (hD0 : modifiedB a b u x=Matrix.diagonal (fun j => (d0 j : ℂ)))
    (htop : 0 < d0 i^2) (hgap0 : ∀ j, j ≠ i → d0 j^2 < d0 i^2) (v w s t : E) :
    ∃ S : Set E, S ∈ 𝓝 x ∧ S ⊆ U ∧ ∃ C q : ℝ, 0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧
      (∀ n : ℕ, ∀ y ∈ S,
        ‖dz s t (dz v w (fun z => (tracePowerRoot (modifiedPositiveProduct a b u) (n+2) z : ℂ))) y-
          dz s t (dz v w (fun z => (largestRealEigenvalue (modifiedPositiveProduct a b u z) : ℂ))) y‖ ≤
            C*((n : ℝ)+1)*q^n) ∧
      TendstoUniformlyOn
        (fun n y => dz s t (dz v w (fun z => (tracePowerRoot (modifiedPositiveProduct a b u) (n+2) z : ℂ))) y)
        (fun y => dz s t (dz v w (fun z => (largestRealEigenvalue (modifiedPositiveProduct a b u z) : ℂ))) y) atTop S := by
  apply tracePowerRoot_second_local_uniform_of_metric_diagonalization (A := modifiedA a b u) hU _ hx
    (modifiedA_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) a b)
    (ne_of_gt (modifiedA_posDef a b (hneg x hx) (hpos x hx)).det_pos) _
    i (fun j => d0 j^2) (modifiedPositiveProduct_normalized_diagonal a b u x d0 hI0 hD0)
    hgap0 htop v w s t
  · intro l m y hy
    exact (contDiffAt_const.sub (modifiedK_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hy))
      (hneg y hy) a b (hpos y hy) l m)).contDiffWithinAt
  · intro y hy
    exact modifiedPositiveProduct_metric_diagonalization
      ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) (hneg y hy) a b (hpos y hy)

end PowerConvexity
