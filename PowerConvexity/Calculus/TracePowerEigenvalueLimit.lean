import PowerConvexity.Calculus.TracePowerSecondLimit
import PowerConvexity.Calculus.ExtremalEigenvalueDerivatives
import PowerConvexity.Algebra.WeightedSpectralContraction

/-! # B3-3: pointwise derivative-limit identification with the actual largest root

The trace-power limit is proved independently of the eigenvalue jet. The
identification uses the independently proved implicit-function jet theorem;
no unproved uniform convergence or exchange of derivatives and limits is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem paper_B3_3_tracePowerRoot_second_limit_actual_largest {K : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hK : ∀ i j, ContDiffOn ℝ 2 (fun y => K y i j) U)
    {x : E} (hx : x ∈ U) (k : ι → ℝ) (i : ι)
    (hdiag : K x = Matrix.diagonal (fun j => (k j:ℂ)))
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (hgap : ∀ j, j ≠ i → k j < k i)
    (htrace : ∀ n : ℕ, ∀ y ∈ U, (K y ^ (n+2)).trace.im = 0)
    (hspec : ∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im = 0)
    (a b c d : E) :
    Filter.Tendsto (fun n : ℕ => dz c d (dz a b (fun y => (tracePowerRoot K (n+2) y : ℂ))) x)
      Filter.atTop (𝓝 (dz c d (dz a b (fun y => (largestRealEigenvalue (K y):ℂ))) x)) := by
  have hjet := largestRealEigenvalue_jet (fun j l => (hK j l).contDiffAt (hU.mem_nhds hx))
    i k hdiag hgap hspec
  rw [(hjet.2.2 a b c d).2]
  have hsum := sum_complement_eq_erase (fun j =>
    (dz a b (fun y => K y i j) x * dz c d (fun y => K y j i) x +
      dz c d (fun y => K y i j) x * dz a b (fun y => K y j i) x) /
      ((k i:ℂ)-(k j:ℂ))) i
  rw [hsum]
  convert paper_B3_2_tracePowerRoot_second_limit hU hK hx k i hdiag hi h0 hgap htrace a b c d using 1
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  simp only [matrixDZ, Complex.ofReal_sub]
  ring

end PowerConvexity
