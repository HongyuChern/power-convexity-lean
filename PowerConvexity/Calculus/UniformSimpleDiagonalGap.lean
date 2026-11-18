import PowerConvexity.Calculus.SimpleEigenvalueUniformGap
import PowerConvexity.Algebra.SimpleDiagonalMultiplicity
import PowerConvexity.Algebra.TakagiSchurSpectrumGeneral

/-! # Uniform local spectral gaps with multiplicity included

Continuity preserves a nonzero complementary minor at the actual simple
root. The rank argument then excludes repeated copies of the top root in
any diagonalizing frame, completing the distinct-value gap estimate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem simple_largest_eigenvalue_uniform_diagonal_gap
    {K : E → Matrix ι ι ℂ} {x : E}
    (hK : ∀ j k, ContDiffAt ℝ 2 (fun y => K y j k) x)
    (i : ι) (d : ι → ℝ) (hdiag : K x = Matrix.diagonal (fun j => (d j : ℂ)))
    (hmax : ∀ j, j ≠ i → d j < d i)
    (hreal : ∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im = 0) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ y in 𝓝 x, ∀ (Q : Matrix ι ι ℂ), IsUnit Q.det →
      ∀ (k : ι → ℝ), Q*K y*Q⁻¹ = Matrix.diagonal (fun j => (k j : ℂ)) →
      ∀ j, k j = largestRealEigenvalue (K y) → ∀ l, l ≠ j → γ ≤ k j-k l := by
  letI : Nonempty ι := ⟨i⟩
  have hj := largestRealEigenvalue_jet hK i d hdiag hmax hreal
  have hLam : ContDiffAt ℝ 2 (fun y => (largestRealEigenvalue (K y) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hj.1
  have hD (j k : {j : ι // j ≠ i}) : ContDiffAt ℝ 2
      (fun y => eigenvalueComplement (K y) i (largestRealEigenvalue (K y) : ℂ) j k) x :=
    (hK j k).sub (hLam.mul contDiffAt_const)
  have hminor0 : (eigenvalueComplement (K x) i (largestRealEigenvalue (K x) : ℂ)).det ≠ 0 := by
    have hv : largestRealEigenvalue (K x) = d i := hj.2.1
    rw [hv,hdiag]
    apply eigenvalueComplement_diagonal_det_ne_zero
    intro j hji he
    exact (hmax j hji).ne (Complex.ofReal_injective he)
  have hm := (field_det_contDiffAt hD).continuousAt.eventually_ne hminor0
  obtain ⟨γ,hγ,hg⟩ := simple_largest_eigenvalue_uniform_gap hK i d hdiag hmax hreal
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hm,hg] with y hmy hgy
  intro Q hQ k hk j hjLam l hlj
  have hne := diagonal_root_unique_of_complement_det_ne_zero (K y) Q i
    (largestRealEigenvalue (K y) : ℂ) hmy hQ (fun r => (k r : ℂ)) hk j
    (congrArg Complex.ofReal hjLam) l hlj
  have hneR : k l ≠ largestRealEigenvalue (K y) := fun he => hne (congrArg Complex.ofReal he)
  have heig : Module.End.HasEigenvalue (K y).toLin' (k l : ℂ) := by
    apply (hasEigenvalue_of_charpoly_eq (charpoly_complex_similarity Q (K y) hQ) _).mp
    rw [hk]
    exact (real_diagonal_hasEigenvalue_iff k (k l)).mpr ⟨l,rfl⟩
  rw [hjLam]
  exact hgy (k l) heig hneR

/-- The same result with the selected entry specified by the ordinary
non-strict ordering of a diagonal spectrum, not by a supplied strict gap. -/
theorem simple_largest_eigenvalue_uniform_ordered_gap
    {K : E → Matrix ι ι ℂ} {x : E}
    (hK : ∀ j k, ContDiffAt ℝ 2 (fun y => K y j k) x)
    (i : ι) (d : ι → ℝ) (hdiag : K x = Matrix.diagonal (fun j => (d j : ℂ)))
    (hmax : ∀ j, j ≠ i → d j < d i)
    (hreal : ∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im = 0) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ y in 𝓝 x, ∀ (Q : Matrix ι ι ℂ), IsUnit Q.det →
      ∀ (k : ι → ℝ), Q*K y*Q⁻¹ = Matrix.diagonal (fun j => (k j : ℂ)) →
      ∀ j, (∀ l, k l ≤ k j) → ∀ l, l ≠ j → γ ≤ k j-k l := by
  letI : Nonempty ι := ⟨i⟩
  obtain ⟨γ,hγ,hgap⟩ := simple_largest_eigenvalue_uniform_diagonal_gap hK i d hdiag hmax hreal
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hgap] with y hy
  intro Q hQ k hk j hj
  apply hy Q hQ k hk j
  have he : IsGreatest {t : ℝ | Module.End.HasEigenvalue (K y).toLin' (t : ℂ)} (k j) := by
    have heq (t : ℝ) : Module.End.HasEigenvalue (K y).toLin' (t : ℂ) ↔ ∃ l, k l=t := by
      rw [← hasEigenvalue_of_charpoly_eq (charpoly_complex_similarity Q (K y) hQ) (t : ℂ),hk]
      exact real_diagonal_hasEigenvalue_iff k t
    refine ⟨(heq (k j)).mpr ⟨j,rfl⟩,?_⟩
    intro t ht
    obtain ⟨l,rfl⟩ := (heq t).mp ht
    exact hj l
  exact he.csSup_eq.symm

end PowerConvexity
