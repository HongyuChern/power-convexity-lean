import PowerConvexity.Calculus.SimpleEigenvalueBranch

/-! # Frozen Appendix B in arbitrary dimension

The extrema are the actual supremum/infimum of real eigenvalues. Local C²
regularity is proved from the matrix entries and a simple extreme at the base
point. The necessary real-spectrum neighborhood is explicit; self-adjointness
in the displayed coordinates is not required.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Topology ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def largestRealEigenvalue (K : Matrix ι ι ℂ) : ℝ :=
  sSup {t : ℝ | Module.End.HasEigenvalue K.toLin' (t:ℂ)}

noncomputable def smallestRealEigenvalue (K : Matrix ι ι ℂ) : ℝ :=
  sInf {t : ℝ | Module.End.HasEigenvalue K.toLin' (t:ℂ)}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Complete actual jet in `B1-1/B1-2` and `B2-1/B2-2`, with any constant
Wirtinger directions. Setting b or e to zero also includes real directions. -/
def SimpleRealEigenvalueJet (K : E → Matrix ι ι ℂ) (f : E → ℝ)
    (x : E) (i : ι) (d : ι → ℝ) : Prop :=
  ContDiffAt ℝ 2 f x ∧ f x = d i ∧ ∀ a b c e : E,
    dz a b (fun y => (f y:ℂ)) x = dz a b (fun y => K y i i) x ∧
    dz c e (dz a b (fun y => (f y:ℂ))) x = dz c e (dz a b (fun y => K y i i)) x +
      ∑ j : {j : ι // j ≠ i},
        (dz a b (fun y => K y i j) x * dz c e (fun y => K y j i) x +
          dz c e (fun y => K y i j) x * dz a b (fun y => K y j i) x) /
          ((d i:ℂ)-(d j:ℂ))

theorem simpleRealEigenvalueJet_of_branch
    {K : E → Matrix ι ι ℂ} {ell : E → ℂ} {f : E → ℝ} {x : E}
    (hK : ∀ j k, ContDiffAt ℝ 2 (fun y => K y j k) x)
    (hell : ContDiffAt ℝ 2 ell x) (i : ι) (d : ι → ℝ)
    (hdiag : K x = Matrix.diagonal (fun j => (d j:ℂ))) (hellx : ell x = (d i:ℂ))
    (hgap : ∀ j, j ≠ i → d j ≠ d i)
    (hroot : ∀ᶠ y in 𝓝 x, eigenvalueSchur (K y) i (ell y) = 0)
    (heq : (fun y => (f y:ℂ)) =ᶠ[𝓝 x] ell) :
    SimpleRealEigenvalueJet K f x i d := by
  have heR : f =ᶠ[𝓝 x] (fun y => (ell y).re) := by
    filter_upwards [heq] with y hy
    exact congrArg Complex.re hy
  refine ⟨(Complex.reCLM.contDiff.contDiffAt.comp x hell).congr_of_eventuallyEq heR,?_,?_⟩
  · have h := congrArg Complex.re (heq.eq_of_nhds.trans hellx)
    exact h
  · intro a b c e
    have h := simple_schur_root_derivatives hK hell i (fun j => (d j:ℂ)) hdiag hellx
      (fun j hj he => (hgap j hj) (Complex.ofReal_injective he))
      hroot a b c e
    rw [dz_congr_nhds heq, dz_dz_congr_nhds heq]
    exact h

/-- Frozen `lem:derivates_min_eig`, largest-eigenvalue case, with the necessary
local real-spectrum condition. No differentiable eigenvalue is assumed. -/
theorem largestRealEigenvalue_jet
    {K : E → Matrix ι ι ℂ} {x : E} (hK : ∀ j k, ContDiffAt ℝ 2 (fun y => K y j k) x)
    (i : ι) (d : ι → ℝ) (hdiag : K x = Matrix.diagonal (fun j => (d j:ℂ)))
    (hmax : ∀ j, j ≠ i → d j < d i)
    (hreal : ∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im = 0) :
    SimpleRealEigenvalueJet K (fun y => largestRealEigenvalue (K y)) x i d := by
  have hgap : ∀ j, j ≠ i → (d j:ℂ) ≠ (d i:ℂ) := by
    intro j hj he
    have := congrArg Complex.re he
    exact (hmax j hj).ne this
  obtain ⟨ell,hell,hellx,heig,hunique,hroot⟩ :=
    exists_contDiff_simple_eigenvalue hK i (fun j => (d j:ℂ)) hdiag hgap
  have hg := simple_eigenvalue_isGreatest_eventually (fun j k => (hK j k).continuousAt)
    hell.continuousAt i d hdiag hellx hmax heig hunique hreal
  apply simpleRealEigenvalueJet_of_branch hK hell i d hdiag hellx
    (fun j hj => (hmax j hj).ne) hroot
  filter_upwards [hg,heig,hreal] with y hy hey hry
  rw [largestRealEigenvalue,hy.csSup_eq]
  apply Complex.ext <;> simp [hry _ hey]

/-- Frozen `lem:derivates_min_eig`, smallest-eigenvalue case, in the same
generality as the largest-root theorem. -/
theorem smallestRealEigenvalue_jet
    {K : E → Matrix ι ι ℂ} {x : E} (hK : ∀ j k, ContDiffAt ℝ 2 (fun y => K y j k) x)
    (i : ι) (d : ι → ℝ) (hdiag : K x = Matrix.diagonal (fun j => (d j:ℂ)))
    (hmin : ∀ j, j ≠ i → d i < d j)
    (hreal : ∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im = 0) :
    SimpleRealEigenvalueJet K (fun y => smallestRealEigenvalue (K y)) x i d := by
  have hgap : ∀ j, j ≠ i → (d j:ℂ) ≠ (d i:ℂ) := by
    intro j hj he
    have := congrArg Complex.re he
    exact (hmin j hj).ne' this
  obtain ⟨ell,hell,hellx,heig,hunique,hroot⟩ :=
    exists_contDiff_simple_eigenvalue hK i (fun j => (d j:ℂ)) hdiag hgap
  have hg := simple_eigenvalue_isLeast_eventually (fun j k => (hK j k).continuousAt)
    hell.continuousAt i d hdiag hellx hmin heig hunique hreal
  apply simpleRealEigenvalueJet_of_branch hK hell i d hdiag hellx
    (fun j hj => (hmin j hj).ne') hroot
  filter_upwards [hg,heig,hreal] with y hy hey hry
  rw [smallestRealEigenvalue,hy.csInf_eq]
  apply Complex.ext <;> simp [hry _ hey]

end PowerConvexity
