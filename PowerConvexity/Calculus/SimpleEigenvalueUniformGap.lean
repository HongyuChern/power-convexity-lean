import PowerConvexity.Calculus.ExtremalEigenvalueDerivatives

/-! # A common local gap for the actual simple largest root

This controls every distinct real eigenvalue near the base point. It does
not replace algebraic simplicity by separation of distinct values.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Filter Set Metric
open scoped Topology ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem simple_largest_eigenvalue_uniform_gap
    {K : E → Matrix ι ι ℂ} {x : E}
    (hK : ∀ j k, ContDiffAt ℝ 2 (fun y => K y j k) x)
    (i : ι) (d : ι → ℝ) (hdiag : K x = Matrix.diagonal (fun j => (d j : ℂ)))
    (hmax : ∀ j, j ≠ i → d j < d i)
    (hreal : ∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im = 0) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ y in 𝓝 x, ∀ t : ℝ,
      Module.End.HasEigenvalue (K y).toLin' (t : ℂ) →
      t ≠ largestRealEigenvalue (K y) → γ ≤ largestRealEigenvalue (K y)-t := by
  letI : Nonempty ι := ⟨i⟩
  have hgap : ∀ j, j ≠ i → (d j : ℂ) ≠ (d i : ℂ) := by
    intro j hj he
    exact (hmax j hj).ne (Complex.ofReal_injective he)
  obtain ⟨ell,hell,hellx,heig,hunique,_hroot⟩ :=
    exists_contDiff_simple_eigenvalue hK i (fun j => (d j : ℂ)) hdiag hgap
  let r : ι → ℝ := fun j => if j=i then 1 else (d i-d j)/2
  have hr : ∀ j, 0 < r j := by
    intro j
    by_cases hj : j=i
    · simp [r,hj]
    · have hh := hmax j hj
      dsimp [r]
      rw [if_neg hj]
      linarith
  obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ r Finset.univ_nonempty
  let γ := r j
  have hγ : 0 < γ := hr j
  have hγgap (l : ι) (hl : l ≠ i) : 2*γ ≤ d i-d l := by
    have h := hj l (Finset.mem_univ l)
    change γ ≤ r l at h
    simp only [r, if_neg hl] at h
    linarith
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hunique
  have hrad : ∀ᶠ y in 𝓝 x,
      matrixRowOffNorm (K y) i+‖K y i i-(d i : ℂ)‖ < δ := by
    have hc : ContinuousAt (fun y => matrixRowOffNorm (K y) i+‖K y i i-(d i : ℂ)‖) x :=
      (matrixRowOffNorm_continuousAt (fun l m => (hK l m).continuousAt) i).add
        ((hK i i).continuousAt.sub continuousAt_const).norm
    apply hc.eventually (gt_mem_nhds _)
    simpa [hdiag,matrixRowOffNorm_diagonal] using hδ
  have hother : ∀ᶠ y in 𝓝 x, ∀ l, l ≠ i →
      (K y l l).re+matrixRowOffNorm (K y) l+γ < (ell y).re := by
    apply eventually_all.mpr
    intro l
    by_cases hl : l=i
    · exact Eventually.of_forall fun _ h => (h hl).elim
    · have hleft : ContinuousAt (fun y => (K y l l).re+matrixRowOffNorm (K y) l+γ) x :=
        ((Complex.continuous_re.continuousAt.comp (hK l l).continuousAt).add
        (matrixRowOffNorm_continuousAt (fun p q => (hK p q).continuousAt) l)).add continuousAt_const
      have hright := Complex.continuous_re.continuousAt.comp hell.continuousAt
      have hb : (K x l l).re+matrixRowOffNorm (K x) l+γ < (ell x).re := by
        simp only [hdiag,Matrix.diag_apply,Matrix.diagonal_apply_eq,matrixRowOffNorm_diagonal,
          Complex.ofReal_re,hellx,add_zero]
        linarith [hγgap l hl]
      exact (hleft.eventually_lt hright hb).mono fun y hy _ => hy
  have hg := simple_eigenvalue_isGreatest_eventually (fun l m => (hK l m).continuousAt)
    hell.continuousAt i d hdiag hellx hmax heig hunique hreal
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hg,hrad,hother,Metric.ball_mem_nhds x hδ] with y hgy hri hoy hxy
  intro t ht hne
  have heq : largestRealEigenvalue (K y) = (ell y).re := hgy.csSup_eq
  rw [heq] at hne ⊢
  obtain ⟨l,hl⟩ := eigenvalue_mem_ball ht
  have hnorm : ‖(t : ℂ)-K y l l‖ ≤ matrixRowOffNorm (K y) l := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,matrixRowOffNorm] using hl
  by_cases hli : l=i
  · subst l
    have htδ : dist (t : ℂ) (d i : ℂ) < δ := by
      calc
        _ ≤ ‖(t : ℂ)-K y i i‖+‖K y i i-(d i : ℂ)‖ := by
          simpa only [dist_eq_norm] using dist_triangle (t : ℂ) (K y i i) (d i : ℂ)
        _ ≤ matrixRowOffNorm (K y) i+‖K y i i-(d i : ℂ)‖ := by linarith
        _ < δ := hri
    have hp := hball (show (y,(t : ℂ)) ∈ Metric.ball (x,(d i : ℂ)) δ by
      simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hxy htδ)
    have he := congrArg Complex.re (hp.mp ht)
    exact (hne (by simpa using he.symm)).elim
  · have hrn := Complex.re_le_norm ((t : ℂ)-K y l l)
    simp only [Complex.sub_re,Complex.ofReal_re] at hrn
    have ho := hoy l hli
    linarith

end PowerConvexity
