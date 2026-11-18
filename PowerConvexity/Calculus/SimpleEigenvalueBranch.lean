import PowerConvexity.Algebra.EigenvalueSchur
import PowerConvexity.Calculus.SimpleEigenvalueDerivatives

/-! # Actual local simple eigenvalue and its uniqueness -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set Metric
open scoped Topology ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_contDiff_simple_eigenvalue
    {K : E → Matrix ι ι ℂ} {x : E} (hK : ∀ j k, ContDiffAt ℝ 2 (fun y => K y j k) x)
    (i : ι) (d : ι → ℂ) (hdiag : K x = Matrix.diagonal d)
    (hgap : ∀ j, j ≠ i → d j ≠ d i) :
    ∃ ell : E → ℂ, ContDiffAt ℝ 2 ell x ∧ ell x = d i ∧
      (∀ᶠ y in 𝓝 x, Module.End.HasEigenvalue (K y).toLin' (ell y)) ∧
      (∀ᶠ p : E × ℂ in 𝓝 (x,d i),
        Module.End.HasEigenvalue (K p.1).toLin' p.2 ↔ ell p.1 = p.2) ∧
      (∀ᶠ y in 𝓝 x, eigenvalueSchur (K y) i (ell y) = 0) := by
  obtain ⟨ell,hell,hellx,hroot,hunique⟩ := exists_contDiff_simple_schur_root hK i d hdiag hgap
  have hD (j k : {j : ι // j ≠ i}) : ContDiffAt ℝ 2
      (fun p : E × ℂ => eigenvalueComplement (K p.1) i p.2 j k) (x,d i) :=
    ((hK j k).comp (x,d i) contDiffAt_fst).sub (contDiffAt_snd.mul contDiffAt_const)
  have hd : (eigenvalueComplement (K x) i (d i)).det ≠ 0 := by
    rw [hdiag]
    exact eigenvalueComplement_diagonal_det_ne_zero d i hgap
  have hn := (field_det_contDiffAt hD).continuousAt.eventually_ne hd
  have hp : ∀ᶠ p : E × ℂ in 𝓝 (x,d i),
      Module.End.HasEigenvalue (K p.1).toLin' p.2 ↔ ell p.1 = p.2 := by
    filter_upwards [hn,hunique] with p hdp hup
    exact (eigenvalueSchur_eq_zero_iff (K p.1) i p.2 hdp).symm.trans hup
  have hc : Tendsto (fun y => (y,ell y)) (𝓝 x) (𝓝 (x,d i)) := by
    simpa only [ContinuousAt, id_eq, hellx] using continuousAt_id.prodMk hell.continuousAt
  refine ⟨ell,hell,hellx,?_,hp,hroot⟩
  filter_upwards [hc.eventually hp] with y hy
  exact hy.mpr rfl

noncomputable def matrixRowOffNorm (K : Matrix ι ι ℂ) (j : ι) : ℝ :=
  ∑ k ∈ Finset.univ.erase j, ‖K j k‖

theorem matrixRowOffNorm_continuousAt {K : E → Matrix ι ι ℂ} {x : E}
    (hK : ∀ j k, ContinuousAt (fun y => K y j k) x) (j : ι) :
    ContinuousAt (fun y => matrixRowOffNorm (K y) j) x :=
  tendsto_finsetSum _ (fun k _ => (hK j k).norm)

theorem matrixRowOffNorm_diagonal (d : ι → ℂ) (j : ι) :
    matrixRowOffNorm (Matrix.diagonal d) j = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  rw [Matrix.diagonal_apply_ne d (Ne.symm (Finset.mem_erase.mp hk).1), norm_zero]

/-- An actual eigenvalue branch, isolated at a real simple largest diagonal
entry, is the largest real eigenvalue nearby. The argument permits matrices
which are non-Hermitian in the displayed coordinates. -/
theorem simple_eigenvalue_isGreatest_eventually
    {K : E → Matrix ι ι ℂ} {ell : E → ℂ} {x : E}
    (hK : ∀ j k, ContinuousAt (fun y => K y j k) x) (hell : ContinuousAt ell x)
    (i : ι) (d : ι → ℝ) (hdiag : K x = Matrix.diagonal (fun j => (d j:ℂ)))
    (hellx : ell x = (d i:ℂ)) (hmax : ∀ j, j ≠ i → d j < d i)
    (heig : ∀ᶠ y in 𝓝 x, Module.End.HasEigenvalue (K y).toLin' (ell y))
    (hunique : ∀ᶠ p : E × ℂ in 𝓝 (x,(d i:ℂ)),
      Module.End.HasEigenvalue (K p.1).toLin' p.2 ↔ ell p.1 = p.2)
    (hreal : ∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im = 0) :
    ∀ᶠ y in 𝓝 x, IsGreatest {t : ℝ | Module.End.HasEigenvalue (K y).toLin' (t:ℂ)} (ell y).re := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hunique
  have hrad : ∀ᶠ y in 𝓝 x,
      matrixRowOffNorm (K y) i + ‖K y i i-(d i:ℂ)‖ < δ := by
    have hc : ContinuousAt (fun y => matrixRowOffNorm (K y) i + ‖K y i i-(d i:ℂ)‖) x :=
      (matrixRowOffNorm_continuousAt hK i).add ((hK i i).sub continuousAt_const).norm
    have hx : matrixRowOffNorm (K x) i + ‖K x i i-(d i:ℂ)‖ < δ := by
      simpa [hdiag,matrixRowOffNorm_diagonal] using hδ
    exact hc.eventually (gt_mem_nhds hx)
  have hother : ∀ᶠ y in 𝓝 x, ∀ j, j ≠ i →
      (K y j j).re + matrixRowOffNorm (K y) j < (ell y).re := by
    apply eventually_all.mpr
    intro j
    by_cases hj : j = i
    · exact Eventually.of_forall fun _ h => (h hj).elim
    · have hleft := (Complex.continuous_re.continuousAt.comp (hK j j)).add
          (matrixRowOffNorm_continuousAt hK j)
      have hright := Complex.continuous_re.continuousAt.comp hell
      have hx : (K x j j).re + matrixRowOffNorm (K x) j < (ell x).re := by
        simpa [hdiag,hellx,matrixRowOffNorm_diagonal] using hmax j hj
      exact (hleft.eventually_lt hright hx).mono fun y hy _ => hy
  filter_upwards [heig,hreal,hrad,hother,Metric.ball_mem_nhds x hδ] with y hey hry hri hoy hxy
  have hre : ((ell y).re:ℂ) = ell y := by
    apply Complex.ext <;> simp [hry _ hey]
  refine ⟨by simpa only [Set.mem_ofPred_eq,hre] using hey, ?_⟩
  intro t ht
  obtain ⟨j,hj⟩ := eigenvalue_mem_ball ht
  have hnorm : ‖(t:ℂ)-K y j j‖ ≤ matrixRowOffNorm (K y) j := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, matrixRowOffNorm] using hj
  by_cases hji : j = i
  · subst j
    have htδ : dist (t:ℂ) (d i:ℂ) < δ := by
      calc
        _ ≤ ‖(t:ℂ)-K y i i‖ + ‖K y i i-(d i:ℂ)‖ := by
          simpa only [dist_eq_norm] using dist_triangle (t:ℂ) (K y i i) (d i:ℂ)
        _ ≤ matrixRowOffNorm (K y) i + ‖K y i i-(d i:ℂ)‖ := by linarith
        _ < δ := hri
    have hp := hball (show (y,(t:ℂ)) ∈ Metric.ball (x,(d i:ℂ)) δ by
      simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using And.intro hxy htδ)
    have he := congrArg Complex.re (hp.mp ht)
    simpa using he.ge
  · have hle : t ≤ (K y j j).re + matrixRowOffNorm (K y) j := by
      have hr := Complex.re_le_norm ((t:ℂ)-K y j j)
      simp only [Complex.sub_re,Complex.ofReal_re] at hr
      linarith
    exact hle.trans (hoy j hji).le

theorem matrix_hasEigenvalue_neg_iff (K : Matrix ι ι ℂ) (z : ℂ) :
    Module.End.HasEigenvalue (-K).toLin' z ↔ Module.End.HasEigenvalue K.toLin' (-z) := by
  rw [map_neg, Module.End.hasEigenvalue_neg_iff]

theorem simple_eigenvalue_isLeast_eventually
    {K : E → Matrix ι ι ℂ} {ell : E → ℂ} {x : E}
    (hK : ∀ j k, ContinuousAt (fun y => K y j k) x) (hell : ContinuousAt ell x)
    (i : ι) (d : ι → ℝ) (hdiag : K x = Matrix.diagonal (fun j => (d j:ℂ)))
    (hellx : ell x = (d i:ℂ)) (hmin : ∀ j, j ≠ i → d i < d j)
    (heig : ∀ᶠ y in 𝓝 x, Module.End.HasEigenvalue (K y).toLin' (ell y))
    (hunique : ∀ᶠ p : E × ℂ in 𝓝 (x,(d i:ℂ)),
      Module.End.HasEigenvalue (K p.1).toLin' p.2 ↔ ell p.1 = p.2)
    (hreal : ∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im = 0) :
    ∀ᶠ y in 𝓝 x, IsLeast {t : ℝ | Module.End.HasEigenvalue (K y).toLin' (t:ℂ)} (ell y).re := by
  have hd : -K x = Matrix.diagonal (fun j => (-d j:ℂ)) := by
    rw [hdiag]
    simp only [Complex.ofReal_neg, Matrix.diagonal_neg]
  have he : ∀ᶠ y in 𝓝 x, Module.End.HasEigenvalue (-K y).toLin' (-ell y) := by
    filter_upwards [heig] with y hy
    rw [matrix_hasEigenvalue_neg_iff,neg_neg]
    exact hy
  have ht : Tendsto (fun p : E × ℂ => (p.1,-p.2))
      (𝓝 (x,(-d i:ℂ))) (𝓝 (x,(d i:ℂ))) := by
    have h : ContinuousAt (fun p : E × ℂ => (p.1,-p.2)) (x,(-d i:ℂ)) :=
      continuousAt_fst.prodMk continuousAt_snd.neg
    simpa only [ContinuousAt, Complex.ofReal_neg, neg_neg] using h
  have hu : ∀ᶠ p : E × ℂ in 𝓝 (x,(-d i:ℂ)),
      Module.End.HasEigenvalue (-K p.1).toLin' p.2 ↔ -ell p.1 = p.2 := by
    filter_upwards [ht.eventually hunique] with p hp
    rw [matrix_hasEigenvalue_neg_iff, hp, neg_eq_iff_eq_neg]
  have hr : ∀ᶠ y in 𝓝 x, ∀ z : ℂ,
      Module.End.HasEigenvalue (-K y).toLin' z → z.im = 0 := by
    filter_upwards [hreal] with y hy z hz
    have h := hy (-z) ((matrix_hasEigenvalue_neg_iff (K y) z).mp hz)
    simpa only [Complex.neg_im, neg_eq_zero] using h
  have hn := simple_eigenvalue_isGreatest_eventually (K := fun y => -K y) (ell := fun y => -ell y)
    (fun j k => (hK j k).neg) hell.neg i (fun j => -d j)
    (by simpa only [Complex.ofReal_neg] using hd)
    (by simpa only [Complex.ofReal_neg] using congrArg Neg.neg hellx)
    (fun j hj => neg_lt_neg (hmin j hj)) he
    (by simpa only [Complex.ofReal_neg] using hu) hr
  filter_upwards [hn] with y hy
  refine ⟨?_,?_⟩
  · have h := (matrix_hasEigenvalue_neg_iff (K y) ((-ell y).re:ℂ)).mp hy.1
    change Module.End.HasEigenvalue (K y).toLin' ((ell y).re:ℂ)
    simpa only [Complex.neg_re,Complex.ofReal_neg,neg_neg] using h
  · intro t ht
    have hte : Module.End.HasEigenvalue (-K y).toLin' ((-t:ℝ):ℂ) := by
      rw [matrix_hasEigenvalue_neg_iff,Complex.ofReal_neg,neg_neg]
      exact ht
    have h := hy.2 hte
    simpa only [Complex.neg_re, neg_le_neg_iff] using h

end PowerConvexity
