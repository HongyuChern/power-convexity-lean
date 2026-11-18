import PowerConvexity.Calculus.QuadraticMinimumAttainedGeneral
import PowerConvexity.Calculus.SeparationTestQuadraticsGeneral
import PowerConvexity.Calculus.PowerMixedPositive
import PowerConvexity.Algebra.SimpleLeastSpectrum

/-! # Appendix A: actual L2 quadratic spectral separation in arbitrary dimension -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open Set MeasureTheory
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem pluriharmonic_quadratic_minimizer_unique_takagi_maximum
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis ι ℂ E) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    {ε : ℝ} (hε : 0 < ε)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → u x+q x < 0)
    (hpos : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε →
      (modifiedA e (fun j => Complex.I • e j) (fun y => u y+q y) x).PosDef)
    {q : E → ℝ} (hq : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q)
    (hE : quadraticL2Energy μ K q ≤ ε)
    (hmin : ∀ r : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) r →
      quadraticL2Energy μ K r ≤ ε →
      modifiedSigma e (fun j => Complex.I • e j) (fun y => u y+q y) x ≤
        modifiedSigma e (fun j => Complex.I • e j) (fun y => u y+r y) x) :
    ∃ (Q : Matrix ι ι ℂ) (d : ι → ℝ) (i : ι), IsUnit Q.det ∧
      Q*(modifiedA e (fun j => Complex.I • e j) (fun y => u y+q y) x)*Q.conjTranspose = 1 ∧
      (∀ j, 0 ≤ d j) ∧
      Q*(modifiedB e (fun j => Complex.I • e j) (fun y => u y+q y) x)*Q.transpose =
        Matrix.diagonal (fun j => (d j:ℂ)) ∧
      (∀ j, d j ≤ d i) ∧ ∀ j, j ≠ i → d j < d i := by
  let a0 : ι → E := e
  let b0 : ι → E := fun j => Complex.I • e j
  have hjet (r : E → ℝ) (hr : IsPluriharmonicQuadratic a0 b0 r) :
      ContDiffAt ℝ 2 (fun y => u y+r y) x :=
    hu.add (IsQuadraticPolynomial_contDiff hr.1 2).contDiffAt
  obtain ⟨Q,d,hQ,hQA,hd,hQB⟩ := exists_simultaneous_takagi
    (hpos q hq hE) (modifiedB_transpose (hjet q hq) a0 b0)
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
  have hi' (j : ι) : d j ≤ d i := hi j (Finset.mem_univ _)
  refine ⟨Q,d,i,hQ,hQA,hd,hQB,hi',?_⟩
  intro j hji
  by_contra hnot
  have heq : d j = d i := le_antisymm (hi' j) (le_of_not_gt hnot)
  let a := complexFrameReal Q a0 b0
  let b := complexFrameImag Q a0 b0
  have hAc : modifiedA a b (fun y => u y+q y) x = 1 := by
    rw [modifiedA_complexFrame (hjet q hq) (hneg q hq hE)]
    exact hQA
  have hBc : modifiedB a b (fun y => u y+q y) x = Matrix.diagonal (fun k => (d k:ℂ)) := by
    rw [modifiedB_complexFrame (hjet q hq) (hneg q hq hE),hQB]
  have hposc (r : E → ℝ) (hr : IsPluriharmonicQuadratic a0 b0 r)
      (hEr : quadraticL2Energy μ K r ≤ ε) : (modifiedA a b (fun y => u y+r y) x).PosDef := by
    rw [modifiedA_complexFrame (hjet r hr) (hneg r hr hEr)]
    exact (posDef_complex_congruence_iff Q _ hQ).mpr (hpos r hr hEr)
  have hsigc (r : E → ℝ) (hr : IsPluriharmonicQuadratic a0 b0 r)
      (hEr : quadraticL2Energy μ K r ≤ ε) :
      modifiedSigma a b (fun y => u y+r y) x = modifiedSigma a0 b0 (fun y => u y+r y) x :=
    modifiedSigma_complexFrame (hjet r hr) (hneg r hr hEr) Q hQ a0 b0
  rcases eq_or_lt_of_le (hd i) with hz | hdpos
  · have hroot : modifiedSigma a0 b0 (fun y => u y+q y) x = 1 := by
      have hr := schur_quotient_takagi_minimum _ _ Q d hQ hQA hQB hd i hi'
      simpa only [← hz,zero_pow (by decide : 2 ≠ 0),sub_zero,
        modifiedSigma,modifiedK,modifiedSchur,a0,b0] using hr
    have hzero : IsPluriharmonicQuadratic a0 b0 (fun _ : E => 0) :=
      ⟨(quadraticSubmodule E).zero_mem,(pluriharmonicQuadraticSubmodule a0 b0).zero_mem⟩
    have hEzero : quadraticL2Energy μ K (fun _ : E => 0) ≤ ε := by
      simpa [quadraticL2Energy] using hε.le
    have hAu : (modifiedA a b u x).PosDef := by simpa using hposc _ hzero hEzero
    have hsig0 : modifiedSigma a b u x = 1 := by
      have hlow := hmin _ hzero hEzero
      rw [hroot] at hlow
      have hc := hsigc _ hzero hEzero
      simp only [add_zero] at hlow hc
      rw [← hc] at hlow
      exact le_antisymm (schur_minimum_le_one hAu (modifiedB_transpose hu a b)) hlow
    have hBu : modifiedB a b u x = 0 :=
      (schur_minimum_eq_one_iff hAu (modifiedB_transpose hu a b)).mp hsig0
    let g := frameCoordinateSquare e Q i x
    have hg := frameCoordinateSquare_pluriharmonic e Q i x
    obtain ⟨δ,hδ,hsmall⟩ := exists_positive_scaled_energy_radius μ K g hε
    let t := δ/2
    have ht : 0 < t := by dsimp [t]; linarith
    have htδ : |t| ≤ δ := by rw [abs_of_pos ht]; dsimp [t]; linarith
    let r : E → ℝ := fun y => t*g y
    have hr := IsPluriharmonicQuadratic_const_mul hg t
    have hEr : quadraticL2Energy μ K r ≤ ε := hsmall t htδ
    have hBr : modifiedB a b (fun y => u y+r y) x ≠ 0 := by
      rw [modifiedB_centered_scaled_perturbation hu
        (IsQuadraticPolynomial_contDiff hg.1 2).contDiffAt a b
        (frameCoordinateSquare_center e Q i x) (frameCoordinateSquare_fderiv_center e Q i x),
        hBu,zero_add,frameCoordinateSquare_pure_diagonal e Q hQ]
      intro he
      have he0 := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) he
      have : t = 0 := by simpa using he0
      exact ht.ne' this
    have hsr : modifiedSigma a b (fun y => u y+r y) x < 1 := by
      have ha := hposc r hr hEr
      have hb := modifiedB_transpose (hjet r hr) a b
      exact lt_of_le_of_ne (schur_minimum_le_one ha hb)
        (fun he => hBr ((schur_minimum_eq_one_iff ha hb).mp he))
    have hlow := hmin r hr hEr
    rw [hroot,← hsigc r hr hEr] at hlow
    exact (not_lt_of_ge hlow) hsr
  · obtain ⟨h,hh,hh0,hh1,hh2,hhH⟩ := exists_separation_test_quadratic e Q hQ x i j
    letI := quadraticL2NormedAddCommGroup μ hK hKi
    letI : TopologicalSpace (quadraticSubmodule E) :=
      (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
    letI := quadraticL2InnerProductSpace μ hK hKi
    letI := quadraticSubmodule_finiteDimensional (E := E)
    let P := pluriharmonicQuadraticSubmodule a0 b0
    let F : P →ₗ[ℝ] quadraticSubmodule E := P.subtype
    let pq : P := ⟨⟨q,hq.1⟩,hq.2⟩
    let ph : P := ⟨⟨h,hh.1⟩,hh.2⟩
    have hn (p : P) : ‖p‖^2 = quadraticL2Energy μ K p.val.val := quadraticL2_norm_sq μ hK hKi p.val
    apply quadraticFamily_repeated_positive_not_minimum_general F a b hu hε d hd i j
      (Ne.symm hji) hi' heq hdpos pq ph (by rw [hn]; exact hE)
      (fun p hp => hneg p.val.val ⟨p.val.property,p.property⟩ (by rwa [← hn]))
      (fun p hp => hposc p.val.val ⟨p.val.property,p.property⟩ (by rwa [← hn]))
      hh0 hh1 hh2 hAc hBc hhH
    intro p hp
    have hEp : quadraticL2Energy μ K p.val.val ≤ ε := by rwa [← hn]
    have hpclass : IsPluriharmonicQuadratic a0 b0 p.val.val := ⟨p.val.property,p.property⟩
    change modifiedSigma a b (fun y => u y+q y) x ≤ modifiedSigma a b (fun y => u y+p.val.val y) x
    rw [hsigc q hq hE,hsigc p.val.val hpclass hEp]
    exact hmin p.val.val hpclass hEp

theorem pluriharmonic_quadratic_minimizer_has_gap
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis ι ℂ E) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    {ε : ℝ} (hε : 0 < ε)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → u x+q x < 0)
    (hpos : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε →
      (modifiedA e (fun j => Complex.I • e j) (fun y => u y+q y) x).PosDef)
    {q : E → ℝ} (hq : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q)
    (hE : quadraticL2Energy μ K q ≤ ε)
    (hmin : ∀ r : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) r →
      quadraticL2Energy μ K r ≤ ε →
      modifiedSigma e (fun j => Complex.I • e j) (fun y => u y+q y) x ≤
        modifiedSigma e (fun j => Complex.I • e j) (fun y => u y+r y) x) :
    HasSimpleLeastSpectrum (modifiedK e (fun j => Complex.I • e j) (fun y => u y+q y) x) := by
  obtain ⟨Q,d,i,hQ,hQA,hd,hQB,hi,hstrict⟩ :=
    pluriharmonic_quadratic_minimizer_unique_takagi_maximum μ hK hKi e hu hε hneg hpos hq hE hmin
  exact hasSimpleLeastSpectrum_of_takagi hQ hQA hQB hd i hi hstrict

/-- Frozen `lemma:Seperation` in every finite complex dimension. Both attainment
and the gap are conclusions on the actual L2 ball. -/
theorem exists_pluriharmonic_quadratic_minimizer_with_gap
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis ι ℂ E) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    {ε : ℝ} (hε : 0 < ε)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → u x+q x < 0)
    (hpsh : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε →
      (complexHessian e (fun j => Complex.I • e j) (powerTransform (fun y => u y+q y)) x).PosDef) :
    ∃ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q ∧
      quadraticL2Energy μ K q ≤ ε ∧
      (∀ r : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) r →
        quadraticL2Energy μ K r ≤ ε →
        modifiedSigma e (fun j => Complex.I • e j) (fun y => u y+q y) x ≤
          modifiedSigma e (fun j => Complex.I • e j) (fun y => u y+r y) x) ∧
      HasSimpleLeastSpectrum (modifiedK e (fun j => Complex.I • e j) (fun y => u y+q y) x) := by
  have hpos (q : E → ℝ) (hq : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q)
      (hEq : quadraticL2Energy μ K q ≤ ε) :
      (modifiedA e (fun j => Complex.I • e j) (fun y => u y+q y) x).PosDef :=
    (power_mixed_posDef_iff_modifiedA
      (hu.add (IsQuadraticPolynomial_contDiff hq.1 2).contDiffAt)
      (hneg q hq hEq) e (fun j => Complex.I • e j)).mp (hpsh q hq hEq)
  obtain ⟨q,hq,hEq,hmin⟩ := exists_pluriharmonic_quadratic_minimizer_general μ hK hKi e
    (fun j => Complex.I • e j) hu hε.le hneg hpos
  exact ⟨q,hq,hEq,hmin,
    pluriharmonic_quadratic_minimizer_has_gap μ hK hKi e hu hε hneg hpos hq hEq hmin⟩

end PowerConvexity
