import PowerConvexity.Calculus.QuadraticMinimumAttained
import PowerConvexity.Calculus.SeparationTestQuadratics
import PowerConvexity.Calculus.QuadraticRayleighContact
import PowerConvexity.Algebra.EigenvalueCovarianceTwo
import PowerConvexity.Algebra.SchurUpperOneTwo
import PowerConvexity.Calculus.PowerMixedPositive

/-! # Appendix A spectral separation for the actual minimizing perturbation

The theorem below uses exactly the sign and modified-mixed-Hessian positivity
needed by the argument. It does not infer them from strict set convexity or
from positivity of the Monge--Ampere determinant.
-/
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

theorem pluriharmonic_quadratic_minimizer_has_gap_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
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
      modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q y) x ≤
        modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+r y) x) :
    0 < eigenDiscriminantTwo
      (modifiedK e (fun j => Complex.I • e j) (fun y => u y+q y) x) := by
  let a0 : Fin 2 → E := e
  let b0 : Fin 2 → E := fun j => Complex.I • e j
  have hjet (r : E → ℝ) (hr : IsPluriharmonicQuadratic a0 b0 r) :
      ContDiffAt ℝ 2 (fun y => u y+r y) x :=
    hu.add (IsQuadraticPolynomial_contDiff hr.1 2).contDiffAt
  obtain ⟨Q,d,hQ,hQA,hd1,hd,hQB⟩ := exists_simultaneous_takagi_two
    (hpos q hq hE) (modifiedB_transpose (hjet q hq) a0 b0)
  have hgap := schur_quotient_gap_iff_takagi _ _ Q d hQ hQA hQB hd1 hd
  by_contra hnot
  have hdeq : d 1 = d 0 := by
    apply le_antisymm hd
    apply le_of_not_gt
    intro hh
    exact hnot ((eigenvalueTwo_strict_gap_iff _).mp (hgap.mpr hh))
  let a := complexFrameReal Q a0 b0
  let b := complexFrameImag Q a0 b0
  have hAc : modifiedA a b (fun y => u y+q y) x = 1 := by
    rw [modifiedA_complexFrame (hjet q hq) (hneg q hq hE)]
    exact hQA
  have hBc : modifiedB a b (fun y => u y+q y) x = Matrix.diagonal (fun _ => (d 0:ℂ)) := by
    rw [modifiedB_complexFrame (hjet q hq) (hneg q hq hE),hQB]
    congr 1
    funext i
    fin_cases i <;> simp [hdeq]
  have hposc (r : E → ℝ) (hr : IsPluriharmonicQuadratic a0 b0 r)
      (hEr : quadraticL2Energy μ K r ≤ ε) : (modifiedA a b (fun y => u y+r y) x).PosDef := by
    rw [modifiedA_complexFrame (hjet r hr) (hneg r hr hEr)]
    exact (posDef_complex_congruence_iff Q _ hQ).mpr (hpos r hr hEr)
  have hsigc (r : E → ℝ) (hr : IsPluriharmonicQuadratic a0 b0 r)
      (hEr : quadraticL2Energy μ K r ≤ ε) :
      modifiedSigmaTwo a b (fun y => u y+r y) x = modifiedSigmaTwo a0 b0 (fun y => u y+r y) x :=
    modifiedSigmaTwo_complexFrame (hjet r hr) (hneg r hr hEr) Q hQ a0 b0
  obtain ⟨h,g,hh,hg,hh0,hg0,hh1,hg1,hh2,hg2,hhH,hgH⟩ :=
    exists_separation_test_quadratics_two e Q hQ x
  have hd0 : 0 ≤ d 0 := hd1.trans hd
  rcases eq_or_lt_of_le hd0 with hz | hdpos
  · have hroot : modifiedSigmaTwo a0 b0 (fun y => u y+q y) x = 1 := by
      have hr := (schur_quotient_takagi_ordered_roots _ _ Q d hQ hQA hQB hd1 hd).1
      simpa only [← hz,zero_pow (by decide : 2 ≠ 0),sub_zero,
        modifiedSigmaTwo,modifiedK,modifiedSchur,a0,b0] using hr
    have hzero : IsPluriharmonicQuadratic a0 b0 (fun _ : E => 0) := by
      exact ⟨(quadraticSubmodule E).zero_mem,(pluriharmonicQuadraticSubmodule a0 b0).zero_mem⟩
    have hEzero : quadraticL2Energy μ K (fun _ : E => 0) ≤ ε := by
      simpa [quadraticL2Energy] using hε.le
    have hAu : (modifiedA a b u x).PosDef := by simpa using hposc _ hzero hEzero
    have hsig0 : modifiedSigmaTwo a b u x = 1 := by
      have hlow := hmin _ hzero hEzero
      rw [hroot] at hlow
      have hc := hsigc _ hzero hEzero
      simp only [add_zero] at hlow hc
      rw [← hc] at hlow
      exact le_antisymm (schur_lower_le_one_two hAu (modifiedB_transpose hu a b)) hlow
    have hBu : modifiedB a b u x = 0 :=
      (schur_lower_eq_one_iff_two hAu (modifiedB_transpose hu a b)).mp hsig0
    obtain ⟨δ,hδ,hsmall⟩ := exists_positive_scaled_energy_radius μ K g hε
    let t := δ/2
    have ht : 0 < t := by dsimp [t]; linarith
    have htδ : |t| ≤ δ := by rw [abs_of_pos ht]; dsimp [t]; linarith
    let r : E → ℝ := fun y => t*g y
    have hr := IsPluriharmonicQuadratic_const_mul hg t
    have hEr : quadraticL2Energy μ K r ≤ ε := hsmall t htδ
    have hBr : modifiedB a b (fun y => u y+r y) x ≠ 0 := by
      rw [modifiedB_centered_scaled_perturbation hu
        (IsQuadraticPolynomial_contDiff hg.1 2).contDiffAt a b hg0 hg1,hBu,zero_add,hgH]
      intro he
      have he0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) he
      have : t = 0 := by simpa using he0
      exact ht.ne' this
    have hsr : modifiedSigmaTwo a b (fun y => u y+r y) x < 1 := by
      have ha := hposc r hr hEr
      have hb := modifiedB_transpose (hjet r hr) a b
      exact lt_of_le_of_ne (schur_lower_le_one_two ha hb)
        (fun he => hBr ((schur_lower_eq_one_iff_two ha hb).mp he))
    have hlow := hmin r hr hEr
    rw [hroot,← hsigc r hr hEr] at hlow
    exact (not_lt_of_ge hlow) hsr
  · letI := quadraticL2NormedAddCommGroup μ hK hKi
    letI : TopologicalSpace (quadraticSubmodule E) :=
      (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
    letI := quadraticL2InnerProductSpace μ hK hKi
    letI := quadraticSubmodule_finiteDimensional (E := E)
    let P := pluriharmonicQuadraticSubmodule a0 b0
    let F : P →ₗ[ℝ] quadraticSubmodule E := P.subtype
    let pq : P := ⟨⟨q,hq.1⟩,hq.2⟩
    let ph : P := ⟨⟨h,hh.1⟩,hh.2⟩
    have hn (p : P) : ‖p‖^2 = quadraticL2Energy μ K p.val.val := quadraticL2_norm_sq μ hK hKi p.val
    apply quadraticFamily_repeated_positive_not_minimum F a b hu hε hdpos pq ph
      (by rw [hn]; exact hE)
      (fun p hp => hneg p.val.val ⟨p.val.property,p.property⟩ (by rwa [← hn]))
      (fun p hp => hposc p.val.val ⟨p.val.property,p.property⟩ (by rwa [← hn]))
      hh0 hh1 hh2 hAc hBc hhH
    intro p hp
    have hEp : quadraticL2Energy μ K p.val.val ≤ ε := by rwa [← hn]
    have hpclass : IsPluriharmonicQuadratic a0 b0 p.val.val := ⟨p.val.property,p.property⟩
    change modifiedSigmaTwo a b (fun y => u y+q y) x ≤
      modifiedSigmaTwo a b (fun y => u y+p.val.val y) x
    rw [hsigc q hq hE,hsigc p.val.val hpclass hEp]
    exact hmin p.val.val hpclass hEp

/-- Attainment and separation, with the strict-psh assumption stated for
exactly the power-transformed perturbed potential as in the frozen lemma. -/
theorem exists_pluriharmonic_quadratic_minimizer_with_gap_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
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
        modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q y) x ≤
          modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+r y) x) ∧
      0 < eigenDiscriminantTwo (modifiedK e (fun j => Complex.I • e j) (fun y => u y+q y) x) := by
  have hpos (q : E → ℝ) (hq : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q)
      (hEq : quadraticL2Energy μ K q ≤ ε) :
      (modifiedA e (fun j => Complex.I • e j) (fun y => u y+q y) x).PosDef :=
    (power_mixed_posDef_iff_modifiedA
      (hu.add (IsQuadraticPolynomial_contDiff hq.1 2).contDiffAt)
      (hneg q hq hEq) e (fun j => Complex.I • e j)).mp (hpsh q hq hEq)
  obtain ⟨q,hq,hEq,hmin⟩ := exists_pluriharmonic_quadratic_minimizer μ hK hKi e
    (fun j => Complex.I • e j) hu hε.le hneg hpos
  exact ⟨q,hq,hEq,hmin,
    pluriharmonic_quadratic_minimizer_has_gap_two μ hK hKi e hu hε hneg hpos hq hEq hmin⟩

end PowerConvexity
