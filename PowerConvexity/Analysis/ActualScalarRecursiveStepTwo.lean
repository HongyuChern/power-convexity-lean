import PowerConvexity.Analysis.ActualScalarQuadraticUpdateTwo
import PowerConvexity.Analysis.ActualRescaledScalarSourceTwo
import PowerConvexity.Analysis.ActualConcentricWeakScalingTwo

/-! # A closed actual recursive step for a fixed scalar weak equation.
The coefficient, source and weak solution are fixed once. All normalizing
constants are chosen before them, and the same polynomial update supplies
the next residual, trace, Hessian bound and complete jet increments.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_scalar_recursive_step_two {L : ℝ} (hL : 0 ≤ L) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/32 : ℝ) ∧ ∃ epsilon > 0, epsilon ≤ 1 ∧
      ∀ A : EllipticCoeff (2+2) (ball (0 : E) 1),
      (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      ∀ V : Set E, IsOpen V → closedBall (0 : E) 1 ⊆ V →
      (∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) V) →
      (∀ x ∈ ball (0 : E) 1, ∀ j,
        (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0) →
      (∀ x ∈ ball (0 : E) 1, ∀ v : E,
        ‖v-matMulE (A.a x) v‖ ≤ (epsilon*‖x‖)*‖v‖) →
      ∀ f u : E → ℝ, MemLp f 2 (volume.restrict (ball (0 : E) 1)) →
      (∀ x ∈ ball (0 : E) 1, |f x| ≤ epsilon*‖x‖) →
      ActualScalarWeakEquationTwo A f u →
      ∀ R a : ℝ, 0 < R → 0 < a → R ≤ a → a ≤ 1 →
      ∀ q : E → ℝ, IsQuadraticPolynomial q →
      (∀ x, (realBlockHessian realDirections imagDirections q x).trace = 0) →
      (∀ x, ‖realHessian q x‖ ≤ 2*M*(1-a)) →
      ∀ ww : MemW1pWitness 2 (normalizedScalarResidualTwo u q R a) (ball (0 : E) 1),
      ‖ww.memLp.toLp (normalizedScalarResidualTwo u q R a)‖ ≤ 1 →
      ∃ q' : E → ℝ, IsQuadraticPolynomial q' ∧
        (∀ x, (realBlockHessian realDirections imagDirections q' x).trace = 0) ∧
        (∀ x, ‖realHessian q' x‖ ≤ 2*M*(1-a/2)) ∧
        |q' 0-q 0| ≤ a*R^2*M ∧
        ‖fderiv ℝ q' 0-fderiv ℝ q 0‖ ≤ a*R*M ∧
        (∀ x, ‖realHessian q' x-realHessian q x‖ ≤ a*M) ∧
        ∃ ww' : MemW1pWitness 2 (normalizedScalarResidualTwo u q' (R*r) (a/2))
          (ball (0 : E) 1),
          ‖ww'.memLp.toLp (normalizedScalarResidualTwo u q' (R*r) (a/2))‖ ≤ 1 := by
  obtain ⟨M,hM,r,hr,hrb,delta,hd,hd1,hstep⟩ := actual_scalar_normalized_fullJet_step_two hL
  let C : ℝ := (1+32*M)*Real.sqrt (volume (ball (0 : E) 1)).toReal
  have hC : 0 ≤ C := by dsimp [C];positivity
  let epsilon : ℝ := delta/(1+C)
  have heps : 0 < epsilon := div_pos hd (by linarith)
  have heq : epsilon*(1+C) = delta := div_mul_cancel₀ delta (by linarith)
  have hepdelta : epsilon ≤ delta := by nlinarith
  have hsource : epsilon*(1+16*(2*M))*Real.sqrt (volume (ball (0 : E) 1)).toReal ≤ delta := by
    have hh : epsilon*C ≤ delta := by nlinarith
    convert hh using 1 <;> dsimp [C] <;> ring
  refine ⟨M,hM,r,hr,hrb,epsilon,heps,hepdelta.trans hd1,?_⟩
  intro A hlam hAL V hV hclosed hA hdiv hdev f u hf hfn hu R a hR ha hRa ha1 q hq hqt hqH ww hwn
  have hR1 : R ≤ 1 := hRa.trans ha1
  have hsub : ball (0 : E) R ⊆ ball (0 : E) 1 := ball_subset_ball hR1
  have hclosedR : closedBall (0 : E) R ⊆ V := (closedBall_subset_closedBall hR1).trans hclosed
  let AR := A.restrict hsub
  let B := rescaleCoeffToUnitBall hR AR
  have hur : ActualScalarWeakEquationTwo AR f u := actual_scalar_weak_restrict_concentric_two A hR hR1 hu
  have hfr : MemLp f 2 (volume.restrict (ball (0 : E) R)) :=
    hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hqfr := actual_quadratic_source_memLp_two
    (fun i j => (hA i j).continuousOn.mono hclosedR) hq
  obtain ⟨hg,hgn⟩ := actual_rescaled_harmonic_quadratic_source_smallness_two hR ha hRa
    heps.le (by positivity : 0 ≤ 2*M) hfr hqfr
    (fun x hx => hdev x (hsub hx)) (fun x hx => hfn x (hsub hx))
    (fun x _ => (hqH x).trans (by nlinarith)) (fun x _ => hqt x)
  let g : E → ℝ := fun z => a⁻¹*(f (R • z)-quadraticScalarSourceTwo A.a q (R • z))
  have hw : ActualScalarWeakEquationTwo B g (normalizedScalarResidualTwo u q R a) := by
    have hh := actual_normalized_quadratic_residual_equation_two hR ha hV hclosedR AR
      hA (fun x hx => hdiv x (hsub hx)) hfr hur hq
    change ActualScalarWeakEquationTwo B g (fun z => a⁻¹*(R^2)⁻¹*(u (R • z)-q (R • z)))
    simpa only [B,g,quadraticScalarSourceTwo,zero_add,sub_neg_eq_add,AR,EllipticCoeff.restrict] using hh
  have hBdev : ∀ᵐ z ∂volume.restrict (ball (0 : E) 1), ∀ v : E,
      ‖v-matMulE (B.a z) v‖ ≤ delta*‖v‖ := by
    filter_upwards [actual_rescaled_coefficient_deviation_ae_two A hR hR1 heps.le hdev] with z hz
    intro v
    exact (hz v).trans (mul_le_mul_of_nonneg_right hepdelta (norm_nonneg v))
  obtain ⟨p,hp,hpt,hp0,hp1,hp2,herr,ww',hwn'⟩ :=
    hstep B hlam hAL hBdev g (normalizedScalarResidualTwo u q R a) hg
      (hgn.trans hsource) hw ww hwn
  let q' := scalarQuadraticUpdateTwo q p R a
  obtain ⟨hb0,hb1,hb2⟩ := scalarQuadraticUpdateTwo_jet_increment_bounds hq hp hR ha.le hp0 hp1 (hp2 0)
  refine ⟨q',scalarQuadraticUpdateTwo_isQuadratic hq hp R a,
    scalarQuadraticUpdateTwo_trace_zero hq hp hR hqt hpt,?_,hb0,hb1,hb2,?_⟩
  · intro x
    have hh : ‖realHessian q' x‖ ≤ ‖realHessian q x‖+‖realHessian q' x-realHessian q x‖ := by
      have he : realHessian q' x = realHessian q x+(realHessian q' x-realHessian q x) := by
        ext v z
        simp only [_root_.add_apply,_root_.sub_apply]
        ring
      exact (congrArg norm he).trans_le
        (norm_add_le (realHessian q x) (realHessian q' x-realHessian q x))
    have hh2 := add_le_add (hqH x) (hb2 x)
    have ht : 2*M*(1-a)+a*M = 2*M*(1-a/2) := by ring
    exact hh.trans (hh2.trans_eq ht)
  · have he := normalizedScalarResidualTwo_update (u := u) (q := q) (p := p) hR ha hr
    change ∃ ww' : MemW1pWitness 2 (normalizedScalarResidualTwo u (scalarQuadraticUpdateTwo q p R a) (R*r) (a/2)) _, _
    rw [he]
    exact ⟨ww',hwn'⟩

end PowerConvexity
