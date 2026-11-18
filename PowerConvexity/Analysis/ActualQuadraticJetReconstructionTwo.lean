import PowerConvexity.Analysis.ActualScalarQuadraticJetLimitsTwo

/-! # Reconstruction of an actual harmonic quadratic from the limiting jets.
Symmetry and zero real trace are passed through the actual operator-norm
limit. The reconstructed function has exactly the limiting classical jets.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualQuadraticJetFunctionTwo (c : ℝ) (l : E →L[ℝ] ℝ)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (x : E) : ℝ :=
  c+l x+((1/2 : ℝ) • H) x x

theorem actual_quadratic_jet_reconstruction_two (c : ℝ) (l : E →L[ℝ] ℝ)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ v w, H v w = H w v) :
    IsQuadraticPolynomial (actualQuadraticJetFunctionTwo c l H) ∧
    actualQuadraticJetFunctionTwo c l H 0 = c ∧
    fderiv ℝ (actualQuadraticJetFunctionTwo c l H) 0 = l ∧
    ∀ x, realHessian (actualQuadraticJetFunctionTwo c l H) x = H := by
  have hs : ∀ v w, ((1/2 : ℝ) • H) v w = ((1/2 : ℝ) • H) w v := by
    intro v w
    simp only [_root_.smul_apply,smul_eq_mul,hsym v w]
  refine ⟨⟨c,l,(1/2 : ℝ) • H,hs,fun _ => rfl⟩,?_,?_,?_⟩
  · simp [actualQuadraticJetFunctionTwo]
  · change fderiv ℝ (fun y => c+l y+((1/2 : ℝ) • H) y y) 0 = l
    rw [(quadratic_coeff_hasFDerivAt c l ((1/2 : ℝ) • H) hs 0).fderiv]
    simp only [map_zero,smul_zero,add_zero]
  · intro x
    change realHessian (fun y => c+l y+((1/2 : ℝ) • H) y y) x = H
    rw [quadratic_coeff_realHessian c l ((1/2 : ℝ) • H) hs x,smul_smul]
    norm_num

theorem actual_realHessian_limit_symmetry_two
    {Q : ℕ → E → ℝ} {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hQ : ∀ n, IsQuadraticPolynomial (Q n))
    (hH : Tendsto (fun n => realHessian (Q n) 0) atTop (𝓝 H)) :
    ∀ v w, H v w = H w v := by
  have heval (v w : E) : Continuous (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v w) :=
    (continuous_eval_const w).comp (continuous_eval_const v)
  intro v w
  have hvw := ((heval v w).tendsto H).comp hH
  have hwv := ((heval w v).tendsto H).comp hH
  have he : (fun n => realHessian (Q n) 0 w v) = fun n => realHessian (Q n) 0 v w := by
    funext n
    exact realHessian_symm (IsQuadraticPolynomial_contDiff (hQ n) 2).contDiffAt w v
  change Tendsto (fun n => realHessian (Q n) 0 w v) atTop (𝓝 (H w v)) at hwv
  rw [he] at hwv
  exact tendsto_nhds_unique hvw hwv

theorem actual_quadratic_limit_trace_zero_two
    {Q : ℕ → E → ℝ} {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hQ : ∀ n, IsQuadraticPolynomial (Q n))
    (hH : Tendsto (fun n => realHessian (Q n) 0) atTop (𝓝 H))
    (ht : ∀ n, (realBlockHessian realDirections imagDirections (Q n) 0).trace = 0)
    (c : ℝ) (l : E →L[ℝ] ℝ) :
    ∀ x, (realBlockHessian realDirections imagDirections
      (actualQuadraticJetFunctionTwo c l H) x).trace = 0 := by
  let e : (Fin 2 ⊕ Fin 2) → E := Sum.elim realDirections imagDirections
  have hc : Continuous (fun B : E →L[ℝ] E →L[ℝ] ℝ => ∑ i, B (e i) (e i)) := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_eval_const (e i)).comp (continuous_eval_const (e i))
  have hlim := (hc.tendsto H).comp hH
  change Tendsto (fun n => (realBlockHessian realDirections imagDirections (Q n) 0).trace)
    atTop (𝓝 (∑ i, H (e i) (e i))) at hlim
  have h0 : Tendsto (fun n => (realBlockHessian realDirections imagDirections (Q n) 0).trace)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [ht] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hz : (∑ i, H (e i) (e i)) = 0 := tendsto_nhds_unique hlim h0
  have hrec := (actual_quadratic_jet_reconstruction_two c l H
    (actual_realHessian_limit_symmetry_two hQ hH)).2.2.2
  intro x
  change (∑ i, realHessian (actualQuadraticJetFunctionTwo c l H) x (e i) (e i)) = 0
  simpa only [hrec x] using hz

end PowerConvexity
