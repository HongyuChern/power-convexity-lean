import PowerConvexity.Calculus.EuclideanBilinearEntryBound
import PowerConvexity.Calculus.RealHessianEntryFromUpper
import PowerConvexity.Calculus.SecondJetContinuityCriterion
import CHS.Analysis.HessianHolderScaled

/-! # Actual second jets from the scaled CHS estimate

The same potentials occur in the PDE, boundary estimate, and continuity
conclusions. A uniform boundary quadratic upper bound remains an explicit
input to the last theorem; it is not manufactured from separate C2 jets.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Metric Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
variable {n : ℕ}
local notation "E" => DeGiorgi.AmbientSpace (n + n)

theorem euclideanHessian_abs_le_of_boundary_quadratic_upper
    [NeZero n] {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hboundary : ∀ x ∈ frontier U, ∀ v : E, J.hessian x v v ≤ M * ‖v‖^2) :
    ∀ x ∈ U, ∀ i j, |euclideanHessian u x i j| ≤ 3*M := by
  have hnorm (i : Fin n ⊕ Fin n) :
      ‖Sum.elim (realDirections (n := n)) imagDirections i‖ ≤ 1 := by
    rw [blockDirection_eq_single]
    simp
  have hh := realBlockHessian_abs_le_of_boundary_quadratic_upper
    hU hK hu J hb realDirections imagDirections hnorm hpos hdet hM hboundary
  intro x hx i j
  have h := hh x hx (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  simpa only [realBlockHessian, blockDirection_eq_single,
    Equiv.apply_symm_apply, euclideanHessian] using h

theorem exists_scaled_complexMongeAmpere_realHessian_holder
    (hn : 2 ≤ n) {M : ℝ} (hM : 0 ≤ M) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ (x0 : E) (R : ℝ), 0 < R → ∀ u : E → ℝ,
      ContDiffOn ℝ 4 u (ball x0 (2*R)) →
      (∀ x ∈ ball x0 (2*R), (complexHessian realDirections imagDirections u x).det = 1) →
      (∀ x ∈ ball x0 (2*R), (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ ball x0 (2*R), ∀ i j, |euclideanHessian u x i j| ≤ M) →
      ∀ x ∈ ball x0 R, ∀ y ∈ ball x0 R,
        ‖realHessian u x - realHessian u y‖ ≤ C * (‖x-y‖/R)^α := by
  obtain ⟨α,C,hα,hα1,hC,hh⟩ :=
    exists_scaled_complexMongeAmpere_hessian_holder_entry hn hM
  have hnpos : (0 : ℝ) < (n+n : ℕ) := by exact_mod_cast (show 0 < n+n by omega)
  refine ⟨α,((n+n : ℕ) : ℝ)^2*C,hα,hα1,by positivity,?_⟩
  intro x0 R hR u hu hdet hpos hentry x hx y hy
  have hxy := hh x0 R hR u hu hdet hpos hentry x hx y hy
  have hnonneg : 0 ≤ C*(‖x-y‖/R)^α :=
    mul_nonneg hC.le (Real.rpow_nonneg (div_nonneg (norm_nonneg _) hR.le) _)
  have h := euclidean_bilinear_norm_le_of_entry_bound
    (realHessian u x-realHessian u y) hnonneg (fun i j => by
      simpa only [ContinuousLinearMap.sub_apply, euclideanHessian] using hxy i j)
  simpa only [Fintype.card_fin, mul_assoc] using h

variable {T : Type*} [TopologicalSpace T]

theorem realHessian_family_continuousAt_of_CMA_entry_bound
    (hn : 2 ≤ n) {u : T → E → ℝ} {t0 : T} {x0 : E} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hD : ∀ y ∈ closedBall x0 R,
      ContinuousAt (fun p : T × E => fderiv ℝ (u p.1) p.2) (t0,y))
    (hdata : ∀ᶠ t in 𝓝 t0,
      ContDiffOn ℝ 4 (u t) (ball x0 (4*R)) ∧
      (∀ x ∈ ball x0 (4*R), (complexHessian realDirections imagDirections (u t) x).det = 1) ∧
      (∀ x ∈ ball x0 (4*R), (complexHessian realDirections imagDirections (u t) x).PosDef) ∧
      (∀ x ∈ ball x0 (4*R), ∀ i j, |euclideanHessian (u t) x i j| ≤ M)) :
    ContinuousAt (fun p : T × E => realHessian (u p.1) p.2) (t0,x0) := by
  obtain ⟨α,C,hα,_hα1,_hC,hholder⟩ :=
    exists_scaled_complexMongeAmpere_realHessian_holder hn hM
  have h2R : 0 < 2*R := by positivity
  have h4R : 2*(2*R) = 4*R := by ring
  have hsmall : closedBall x0 R ⊆ ball x0 (2*R) :=
    closedBall_subset_ball (by linarith)
  have hlarge : closedBall x0 R ⊆ ball x0 (4*R) :=
    closedBall_subset_ball (by linarith)
  have hcont : Continuous (fun r : ℝ => C*(|r|/(2*R))^α) :=
    continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
      (continuous_abs.div_const (2*R)))
  have homega : Tendsto (fun r : ℝ => C*(|r|/(2*R))^α) (𝓝 0) (𝓝 0) := by
    simpa only [abs_zero,zero_div,Real.zero_rpow hα.ne',mul_zero] using
      (hcont.continuousAt (x := 0)).tendsto
  have hu' : ∀ᶠ t in 𝓝 t0, ∀ y ∈ closedBall x0 R, ContDiffAt ℝ 2 (u t) y := by
    filter_upwards [hdata] with t ht
    intro y hy
    exact (ht.1.contDiffAt (isOpen_ball.mem_nhds (hlarge hy))).of_le (m := 2) (by norm_num)
  apply realHessian_family_continuousAt_of_firstJet_modulus hR hD hu' homega
  filter_upwards [hdata] with t ht
  have hh := hholder x0 (2*R) h2R (u t)
  rw [h4R] at hh
  intro y hy
  have hb := hh ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 y (hsmall hy)
    x0 (mem_ball_self h2R)
  simpa only [abs_of_nonneg (norm_nonneg _)] using hb

theorem realHessian_family_continuousAt_of_CMA_boundary_upper
    (hn : 2 ≤ n) {u : T → E → ℝ} {U : T → Set E}
    (J : ∀ t, ClosureC2Jet (u t) (U t)) {t0 : T} {x0 : E} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hD : ∀ y ∈ closedBall x0 R,
      ContinuousAt (fun p : T × E => fderiv ℝ (u p.1) p.2) (t0,y))
    (hdata : ∀ᶠ t in 𝓝 t0,
      IsOpen (U t) ∧ IsCompact (closure (U t)) ∧
      ContDiffOn ℝ 4 (u t) (U t) ∧
      (∀ x ∈ frontier (U t), u t x = 0) ∧
      (∀ x ∈ U t, (complexHessian realDirections imagDirections (u t) x).PosDef) ∧
      (∀ x ∈ U t, (complexHessian realDirections imagDirections (u t) x).det = 1) ∧
      ball x0 (4*R) ⊆ U t ∧
      (∀ x ∈ frontier (U t), ∀ v : E, (J t).hessian x v v ≤ M*‖v‖^2)) :
    ContinuousAt (fun p : T × E => realHessian (u p.1) p.2) (t0,x0) := by
  have hn0 : n ≠ 0 := by omega
  letI : NeZero n := ⟨hn0⟩
  apply realHessian_family_continuousAt_of_CMA_entry_bound hn hR (by positivity : 0 ≤ 3*M) hD
  filter_upwards [hdata] with t ht
  rcases ht with ⟨hU,hK,hu,hb,hpos,hdet,hball,hboundary⟩
  refine ⟨hu.mono hball,fun x hx => hdet x (hball hx),
    fun x hx => hpos x (hball hx),?_⟩
  intro x hx i j
  exact euclideanHessian_abs_le_of_boundary_quadratic_upper
    hU hK hu (J t) hb hpos hdet hM hboundary x (hball hx) i j

end PowerConvexity
