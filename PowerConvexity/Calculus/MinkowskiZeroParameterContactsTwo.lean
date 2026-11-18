import PowerConvexity.Calculus.SmallValueContactMeasureTwo
import PowerConvexity.Calculus.MinkowskiZeroParameterC0RateTwo
import PowerConvexity.Calculus.CMAJetsIsometricTransport
import PowerConvexity.Analysis.MinkowskiInteriorStability

/-! # Actual near-zero Minkowski solutions have controlled contact sets.
The same fixed isometry pulls back the physical potentials, and the
smallness condition is proved from their quantitative zero-extension
estimate. This is a contact-set bound, not an everywhere Hessian bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "F" => DeGiorgi.AmbientSpace (2+2)
local notation "I" => Icc (0 : ℝ) 1
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

private theorem block_frame_orthonormal_zero_contact_two :
    Orthonormal ℝ (Sum.elim (realDirections (n := 2)) imagDirections) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [blockDirection_eq_single,blockDirection_eq_single,
    orthonormal_iff_ite.mp (EuclideanSpace.orthonormal_single (𝕜 := ℝ))]
  simp only [Equiv.apply_eq_iff_eq]

theorem minkowski_actual_near_zero_contact_volume_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A)
    {R rho L : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) rho ⊆ A)
    (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    (T : F ≃ₗᵢ[ℝ] E)
    (hab : Orthonormal ℝ (Sum.elim (fun i => T (realDirections i))
      (fun i => T (imagDirections i))))
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo (fun i => T (realDirections i))
      (fun i => T (imagDirections i)) A (ball 0 R) u) :
    ∃ K > 0, ∀ x ∈ ball (0 : E) R, ∃ r > 0, ∀ a : ℝ, 0 < a → a ≤ 1 →
      ∀ᶠ t : I in 𝓝 (⟨0,by norm_num⟩ : I),
        closedBall x r ⊆ minkowskiDomain t A (ball 0 R) ∧
        let w := fun z : F => u t (T z)-quadraticBallPotential 1 R z
        let S := lowerParaboloidContactsTwo a w
          (closedBall (T.symm x) r) (closedBall (T.symm x) (r/2))
        IsCompact S ∧ S ⊆ ball (T.symm x) (3*r/4) ∧
          volume (closedBall (T.symm x) (r/2)) ≤ ENNReal.ofReal K*volume S ∧
          ∀ z ∈ S, ‖realHessian w z‖ ≤ 144*a := by
  obtain ⟨K,hK,hmeasure⟩ := exists_universal_small_value_contact_volume_bound_two
  refine ⟨K,hK,?_⟩
  intro x hx
  let t0 : I := ⟨0,by norm_num⟩
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hrho.le)⟩
  have he : minkowskiDomain (t0 : ℝ) A (ball (0 : E) R) = ball 0 R :=
    minkowskiDomain_zero hAn
  obtain ⟨r,hr,hrB,hnear⟩ := minkowskiDomain_eventually_contains_closedBall
    hconv (convex_ball (0 : E) R) hrho hL hballA hballB hAb hBb
    (s := t0) (by simpa only [he] using (isOpen_ball : IsOpen (ball (0 : E) R)))
    (x := x) (by simpa only [he] using hx)
  rw [he] at hrB
  refine ⟨r,hr,?_⟩
  intro a ha ha1
  let k : ℝ := 2*L/rho
  let C : ℝ := (2*k+k^2)*R^2
  have hrate := minkowski_actual_solution_uniform_C0_rate_at_zero_two
    hA hconv hR hrho hL hballA hballB hAb hBb
    (fun i => T (realDirections i)) (fun i => T (imagDirections i)) hab hu
  have hct : Continuous (fun t : I => C*(t : ℝ)) := by fun_prop
  have htzero : Tendsto (fun t : I => C*(t : ℝ)) (𝓝 t0) (𝓝 0) := by
    simpa only [t0,zero_mul,mul_zero] using (hct.continuousAt (x := t0)).tendsto
  have heps : 0 < a*r^2/128 := by positivity
  have hsmallt : ∀ᶠ t : I in 𝓝 t0, C*(t : ℝ) < a*r^2/128 :=
    htzero.eventually (gt_mem_nhds heps)
  filter_upwards [hnear,hsmallt] with t ht hepsilon
  let w : F → ℝ := fun z => u t (T z)-quadraticBallPotential 1 R z
  let D := closedBall (T.symm x) r
  let S := lowerParaboloidContactsTwo a w D (closedBall (T.symm x) (r/2))
  have hball (z : F) (hz : z ∈ D) : T z ∈ closedBall x r := by
    simpa only [D,mem_closedBall,T.dist_map,T.apply_symm_apply] using
      (show dist (T z) (T (T.symm x)) ≤ r by rw [T.dist_map]; exact hz)
  have hU : IsOpen (minkowskiDomain (t : ℝ) A (ball (0 : E) R)) :=
    minkowskiDomain_isOpen hA isOpen_ball hAn (t : ℝ)
  have hux (z : F) (hz : z ∈ D) : ContDiffAt ℝ 2 (u t) (T z) :=
    ((hu t).1.contDiffAt (hU.mem_nhds (ht (hball z hz)))).of_le (by norm_num)
  have hreg (z : F) (hz : z ∈ D) : ContDiffAt ℝ 2 w z :=
    ((hux z hz).comp z T.toContinuousLinearEquiv.contDiff.contDiffAt).sub
      (quadraticBallPotential_contDiff 1 R 2).contDiffAt
  have hd (z : F) (hz : z ∈ D) :
      (1+complexHessian realDirections imagDirections w z).det = 1 := by
    have hcomp : ContDiffAt ℝ 2 (fun y : F => u t (T y)) z := by
      simpa only [Function.comp_def] using
        (hux z hz).comp z T.toContinuousLinearEquiv.contDiff.contDiffAt
    dsimp only [w]
    rw [actual_ball_deviation_complexHessian_two realDirections imagDirections
      block_frame_orthonormal_zero_contact_two hcomp R,
      complexHessian_comp_linearIsometry T (hux z hz)]
    exact (hu t).2.2.2.1 (T z) (ht (hball z hz))
  have hv (z : F) (hz : z ∈ D) : |w z| ≤ a*r^2/128 := by
    have hzB := hrB (hball z hz)
    have h := hrate t (T z)
    rw [show minkowskiDomain (0 : ℝ) A (ball (0 : E) R) = ball 0 R from
      minkowskiDomain_zero hAn,indicator_of_mem (ht (hball z hz)),indicator_of_mem hzB,
      hu.endpoint_zero hab hAn hR (subset_closure hzB)] at h
    have hq : quadraticBallPotential 1 R (T z) = quadraticBallPotential 1 R z := by
      simp only [quadraticBallPotential,T.norm_map]
    rw [hq] at h
    exact h.trans (by exact le_of_lt hepsilon)
  have hout := hmeasure w (T.symm x) a r ha ha1 hr
    (fun z hz => (hreg z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hreg z (ball_subset_closedBall hz)).contDiffWithinAt)
    (fun z hz => hd z (ball_subset_closedBall hz)) hv
  refine ⟨ht,hout.1,hout.2.1,hout.2.2,?_⟩
  intro z hz
  have hSI : S ⊆ interior D :=
    (hout.2.1.trans (ball_subset_ball (by linarith))).trans ball_subset_interior_closedBall
  have hq := lowerParaboloidContactsTwo_actual_quadratic_lower_bound hSI
    (fun z hz => hreg z hz.1) z hz
  exact actual_small_semiconvex_hessian_bound_two (hreg z hz.1) ha.le ha1 (hd z hz.1) hq

end PowerConvexity
