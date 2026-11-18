import PowerConvexity.Analysis.NonpositiveBoundaryMaximum
import PowerConvexity.Calculus.ScalarDirichlet
import PowerConvexity.Calculus.QuadraticBallPotential

/-! # Weak scalar comparison, proved by a strict quadratic perturbation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus

theorem nonpositive_of_nonnegative_scalar_contraction
    {U : Set ℂ} (hU : IsOpen U) (hK : IsCompact (closure U)) {f : ℂ → ℝ}
    (hfc : ContinuousOn f (closure U)) (hf : ContDiffOn ℝ 2 f U)
    (hboundary : ∀ x ∈ frontier U, f x ≤ 0)
    (hL : ∀ x ∈ U, 0 ≤ scalarHessianContraction (realHessian f x)) :
    ∀ x ∈ closure U, f x ≤ 0 := by
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  intro x hx
  by_cases hxU : x ∈ U
  · by_contra hn
    have hfx : 0 < f x := lt_of_not_ge hn
    let ε := f x/(2*(R^2+1))
    have hε : 0 < ε := div_pos hfx (by positivity)
    have he : ε*(2*(R^2+1)) = f x := by dsimp [ε]; field_simp
    let q := quadraticBallPotential (E := ℂ) ε R
    let g : ℂ → ℝ := fun y => f y+q y
    have hq : ContDiff ℝ 2 q := quadraticBallPotential_contDiff ε R 2
    have hgc : ContinuousOn g (closure U) := hfc.add hq.continuous.continuousOn
    have hg : ContDiffOn ℝ 2 g U := hf.add hq.contDiffOn
    have hgb (y : ℂ) (hy : y ∈ frontier U) : g y ≤ 0 := by
      have hb := hbound y (frontier_subset_closure hy)
      have hs : ‖y‖^2 ≤ R^2 := by nlinarith [norm_nonneg y]
      have hqle : q y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε.le (sub_nonpos.mpr hs)
      exact add_nonpos (hboundary y hy) hqle
    have hgp (y : ℂ) (hy : y ∈ U) : 0 < scalarHessianContraction (realHessian g y) := by
      have hQ : realHessian q y = (2*ε) • (realInnerForm (E := ℂ)) := by
        ext v w
        change realHessian (quadraticBallPotential ε R) y v w = 2*ε*inner ℝ v w
        exact quadraticBallPotential_realHessian ε R y v w
      change 0 < scalarHessianContraction (realHessian (fun y => f y+q y) y)
      rw [realHessian_add (hf.contDiffAt (hU.mem_nhds hy)) hq.contDiffAt,
        scalarHessianContraction.map_add,hQ,scalarHessianContraction.map_smul,smul_eq_mul,scalarHessianContraction_trace]
      have hh := hL y hy
      nlinarith
    have hgneg := negative_of_positive_contraction_nonpositive_boundary hU hK hgc hg hgb
      (fun _ => scalarHessianContraction) (fun _ _ => scalarHessianContraction_positive) hgp x hxU
    have hge : 0 < g x := by
      dsimp [g,q,quadraticBallPotential]
      have hh : 0 ≤ ε*‖x‖^2 := mul_nonneg hε.le (sq_nonneg _)
      nlinarith
    exact (not_lt_of_ge hge.le) hgneg
  · exact hboundary x (by rw [hU.frontier_eq]; exact ⟨hx,hxU⟩)

theorem scalar_comparison_on_closure
    {U : Set ℂ} (hU : IsOpen U) (hK : IsCompact (closure U)) {u v : ℂ → ℝ}
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hboundary : ∀ x ∈ frontier U, u x ≤ v x)
    (hL : ∀ x ∈ U, scalarHessianContraction (realHessian v x) ≤
      scalarHessianContraction (realHessian u x)) :
    ∀ x ∈ closure U, u x ≤ v x := by
  have hh := nonpositive_of_nonnegative_scalar_contraction hU hK (huc.sub hvc) (hu.sub hv)
    (fun x hx => sub_nonpos.mpr (hboundary x hx)) (fun x hx => by
      change 0 ≤ scalarHessianContraction (realHessian (fun y => u y-v y) x)
      rw [realHessian_sub_at (hu.contDiffAt (hU.mem_nhds hx)) (hv.contDiffAt (hU.mem_nhds hx)),map_sub scalarHessianContraction (realHessian u x) (realHessian v x)]
      exact sub_nonneg.mpr (hL x hx))
  exact fun x hx => sub_nonpos.mp (hh x hx)

theorem scalarDirichlet_nonpos_closure {U : Set ℂ} {u : ℂ → ℝ} {ρ : ℝ}
    (hU : IsOpen U) (hK : IsCompact (closure U))
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0) (hρpos : 0 < ρ)
    (hρ : ∀ x ∈ U, complexHessian (fun _ : Fin 1 => (1:ℂ))
      (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ:ℂ)) :
    ∀ x ∈ closure U, u x ≤ 0 := by
  intro x hx
  by_cases hi : x ∈ U
  · exact (scalarDirichlet_negative hU hK huc hu hboundary hρpos hρ x hi).le
  · rw [hboundary x (by rw [hU.frontier_eq]; exact ⟨hx,hi⟩)]

end PowerConvexity
