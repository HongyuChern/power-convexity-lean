import PowerConvexity.Calculus.StrongDefiningMinkowskiCurvature
import PowerConvexity.Calculus.StrongDefiningDirichletTangentTwo
import PowerConvexity.Calculus.MinkowskiClosureJetsFromBoundaryModulusTwo
import PowerConvexity.Calculus.ActualFamilyBoundaryPowerCollar
import PowerConvexity.Calculus.MinkowskiSmoothBoundary
import PowerConvexity.Calculus.MinkowskiActualCollarExhaustionTwo

/-! # The actual strong-curvature route to a common truncation collar

The geometry is a supplied genuine smooth defining function with a positive
real Hessian bound, as constructed by the finite-support outer approximation.
Classical-family existence and one common boundary Hessian Holder estimate
remain explicit.  Every other collar input is derived for the same actual
family: true boundary tangent positivity, joint closure jets, and compact
moving geometry.  The ball endpoint is identified by the existing actual
Dirichlet comparison theorem.  The original fixed-truncation P119 and its
exhaustion then return positivity throughout each original Minkowski domain.

This conditional theorem is not a proof that the two remaining analytic
inputs hold on the constructed approximants.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E] [Nontrivial E]
attribute [local instance] zphRealSpace zphRealModule zphDualSpace zphDualModule
  zphDualTopology zphHessSpace zphHessModule zphHessTopology
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_actual_ball_endpoint_closure_hessian_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A : Set E} (hAn : A.Nonempty) {R : ℝ} (hR : 0 < R)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R))) :
    ∀ x ∈ closure (ball (0 : E) R), ∀ v w : E,
      (J ⟨0,by norm_num⟩).hessian x v w = 2*inner ℝ v w := by
  let t0 : I := ⟨0,by norm_num⟩
  have hV0 : minkowskiDomain t0 A (ball (0 : E) R) = ball 0 R :=
    minkowskiDomain_zero hAn
  have heq := hu.endpoint_zero hab hAn hR
  have hHcont : ContinuousOn (J t0).hessian (closure (ball (0 : E) R)) := by
    simpa only [hV0] using (J t0).continuous_hessian
  intro x hx v w
  apply ContinuousWithinAt.eq_const_of_mem_closure
    (((hHcont x hx).mono subset_closure).clm_apply continuousWithinAt_const |>.clm_apply continuousWithinAt_const) hx
  intro y hy
  have hyV : y ∈ minkowskiDomain t0 A (ball (0 : E) R) := by rwa [hV0]
  have he : u t0 =ᶠ[𝓝 y] quadraticBallPotential 1 R := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    exact heq (subset_closure hz)
  have hH : realHessian (u t0) y = realHessian (quadraticBallPotential 1 R) y :=
    (he.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  rw [(J t0).hessian_eq hyV]
  change realHessian (u t0) y v w = _
  rw [hH,quadraticBallPotential_realHessian]
  ring

theorem minkowski_strong_defining_actual_boundary_tangent_positive_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    {F : E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFb : ∀ x ∈ frontier A, F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
      ∀ᶠ z in 𝓝 x, z ∈ A ↔ F z < 0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hFH : ∀ x ∈ frontier A, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian F x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho L : ℝ} (hR : 0 < R) (hrho : 0 < rho)
    (hballA : closedBall (0 : E) rho ⊆ A)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R))) :
    ∀ t : I, ∀ x ∈ frontier (minkowskiDomain t A (ball 0 R)),
      ∀ v : E, v ≠ 0 → (J t).derivative x v = 0 → 0 < (J t).hessian x v v := by
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hrho.le)⟩
  have hSmooth : HasSmoothLocalDefiningFunction A :=
    fun x hx => ⟨F,hF.contDiffAt,(hFb x hx).1,(hFb x hx).2.1,(hFb x hx).2.2⟩
  obtain ⟨kappa,hkappa,hcurv⟩ := strong_defining_minkowski_actual_tangent_curvature_uniform_lower
    hA hconv hK ((contDiff_infty.mp hF) 3) hFb hdelta hFH hR
  intro t x hx
  by_cases ht0 : (t : ℝ) = 0
  · have htEq : t = (⟨0,by norm_num⟩ : I) := Subtype.ext ht0
    subst t
    have hxB : x ∈ closure (ball (0 : E) R) := by
      simpa only [minkowskiDomain_zero hAn] using frontier_subset_closure hx
    intro v hv _
    rw [minkowski_actual_ball_endpoint_closure_hessian_two e hab hAn hR hu J x hxB,
      real_inner_self_eq_norm_sq]
    exact mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hv))
  · have ht : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
    have hV : IsOpen (minkowskiDomain t A (ball (0 : E) R)) :=
      minkowskiDomain_isOpen hA isOpen_ball hAn t
    have hVc := minkowskiDomain_convex hconv (convex_ball (0 : E) R) (t : ℝ)
    have hVK := minkowskiDomain_isCompact_closure hAb hBb t.2.1 t.2.2
    have hVreg : HasSmoothLocalDefiningFunction (minkowskiDomain t A (ball (0 : E) R)) := by
      by_cases htlt : (t : ℝ) < 1
      · exact minkowskiDomain_hasSmoothLocalDefiningFunction hA hconv hK hSmooth ht htlt hR
      · have ht1 : (t : ℝ) = 1 := le_antisymm t.2.2 (not_lt.mp htlt)
        simpa only [ht1,minkowskiDomain_one (show (ball (0 : E) R).Nonempty from ⟨0,mem_ball_self hR⟩)]
          using hSmooth
    obtain ⟨g,hg,hgx,hDg,hgdef⟩ := hVreg x hx
    apply actualDirichlet_closure_tangent_positive_of_positive_defining_two hV hVc hVK
      e (fun j => Complex.I • e j) hab (hu t) (J t) hx ((contDiffAt_infty.mp hg) 2) hgx hDg hgdef
    intro v hv hvg
    have hh := hcurv t ht t.2.2 x hx g ((contDiffAt_infty.mp hg) 2) hgx hDg hgdef v hvg
    have hp : 0 < kappa*‖v‖^2 := mul_pos hkappa (sq_pos_of_pos (norm_pos_iff.mpr hv))
    have hgp : 0 < ‖gradient g x‖ := norm_pos_iff.mpr (definingGradient_ne_zero hDg)
    have hmul := (lt_div_iff₀ hgp).mp (hp.trans_le hh)
    simpa only [zero_mul] using hmul

theorem minkowski_strong_defining_actual_common_collar_from_boundary_holder_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    {F : E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFb : ∀ x ∈ frontier A, F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
      ∀ᶠ z in 𝓝 x, z ∈ A ↔ F z < 0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hFH : ∀ x ∈ frontier A, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian F x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho L : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    {C gamma radius : ℝ} (hgamma : 0 < gamma) (hradius : 0 < radius)
    (hholder : ∀ t : I, ∀ c ∈ frontier (minkowskiDomain t A (ball 0 R)),
      ∀ z ∈ closure (minkowskiDomain t A (ball 0 R)), ‖z-c‖ < radius →
        ‖(J t).hessian z-(J t).hessian c‖ ≤ C*‖z-c‖^gamma) :
    ∃ thickness > 0, ∀ eps : ℝ, 0 < eps → eps < thickness →
      ∀ t : I, ∀ x ∈ frontier (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x := by
  let V : I → Set E := fun t => minkowskiDomain t A (ball (0 : E) R)
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hrho.le)⟩
  have hSmooth : HasSmoothLocalDefiningFunction A :=
    fun x hx => ⟨F,hF.contDiffAt,(hFb x hx).1,(hFb x hx).2.1,(hFb x hx).2.2⟩
  have hV (t : I) : IsOpen (V t) := minkowskiDomain_isOpen hA isOpen_ball hAn t
  have hVK (t : I) : IsCompact (closure (V t)) :=
    minkowskiDomain_isCompact_closure hAb hBb t.2.1 t.2.2
  have hgraph : IsOpen {p : I × E | p.2 ∈ V p.1} :=
    minkowskiDomain_parameterGraph_isOpen hA isOpen_ball hconv (convex_ball 0 R)
      hrho hL hballA hballB hAb hBb
  have hKB : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hKG : IsCompact {p : I × E | p.2 ∈ closure (V p.1)} :=
    minkowskiDomain_closure_parameterGraph_isCompact hK hKB
  have hfront (t : I) : (frontier (V t)).Nonempty := by
    apply nonempty_frontier_iff.mpr
    refine ⟨?_,?_⟩
    · exact ⟨0,minkowskiDomain_contains_inter t A (ball 0 R)
        ⟨hballA (mem_closedBall_self hrho.le),mem_ball_self hR⟩⟩
    · intro he
      apply (hVK t).ne_univ
      simp only [he,closure_univ]
  obtain ⟨hvalue,hder,hhess⟩ := minkowski_actual_joint_closure_jets_from_boundary_hessian_holder_two
    hA hconv hK hSmooth e hab hR hrho hL hballA hballB hAb hBb hu J hgamma hradius hholder
  apply actual_family_common_truncation_sigma_two_of_joint_closure_jets e hV hgraph hKG hfront
    (fun t => (hu t).1.of_le (by norm_num)) J hvalue hder hhess
    (fun t => strictPshDirichlet_negative (hV t) (hVK t) (hu t).continuous_closure
      ((hu t).1.of_le (by norm_num)) (hu t).2.2.2.2 e (fun j => Complex.I • e j) (hu t).2.2.1)
    (fun t => (hu t).2.2.2.2) (fun t => (hu t).2.2.1)
  exact minkowski_strong_defining_actual_boundary_tangent_positive_two hA hconv hK
    hF hFb hdelta hFH e hab hR hrho hballA hAb hBb hu J

theorem minkowski_strong_defining_actual_exhaustion_from_boundary_holder_two
    [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [IsFiniteMeasureOnCompacts mu] [Measure.IsOpenPosMeasure mu]
    {Q : Set E} (hQK : IsCompact Q) (hQi : (interior Q).Nonempty)
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    {F : E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFb : ∀ x ∈ frontier A, F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
      ∀ᶠ z in 𝓝 x, z ∈ A ↔ F z < 0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hFH : ∀ x ∈ frontier A, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian F x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho L : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    {C gamma radius : ℝ} (hgamma : 0 < gamma) (hradius : 0 < radius)
    (hholder : ∀ t : I, ∀ c ∈ frontier (minkowskiDomain t A (ball 0 R)),
      ∀ z ∈ closure (minkowskiDomain t A (ball 0 R)), ‖z-c‖ < radius →
        ‖(J t).hessian z-(J t).hessian c‖ ≤ C*‖z-c‖^gamma) :
    ∀ t : I,
      (∀ x ∈ minkowskiDomain t A (ball 0 R),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) ∧
      StrictConvexOn ℝ (minkowskiDomain t A (ball 0 R)) (powerTransform (u t)) := by
  have hSmooth : HasSmoothLocalDefiningFunction A :=
    fun x hx => ⟨F,hF.contDiffAt,(hFb x hx).1,(hFb x hx).2.1,(hFb x hx).2.2⟩
  obtain ⟨thickness,hthickness,hcollar⟩ :=
    minkowski_strong_defining_actual_common_collar_from_boundary_holder_two
      hA hconv hK hF hFb hdelta hFH e hab hR hrho hL hballA hballB hAb hBb hu J
      hgamma hradius hholder
  exact minkowski_actual_exhaustion_from_small_truncation_boundary_two mu hQK hQi e hab
    hA hconv hK hSmooth hR hrho hL hthickness hballA hballB hAb hBb hu J hcollar

end PowerConvexity
