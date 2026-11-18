import PowerConvexity.Calculus.MinkowskiActualDeformationTwo

/-! # Exhausting the actual domains after the common-collar deformation

This discharges the truncation-to-whole-domain step. The classical family,
locally uniform boundary upper estimate and a common positive spectral collar
are explicit unresolved analytic inputs. They are not established here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_actual_deformation_exhaustion_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A : Set E} (hAo : IsOpen A) (hA : Convex ℝ A) {R ρ L δ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    (hbound : ∀ s : I, ∃ M ≥ 0, ∀ᶠ t : I in 𝓝 s,
      ∀ z ∈ frontier (minkowskiDomain t A (ball 0 R)), ∀ v : E,
        (J t).hessian z v v ≤ M*‖v‖^2)
    (hcollar : ∀ t : I, ∀ x ∈ minkowskiDomain t A (ball 0 R),
      infDist x (frontier (minkowskiDomain t A (ball 0 R))) ≤ δ →
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) :
    ∀ t : I,
      (∀ x ∈ minkowskiDomain t A (ball 0 R),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) ∧
      StrictConvexOn ℝ (minkowskiDomain t A (ball 0 R)) (powerTransform (u t)) := by
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hρ.le)⟩
  have hU (t : I) : IsOpen (minkowskiDomain t A (ball 0 R)) :=
    minkowskiDomain_isOpen hAo isOpen_ball hAn t
  have hcompact (t : I) : IsCompact (closure (minkowskiDomain t A (ball 0 R))) :=
    minkowskiDomain_isCompact_closure hAb hBb t.2.1 t.2.2
  have hσ (t : I) (x : E) (hx : x ∈ minkowskiDomain t A (ball 0 R)) :
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x := by
    have hproper : minkowskiDomain t A (ball 0 R) ≠ univ := by
      intro he
      apply (hcompact t).ne_univ
      simp only [he,closure_univ]
    have hfront : (frontier (minkowskiDomain t A (ball 0 R))).Nonempty :=
      nonempty_frontier_iff.mpr ⟨⟨x,hx⟩,hproper⟩
    have hnot : x ∉ frontier (minkowskiDomain t A (ball 0 R)) := by
      rw [(hU t).frontier_eq]
      exact fun hh => hh.2 hx
    have hd : 0 < infDist x (frontier (minkowskiDomain t A (ball 0 R))) :=
      (isClosed_frontier.notMem_iff_infDist_pos hfront).mp hnot
    let ε := min (min ρ δ) (infDist x (frontier (minkowskiDomain t A (ball 0 R)))) / 2
    have hm : 0 < min (min ρ δ) (infDist x (frontier (minkowskiDomain t A (ball 0 R)))) :=
      lt_min (lt_min hρ hδ) hd
    have hε : 0 < ε := half_pos hm
    have hεm : ε < min (min ρ δ) (infDist x (frontier (minkowskiDomain t A (ball 0 R)))) :=
      half_lt_self hm
    have hερ : ε < ρ := hεm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hεδ : ε < δ := hεm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hεd : ε < infDist x (frontier (minkowskiDomain t A (ball 0 R))) :=
      hεm.trans_le (min_le_right _ _)
    have hbε (s : I) (y : E)
        (hy : y ∈ frontier (distanceInteriorDomain (minkowskiDomain s A (ball 0 R)) ε)) :
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u s) y := by
      have hh := distanceInteriorDomain_frontier_value (hU s) hε y hy
      apply hcollar s y hh.1
      rw [hh.2]
      exact hεδ.le
    obtain ⟨η,hη,hresult⟩ := minkowski_actual_deformation_from_boundary_sigma_two
      μ hK hKi e hab hAo hA hR hρ hL hε hερ hballA hballB hAb hBb hu J hbound hbε
    have hzero : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) (0 : E → ℝ) :=
      ⟨(0 : pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j)).val.property,
        (0 : pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j)).property⟩
    have he0 : quadraticL2Energy μ K (0 : E → ℝ) ≤ η := by
      simpa only [quadraticL2Energy,Pi.zero_apply,zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        integral_zero] using hη.le
    have hh := (hresult t 0 hzero he0).1 x (subset_closure ⟨hx,hεd⟩)
    simpa only [Pi.zero_apply,add_zero] using hh
  intro t
  refine ⟨hσ t,?_⟩
  apply strictConvexOn_power_of_modifiedSigmaTwo e (hU t)
    (minkowskiDomain_convex hA (convex_ball 0 R) t) ((hu t).1.of_le (by norm_num))
    (strictPshDirichlet_negative (hU t) (hcompact t) (hu t).continuous_closure
      ((hu t).1.of_le (by norm_num)) (hu t).2.2.2.2 e (fun j => Complex.I • e j)
      (hu t).2.2.1) (hu t).2.2.1 (hσ t)

theorem ClassicalMinkowskiFamilyTwo.strict_endpoint_of_actual_deformation
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A B : Set E} (hAo : IsOpen A) (hAK : IsCompact (closure A)) (hBn : B.Nonempty)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A B u)
    {u₁ : E → ℝ} (hu₁ : ClassicalDirichletDataTwo e (fun j => Complex.I • e j) A u₁)
    (hpath : StrictConvexOn ℝ (minkowskiDomain (1 : ℝ) A B)
      (powerTransform (u ⟨1,by norm_num⟩))) :
    StrictConvexOn ℝ A (powerTransform u₁) := by
  rw [minkowskiDomain_one hBn] at hpath
  apply hpath.congr
  intro x hx
  simp only [powerTransform,hu.endpoint_one hab hAo hAK hBn hu₁ (subset_closure hx)]

/- The three analytic inputs below are intentionally explicit. This theorem
does not claim their derivation from the frozen original hypotheses. -/
theorem classicalDirichlet_strictConvexOn_via_actual_deformation_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A : Set E} (hAo : IsOpen A) (hA : Convex ℝ A) {R ρ L δ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    (hbound : ∀ s : I, ∃ M ≥ 0, ∀ᶠ t : I in 𝓝 s,
      ∀ z ∈ frontier (minkowskiDomain t A (ball 0 R)), ∀ v : E,
        (J t).hessian z v v ≤ M*‖v‖^2)
    (hcollar : ∀ t : I, ∀ x ∈ minkowskiDomain t A (ball 0 R),
      infDist x (frontier (minkowskiDomain t A (ball 0 R))) ≤ δ →
        ∀ v : E, v ≠ 0 → 0 < realHessian (powerTransform (u t)) x v v)
    {u₁ : E → ℝ} (hu₁ : ClassicalDirichletDataTwo e (fun j => Complex.I • e j) A u₁) :
    StrictConvexOn ℝ A (powerTransform u₁) := by
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hρ.le)⟩
  have hBn : (ball (0 : E) R).Nonempty := ⟨0,mem_ball_self hR⟩
  have hU (t : I) : IsOpen (minkowskiDomain t A (ball 0 R)) :=
    minkowskiDomain_isOpen hAo isOpen_ball hAn t
  have hcompact (t : I) : IsCompact (closure (minkowskiDomain t A (ball 0 R))) :=
    minkowskiDomain_isCompact_closure hAb hBb t.2.1 t.2.2
  have hσcollar (t : I) (x : E) (hx : x ∈ minkowskiDomain t A (ball 0 R))
      (hd : infDist x (frontier (minkowskiDomain t A (ball 0 R))) ≤ δ) :
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x := by
    have hneg := strictPshDirichlet_negative (hU t) (hcompact t) (hu t).continuous_closure
      ((hu t).1.of_le (by norm_num)) (hu t).2.2.2.2 e (fun j => Complex.I • e j)
      (hu t).2.2.1 x hx
    exact (modifiedSigmaTwo_pos_iff_powerHessian_pos e
      (((hu t).1.contDiffAt ((hU t).mem_nhds hx)).of_le (by norm_num)) hneg
      ((hu t).2.2.1 x hx)).mpr (hcollar t x hx hd)
  have hpath := minkowski_actual_deformation_exhaustion_two μ hK hKi e hab
    hAo hA hR hρ hL hδ hballA hballB hAb hBb hu J hbound hσcollar
  have hAK : IsCompact (closure A) := by
    simpa only [minkowskiDomain_one hBn] using hcompact ⟨1,by norm_num⟩
  exact hu.strict_endpoint_of_actual_deformation e hab hAo hAK hBn hu₁
    (hpath ⟨1,by norm_num⟩).2

end PowerConvexity
