import PowerConvexity.Calculus.StrongDefiningJointStrictSubsolutionTwo
import PowerConvexity.Calculus.JointGlobalBoundaryLeviTwo

/-! # Genuine joint global defining geometry for strong Minkowski approximants

At every parameter in the entire closed interval, including zero, the same
finite spatial cover is valid for all nearby actual boundaries. Its genuine
local strict subsolutions are glued into one jointly C4 global defining
family. This construction uses the strong approximating domain's real Hessian
and does not assume any nonlinear Dirichlet solution on the new domains.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]

theorem strong_defining_minkowski_exists_joint_regular_ball_subsolution_data_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hUn : U.Nonempty) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hH : ∀ x ∈ frontier U, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian f x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {s R : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hR : 0 < R)
    {x : E} (hx : x ∈ frontier (minkowskiDomain s U (ball (0 : E) R))) :
    ∃ r : ℝ, ∃ w : ℝ × E → ℝ,
      JointRegularBallSubsolutionDataTwo e (fun j => Complex.I • e j)
        (fun t => minkowskiDomain t U (ball (0 : E) R)) (Icc (0 : ℝ) 1) s x r w := by
  obtain ⟨w,hw0,r,hr,hreg,hdata⟩ :=
    strong_defining_minkowski_exists_joint_regular_ball_subsolution_two
      hU hconv hK hUn hf hb hdelta hH e hab hs hs1 hR hx
  exact ⟨r,w,hr,hreg,hdata⟩

theorem strong_defining_minkowski_exists_finite_parameter_subsolution_boundary_cover_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hUn : U.Nonempty) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hH : ∀ x ∈ frontier U, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian f x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {s R : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hR : 0 < R) :
    let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
    ∃ r : frontier (V s) → ℝ, ∃ w : frontier (V s) → ℝ × E → ℝ,
      ∃ T : Finset (frontier (V s)),
        (∀ p : frontier (V s),
          JointRegularBallSubsolutionDataTwo e (fun j => Complex.I • e j)
            V (Icc (0 : ℝ) 1) s p (r p) (w p)) ∧
        ∃ delta > 0, ∀ t ∈ ball s delta, t ∈ Icc (0 : ℝ) 1 →
          (∀ p ∈ T,
            RegularBallSubsolutionDataTwo e (fun j => Complex.I • e j)
              (V t) p (r p/2) (fun y => w p (t,y))) ∧
          frontier (V t) ⊆ ⋃ p ∈ T, ball (p : E) (r p/4) := by
  let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hVK : IsCompact (closure (V s)) := by
    change IsCompact (closure (minkowskiDomain s U (ball (0 : E) R)))
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul s).add (hBK.smul (1-s))
  apply exists_finite_parameter_regular_subsolution_boundary_cover_two e (fun j => Complex.I • e j)
    (hVK.of_isClosed_subset isClosed_frontier frontier_subset_closure)
    (minkowskiDomain_real_frontier_parameterGraph_isCompact hU isOpen_ball hK hBK)
  intro x hx
  exact strong_defining_minkowski_exists_joint_regular_ball_subsolution_data_two
    hU hconv hK hUn hf hb hdelta hH e hab hs hs1 hR hx


theorem strong_defining_minkowski_exists_joint_global_regular_Levi_defining_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hUn : U.Nonempty) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hH : ∀ x ∈ frontier U, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian f x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {s R : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hR : 0 < R) :
    let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
    ∃ d > 0, ∃ F : ℝ × E → ℝ,
      ContDiffOn ℝ 4 F (ball s d ×ˢ (univ : Set E)) ∧
      ∀ t ∈ ball s d, t ∈ Icc (0 : ℝ) 1 →
        ContDiff ℝ 4 (fun x => F (t,x)) ∧ (∀ x ∈ V t, F (t,x) ≤ 0) ∧
        ∀ x ∈ frontier (V t), F (t,x) = 0 ∧ fderiv ℝ (fun y => F (t,y)) x ≠ 0 ∧
          (∀ᶠ z in 𝓝 x, z ∈ V t ↔ F (t,z) < 0) ∧
          ∀ v : E, v ≠ 0 → fderiv ℝ (fun y => F (t,y)) x v = 0 →
            fderiv ℝ (fun y => F (t,y)) x (Complex.I • v) = 0 →
            0 < realHessian (fun y => F (t,y)) x v v +
              realHessian (fun y => F (t,y)) x (Complex.I • v) (Complex.I • v) := by
  let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨r,w,T,hdata,delta,hdelta,hcover⟩ :=
    strong_defining_minkowski_exists_finite_parameter_subsolution_boundary_cover_two
      hU hconv hK hUn hf hb hdelta hH e hab hs hs1 hR
  have hVo (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) : IsOpen (V t) :=
    (minkowskiDomain_real_parameterGraph_isOpen hU isOpen_ball).preimage
      (continuous_const.prodMk continuous_id)
  obtain ⟨d,hd,_hddelta,F,hF,hFdata⟩ :=
    exists_joint_global_regular_Levi_defining_of_finite_subsolutions_two e hVo
      (fun t _ => minkowskiDomain_convex hconv (convex_ball (0 : E) R) t)
      (fun p : frontier (V s) => (p : E)) r w T hdata hdelta
      (fun t ht hI => (hcover t ht hI).2)
  exact ⟨d,hd,F,hF,hFdata⟩


end PowerConvexity
