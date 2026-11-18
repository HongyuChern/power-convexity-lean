import PowerConvexity.Calculus.ParameterLeviStabilization
import PowerConvexity.Calculus.MinkowskiJointDefining
import PowerConvexity.Calculus.LocalStrictPshMinkowskiTwo

/-! # Actual jointly smooth strict psh defining functions near positive parameters

The original endpoint supplies the actual boundary Levi condition. A single
normal correction at the base point and actual joint derivative continuity
give strict psh defining functions on one common parameter-space neighborhood.
These are local barriers and do not assert existence of a Dirichlet solution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]

theorem parameter_smooth_defining_exists_strictPsh_neighborhood_two
    (e : Module.Basis (Fin 2) ℂ E) {V : ℝ → Set E} {S : Set ℝ}
    {F : ℝ × E → ℝ} {s : ℝ} {x : E}
    (hF : ContDiffAt ℝ ∞ F (s,x)) (hFx : F (s,x) = 0)
    (hDf : fderiv ℝ (fun y => F (s,y)) x ≠ 0)
    (hdef : ∀ᶠ p in 𝓝 (s,x), p.1 ∈ S → (p.2 ∈ V p.1 ↔ F p < 0))
    (hLevi : ∀ v : E, v ≠ 0 → fderiv ℝ (fun y => F (s,y)) x v = 0 →
      fderiv ℝ (fun y => F (s,y)) x (Complex.I • v) = 0 →
      0 < realHessian (fun y => F (s,y)) x v v+
        realHessian (fun y => F (s,y)) x (Complex.I • v) (Complex.I • v)) :
    ∃ rho : ℝ × E → ℝ,
      ContDiffAt ℝ ∞ rho (s,x) ∧ rho (s,x) = 0 ∧
      fderiv ℝ (fun y => rho (s,y)) x = fderiv ℝ (fun y => F (s,y)) x ∧
      (∀ᶠ p in 𝓝 (s,x),
        fderiv ℝ (fun y => rho (p.1,y)) p.2 ≠ 0 ∧
        (p.1 ∈ S → (p.2 ∈ V p.1 ↔ rho p < 0)) ∧
        ContDiffAt ℝ 4 (fun y => rho (p.1,y)) p.2 ∧
        (complexHessian e (fun j => Complex.I • e j) (fun y => rho (p.1,y)) p.2).PosDef) := by
  let I : E →L[ℝ] E := (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  have hI (v : E) : I v = Complex.I • v := rfl
  obtain ⟨rho,hrho,hrho0,hDrho,hn⟩ := exists_parameter_smooth_defining_positive_pair
    I hF hFx hDf hdef (by simpa only [hI] using hLevi)
  have hrho4 : ContDiffAt ℝ 4 rho (s,x) := (contDiffAt_infty.mp hrho) 4
  refine ⟨rho,hrho,hrho0,hDrho,?_⟩
  filter_upwards [hrho4.eventually (by norm_num),hn] with p hpreg hp
  have hreg : ContDiffAt ℝ 4 (fun y => rho (p.1,y)) p.2 :=
    hpreg.comp p.2 (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨hp.1,hp.2.1,hreg,complexHessian_posDef_of_paired_positive_two e
    (hreg.of_le (by norm_num)) ?_⟩
  simpa only [hI] using hp.2.2

theorem classicalDirichlet_minkowski_exists_joint_strictPsh_defining_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 < R)
    {x : E} (hx : x ∈ frontier (minkowskiDomain s U (ball (0 : E) R))) :
    ∃ rho : ℝ × E → ℝ,
      ContDiffAt ℝ ∞ rho (s,x) ∧ rho (s,x) = 0 ∧
      (∀ᶠ p in 𝓝 (s,x),
        ContDiffAt ℝ 4 (fun y => rho (p.1,y)) p.2 ∧
        fderiv ℝ (fun y => rho (p.1,y)) p.2 ≠ 0 ∧
        (complexHessian e (fun j => Complex.I • e j) (fun y => rho (p.1,y)) p.2).PosDef ∧
        (p.1 ∈ Icc (0 : ℝ) 1 →
          (p.2 ∈ minkowskiDomain p.1 U (ball (0 : E) R) ↔ rho p < 0))) := by
  obtain ⟨phi,hphi,hphi0,hDphi,hnear⟩ :=
    minkowskiDomain_exists_joint_smooth_defining_function hU hconv hK hboundary hs hs1 hR hx
  have hphis : ContDiffAt ℝ ∞ (fun y => phi (s,y)) x :=
    hphi.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hdef : ∀ᶠ y in 𝓝 x,
      y ∈ minkowskiDomain s U (ball (0 : E) R) ↔ phi (s,y) < 0 := by
    have hin : Tendsto (fun y : E => (s,y)) (𝓝 x) (𝓝 (s,x)) :=
      (continuousAt_const.prodMk continuousAt_id).tendsto
    filter_upwards [hin.eventually hnear] with y hy
    exact hy.2 ⟨hs.le,hs1⟩
  have hLevi : ∀ v : E, v ≠ 0 → fderiv ℝ (fun y => phi (s,y)) x v = 0 →
      fderiv ℝ (fun y => phi (s,y)) x (Complex.I • v) = 0 →
      0 < realHessian (fun y => phi (s,y)) x v v+
        realHessian (fun y => phi (s,y)) x (Complex.I • v) (Complex.I • v) := by
    by_cases hslt : s < 1
    · exact classicalDirichlet_minkowski_defining_Levi_positive_two
        hU hconv hK hboundary hu J hb e hab hpsh hdet hs hslt hR hx
        ((contDiffAt_infty.mp hphis) 2) hphi0 hDphi hdef
    · have hsEq : s = 1 := le_antisymm hs1 (not_lt.mp hslt)
      subst s
      have hBn : (ball (0 : E) R).Nonempty := ⟨0,mem_ball_self hR⟩
      rw [minkowskiDomain_one hBn] at hx hdef
      exact classicalDirichlet_defining_Levi_positive_two hU hconv hK hu J hb e hab hpsh hdet
        hx ((contDiffAt_infty.mp hphis) 2) hphi0 hDphi hdef
  obtain ⟨rho,hrho,hrho0,hDrho,hn⟩ :=
    parameter_smooth_defining_exists_strictPsh_neighborhood_two
      (V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)) (S := Icc (0 : ℝ) 1)
      e hphi hphi0 hDphi
      (hnear.mono (fun _ hp => hp.2)) hLevi
  refine ⟨rho,hrho,hrho0,?_⟩
  filter_upwards [hn] with p hp
  exact ⟨hp.2.2.1,hp.1,hp.2.2.2,hp.2.1⟩

end PowerConvexity
