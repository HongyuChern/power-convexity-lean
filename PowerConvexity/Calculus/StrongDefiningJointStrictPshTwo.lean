import PowerConvexity.Calculus.StrongDefiningJointMinkowskiGeometry
import PowerConvexity.Calculus.MinkowskiJointStrictSubsolutionTwo
import PowerConvexity.Analysis.MinkowskiBoundaryNeighborhoods

/-! # Joint strict psh local defining functions for strong approximants

The actual strong defining Hessian supplies positive tangent curvature for
positive parameters. At parameter zero the true ball supplies the Levi form.
The augmented normal map provides the common joint defining neighborhood;
no Dirichlet solution on an intermediate domain is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]

theorem strong_defining_minkowski_exists_joint_strictPsh_defining_two
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
    ∃ rho : ℝ × E → ℝ,
      ContDiffAt ℝ ∞ rho (s,x) ∧ rho (s,x)=0 ∧
      (∀ᶠ p in 𝓝 (s,x),
        ContDiffAt ℝ 4 (fun y => rho (p.1,y)) p.2 ∧
        fderiv ℝ (fun y => rho (p.1,y)) p.2≠0 ∧
        (complexHessian e (fun j => Complex.I • e j) (fun y => rho (p.1,y)) p.2).PosDef ∧
        (p.1 ∈ Icc (0 : ℝ) 1 →
          (p.2 ∈ minkowskiDomain p.1 U (ball (0 : E) R) ↔ rho p<0))) := by
  have hc (y : E) (hy : y ∈ frontier U) (v : E) (_hv : fderiv ℝ f y v=0) (hv0 : v≠0) :
      0 < realHessian f y v v :=
    (mul_pos (mul_pos (by norm_num) hdelta) (sq_pos_of_pos (norm_pos_iff.mpr hv0))).trans_le
      (hH y hy v)
  obtain ⟨phi,hphi,hphi0,hDphi,hnear⟩ :=
    strong_defining_minkowski_exists_joint_smooth_defining_function hU hconv hK hUn hf hb hc
      hs hs1 hR hx
  have hphis : ContDiffAt ℝ ∞ (fun y => phi (s,y)) x :=
    hphi.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hdef : ∀ᶠ y in 𝓝 x,
      y ∈ minkowskiDomain s U (ball (0 : E) R) ↔ phi (s,y)<0 := by
    have hin : Tendsto (fun y : E => (s,y)) (𝓝 x) (𝓝 (s,x)) :=
      (continuousAt_const.prodMk continuousAt_id).tendsto
    filter_upwards [hin.eventually hnear] with y hy
    exact hy.2 ⟨hs,hs1⟩
  have hLevi : ∀ v : E, v≠0 → fderiv ℝ (fun y => phi (s,y)) x v=0 →
      fderiv ℝ (fun y => phi (s,y)) x (Complex.I • v)=0 →
      0 < realHessian (fun y => phi (s,y)) x v v+
        realHessian (fun y => phi (s,y)) x (Complex.I • v) (Complex.I • v) := by
    by_cases hs0 : s=0
    · subst s
      rw [minkowskiDomain_zero hUn] at hx hdef
      let w : E → ℝ := quadraticBallPotential 1 R
      have hw : ContDiff ℝ 2 w := quadraticBallPotential_contDiff 1 R 2
      obtain ⟨_,⟨J⟩⟩ := c2OnClosure_of_neighborhood (U := ball (0 : E) R)
        isOpen_univ (subset_univ _) hw.contDiffOn
      have hKb : IsCompact (closure (ball (0 : E) R)) := by
        rw [closure_ball 0 hR.ne']
        exact isCompact_closedBall 0 R
      apply classicalDirichlet_defining_Levi_positive_two isOpen_ball (convex_ball 0 R) hKb
        hw.contDiffOn J (fun y hy => ?_) e hab (fun y _ => ?_) (fun y _ => ?_)
        hx ((contDiffAt_infty.mp hphis) 2) hphi0 hDphi hdef
      · apply quadraticBallPotential_boundary
        rwa [frontier_ball 0 hR.ne'] at hy
      · change (complexHessian e (fun j => Complex.I • e j) (quadraticBallPotential 1 R) y).PosDef
        rw [quadraticBallPotential_complexHessian e (fun j => Complex.I • e j) hab]
        simpa only [Complex.ofReal_one,one_smul] using
          (Matrix.PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℂ).PosDef)
      · simpa only [one_pow,Complex.ofReal_one] using quadraticBallPotential_det_two
          e (fun j => Complex.I • e j) hab 1 R y
    · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      obtain ⟨kappa,hk,hcurv⟩ := strong_defining_minkowski_actual_tangent_curvature_uniform_lower
        hU hconv hK ((contDiff_infty.mp hf) 3) hb hdelta hH hR
      intro v hv htv htIv
      have hvlo := hcurv s hsp hs1 x hx (fun y => phi (s,y))
        ((contDiffAt_infty.mp hphis) 2) hphi0 hDphi hdef v htv
      have hgp : 0 < ‖gradient (fun y => phi (s,y)) x‖ :=
        norm_pos_iff.mpr (definingGradient_ne_zero hDphi)
      have hpos : 0 < realHessian (fun y => phi (s,y)) x v v :=
        (div_pos_iff_of_pos_right hgp).mp
          ((mul_pos hk (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le hvlo)
      have hVo : IsOpen (minkowskiDomain s U (ball (0 : E) R)) :=
        (minkowskiDomain_real_parameterGraph_isOpen hU isOpen_ball).preimage
          (continuous_const.prodMk continuous_id)
      have hnonneg := definingFunction_tangent_hessian_nonneg_of_convex hVo
        (minkowskiDomain_convex hconv (convex_ball (0 : E) R) s) hx
        ((contDiffAt_infty.mp hphis) 2) hphi0 hDphi hdef (Complex.I • v) htIv
      exact add_pos_of_pos_of_nonneg hpos hnonneg
  obtain ⟨rho,hrho,hrho0,_,hn⟩ := parameter_smooth_defining_exists_strictPsh_neighborhood_two
    (V := fun t => minkowskiDomain t U (ball (0 : E) R)) (S := Icc (0 : ℝ) 1)
    e hphi hphi0 hDphi (hnear.mono (fun _ hp => hp.2)) hLevi
  refine ⟨rho,hrho,hrho0,?_⟩
  filter_upwards [hn] with p hp
  exact ⟨hp.2.2.1,hp.1,hp.2.2.2,hp.2.1⟩

end PowerConvexity
