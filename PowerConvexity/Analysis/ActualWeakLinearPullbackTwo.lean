import PowerConvexity.Analysis.ActualLinearChangeOfVariablesTwo

/-! # Actual Sobolev pullback by an invertible linear map.
The proof uses the original weak-derivative test identities. In particular,
it does not assume a classical derivative of the Sobolev function.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_weak_directional_identity_two {U : Set E} {u phi : E → ℝ}
    (uw : MemW1pWitness 2 u U) (v : E)
    (hp : ContDiff ℝ (⊤ : ℕ∞) phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ U) :
    (∫ x in U, u x*fderiv ℝ phi x v) =
      -∫ x in U, (∑ i, v i*uw.weakGrad x i)*phi x := by
  have hv : (∑ i, v i • EuclideanSpace.single i (1 : ℝ)) = v := by
    ext j
    simp [Pi.single_apply]
  have hd (i : Fin (2+2)) :
      MemLp (fun x => fderiv ℝ phi x (EuclideanSpace.single i 1)) 2 (volume.restrict U) :=
    (((hp.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) _)).restrict U
  have hpL : MemLp phi 2 (volume.restrict U) :=
    (hp.continuous.memLp_of_hasCompactSupport hc).restrict U
  have he (x : E) : u x*fderiv ℝ phi x v =
      ∑ i, v i*(u x*fderiv ℝ phi x (EuclideanSpace.single i 1)) := by
    nth_rw 1 [← hv]
    simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hf (x : E) : (∑ i, v i*uw.weakGrad x i)*phi x =
      ∑ i, v i*(uw.weakGrad x i*phi x) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [he,hf]
  have hli (i : Fin (2+2)) : Integrable (fun x =>
      v i*(u x*fderiv ℝ phi x (EuclideanSpace.single i 1))) (volume.restrict U) :=
    (uw.memLp.integrable_mul (hd i)).const_mul (v i)
  have hri (i : Fin (2+2)) : Integrable (fun x =>
      v i*(uw.weakGrad x i*phi x)) (volume.restrict U) :=
    ((uw.weakGrad_component_memLp i).integrable_mul hpL).const_mul (v i)
  rw [integral_finsetSum Finset.univ (fun i hi => hli i),
    integral_finsetSum Finset.univ (fun i hi => hri i)]
  simp_rw [integral_const_mul,uw.isWeakGrad _ phi hp hc hs,mul_neg]
  simp only [Finset.sum_neg_distrib]

def actualLinearWeakGradientTwo (G : E ≃L[ℝ] E) (W : E → E) : E → E :=
  fun z => WithLp.toLp 2 (fun i => ∑ j, (G (EuclideanSpace.single i 1)) j*W (G z) j)

theorem actual_linear_pullback_hasWeakGrad_two {U : Set E} {u : E → ℝ}
    (G : E ≃L[ℝ] E) (uw : MemW1pWitness 2 u U) :
    HasWeakGrad (actualLinearWeakGradientTwo G uw.weakGrad)
      (fun z => u (G z)) (G ⁻¹' U) := by
  intro i phi hp hc hs
  let psi : E → ℝ := fun x => phi (G.symm x)
  have hp' : ContDiff ℝ (⊤ : ℕ∞) psi := hp.comp G.symm.contDiff
  have hc' : HasCompactSupport psi := hc.comp_homeomorph G.symm.toHomeomorph
  have hs' : tsupport psi ⊆ U := by
    intro x hx
    have hx' := hs ((tsupport_comp_subset_preimage phi G.symm.continuous) hx)
    simpa only [mem_preimage,G.apply_symm_apply] using hx'
  have he (z : E) : fderiv ℝ psi (G z) (G (EuclideanSpace.single i 1)) =
      fderiv ℝ phi z (EuclideanSpace.single i 1) := by
    have hphi := ((hp.differentiable (by simp)).differentiableAt
      (x := G.symm (G z))).hasFDerivAt
    have hh := hphi.comp (G z) G.symm.hasFDerivAt
    rw [show psi = phi ∘ G.symm from rfl,hh.fderiv]
    simp
  have key := actual_weak_directional_identity_two uw
    (G (EuclideanSpace.single i 1)) hp' hc' hs'
  have hl := actual_setIntegral_linear_pullback_two (U := U) G
    (fun x => u x*fderiv ℝ psi x (G (EuclideanSpace.single i 1)))
  have hr := actual_setIntegral_linear_pullback_two (U := U) G
    (fun x => (∑ j, (G (EuclideanSpace.single i 1)) j*uw.weakGrad x j)*psi x)
  simp_rw [he] at hl
  rw [key] at hl
  change (∫ z in G ⁻¹' U, u (G z)*fderiv ℝ phi z (EuclideanSpace.single i 1)) =
    -∫ z in G ⁻¹' U, (∑ j, (G (EuclideanSpace.single i 1)) j*uw.weakGrad (G z) j)*phi z
  calc
    _ = -(|(LinearMap.det G.toLinearMap)⁻¹| *
        ∫ x in U, (∑ j, (G (EuclideanSpace.single i 1)) j*uw.weakGrad x j)*psi x) := by
      rw [hl,mul_neg]
    _ = _ := by
      rw [← hr]
      simp only [psi,G.symm_apply_apply]

def actual_linear_pullback_witness_two {U : Set E} {u : E → ℝ}
    (G : E ≃L[ℝ] E) (uw : MemW1pWitness 2 u U) :
    MemW1pWitness 2 (fun z => u (G z)) (G ⁻¹' U) where
  memLp := actual_memLp_linear_pullback_two G uw.memLp
  weakGrad := actualLinearWeakGradientTwo G uw.weakGrad
  weakGrad_component_memLp := by
    intro i
    exact memLp_finsetSum Finset.univ (fun j hj =>
      (actual_memLp_linear_pullback_two G (uw.weakGrad_component_memLp j)).const_mul
        ((G (EuclideanSpace.single i 1)) j))
  isWeakGrad := actual_linear_pullback_hasWeakGrad_two G uw

end PowerConvexity
