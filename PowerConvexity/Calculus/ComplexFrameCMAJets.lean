import PowerConvexity.Calculus.CMAJetsIsometricTransport
import PowerConvexity.Calculus.ComplexRealBasis
import PowerConvexity.Calculus.MinkowskiSecondJetsFromBoundaryUpperTwo

/-! # The actual CMA jet criterion in a fixed orthonormal complex frame -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem bilinear_norm_le_of_isometric_entries {d : ℕ}
    (L : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] E) (H : E →L[ℝ] E →L[ℝ] ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hentry : ∀ i j, |H (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))| ≤ M) :
    ‖H‖ ≤ (d : ℝ)^2*M := by
  let P : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    H.bilinearComp L.toContinuousLinearEquiv.toContinuousLinearMap
      L.toContinuousLinearEquiv.toContinuousLinearMap
  have hP : ‖P‖ ≤ (d : ℝ)^2*M := by
    simpa only [Fintype.card_fin] using euclidean_bilinear_norm_le_of_entry_bound P hM hentry
  apply H.opNorm_le_bound (by positivity)
  intro v
  apply (H v).opNorm_le_bound (by positivity)
  intro w
  have hh : ‖H v w‖ ≤ ‖P‖*‖v‖*‖w‖ := by
    simpa only [P,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,L.apply_symm_apply,L.symm.norm_map] using
      P.le_opNorm₂ (L.symm v) (L.symm w)
  exact hh.trans (by gcongr)

theorem realHessian_family_continuousAt_of_values_CMA_isometric_boundary_upper
    {n : ℕ} (hn : 2 ≤ n) (L : DeGiorgi.AmbientSpace (n+n) ≃ₗᵢ[ℝ] E)
    {T : Type*} [TopologicalSpace T] {u : T → E → ℝ} {U : T → Set E}
    (J : ∀ t, ClosureC2Jet (u t) (U t)) {t₀ : T} {x₀ : E} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hval : ∀ y ∈ closedBall x₀ (3*R),
      ContinuousAt (fun p : T × E => u p.1 p.2) (t₀,y))
    (hdata : ∀ᶠ t in 𝓝 t₀,
      IsOpen (U t) ∧ IsCompact (closure (U t)) ∧ ContDiffOn ℝ 4 (u t) (U t) ∧
      (∀ x ∈ frontier (U t), u t x = 0) ∧
      (∀ x ∈ U t,
        (complexHessian (fun i => L (realDirections i)) (fun i => L (imagDirections i)) (u t) x).PosDef) ∧
      (∀ x ∈ U t,
        (complexHessian (fun i => L (realDirections i)) (fun i => L (imagDirections i)) (u t) x).det = 1) ∧
      ball x₀ (4*R) ⊆ U t ∧
      (∀ x ∈ frontier (U t), ∀ v : E, (J t).hessian x v v ≤ M*‖v‖^2)) :
    ContinuousAt (fun p : T × E => fderiv ℝ (u p.1) p.2) (t₀,x₀) ∧
    ContinuousAt (fun p : T × E => realHessian (u p.1) p.2) (t₀,x₀) := by
  have hn0 : n ≠ 0 := by omega
  letI : NeZero n := ⟨hn0⟩
  have hframe : Sum.elim (fun i => L (realDirections (n := n) i)) (fun i => L (imagDirections i)) =
      fun i => L (Sum.elim realDirections imagDirections i) := by
    funext i
    cases i <;> rfl
  have hnorm (i : Fin n ⊕ Fin n) :
      ‖Sum.elim (fun j => L (realDirections j)) (fun j => L (imagDirections j)) i‖ ≤ 1 := by
    rw [hframe,L.norm_map,blockDirection_eq_single]
    simp
  apply realHessian_family_continuousAt_of_values_CMA_isometric_bound hn L hR
    (by positivity : 0 ≤ ((n+n : ℕ) : ℝ)^2*(3*M)) hval
  filter_upwards [hdata] with t ht
  rcases ht with ⟨hU,hK,hu,hb,hpos,hdet,hball,hboundary⟩
  refine ⟨hu.mono hball,fun x hx => hdet x (hball hx),fun x hx => hpos x (hball hx),?_⟩
  intro x hx
  apply bilinear_norm_le_of_isometric_entries L (realHessian (u t) x) (by positivity : 0 ≤ 3*M)
  intro i j
  have hh := realBlockHessian_abs_le_of_boundary_quadratic_upper hU hK hu (J t) hb
    (fun i => L (realDirections i)) (fun i => L (imagDirections i)) hnorm
    hpos hdet hM hboundary x (hball hx) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  simpa only [realBlockHessian,hframe,blockDirection_eq_single,Equiv.apply_symm_apply] using hh

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem exists_euclideanIsometry_complexFrame_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j))) :
    ∃ L : DeGiorgi.AmbientSpace (2+2) ≃ₗᵢ[ℝ] E,
      (∀ i, L (realDirections i) = e i) ∧ (∀ i, L (imagDirections i) = Complex.I • e i) := by
  let B := (complexRealBasis e).toOrthonormalBasis
    (by simpa only [complexRealBasis_eq_sum] using hab)
  let C : OrthonormalBasis (Fin (2+2)) ℝ E := B.reindex finSumFinEquiv
  let L : DeGiorgi.AmbientSpace (2+2) ≃ₗᵢ[ℝ] E := C.repr.symm
  have hblock (i : Fin 2 ⊕ Fin 2) :
      L (Sum.elim realDirections imagDirections i) = Sum.elim e (fun j => Complex.I • e j) i := by
    rw [blockDirection_eq_single]
    change C.repr.symm (EuclideanSpace.single (finSumFinEquiv i) 1) = _
    rw [C.repr_symm_single]
    change (B.reindex finSumFinEquiv) (finSumFinEquiv i) = _
    rw [OrthonormalBasis.reindex_apply,Equiv.symm_apply_apply]
    change (complexRealBasis e).toOrthonormalBasis _ i = _
    simpa only [Module.Basis.coe_toOrthonormalBasis,complexRealBasis_eq_sum]
  exact ⟨L,fun i => hblock (.inl i),fun i => hblock (.inr i)⟩

variable [FiniteDimensional ℝ E]

theorem minkowski_classicalDirichlet_complexFrame_jets_of_boundary_upper_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : Convex ℝ A) (hB : Convex ℝ B) {ρ D : ℝ} (hρ : 0 < ρ) (hD : 0 ≤ D)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ B)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ D) (hBb : ∀ x ∈ B, ‖x‖ ≤ D)
    {u : Icc (0 : ℝ) 1 → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A B u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A B))
    {s : Icc (0 : ℝ) 1} {x : E} (hx : x ∈ minkowskiDomain s A B)
    (hbound : ∃ M ≥ 0, ∀ᶠ t : Icc (0 : ℝ) 1 in 𝓝 s, ∀ z ∈ frontier (minkowskiDomain t A B),
      ∀ v : E, (J t).hessian z v v ≤ M*‖v‖^2) :
    ContinuousAt (fun p : Icc (0 : ℝ) 1 × E => fderiv ℝ (u p.1) p.2) (s,x) ∧
    ContinuousAt (fun p : Icc (0 : ℝ) 1 × E => realHessian (u p.1) p.2) (s,x) := by
  obtain ⟨L,hLa,hLb⟩ := exists_euclideanIsometry_complexFrame_two e hab
  have hLa' : (fun i => L (realDirections i)) = e := funext hLa
  have hLb' : (fun i => L (imagDirections i)) = (fun j => Complex.I • e j) := funext hLb
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hρ.le)⟩
  have hV (t : Icc (0 : ℝ) 1) : IsOpen (minkowskiDomain t A B) :=
    minkowskiDomain_isOpen hAo hBo hAn t
  have hK (t : Icc (0 : ℝ) 1) : IsCompact (closure (minkowskiDomain t A B)) :=
    minkowskiDomain_isCompact_closure hAb hBb t.2.1 t.2.2
  have hZ := hu.joint_continuous hab hAo hBo hA hB hρ hD hballA hballB hAb hBb
  obtain ⟨r,hr,hball0,hball⟩ := minkowskiDomain_eventually_contains_closedBall
    hA hB hρ hD hballA hballB hAb hBb (hV s) hx
  obtain ⟨M,hM,hboundary⟩ := hbound
  have hR : 0 < r/4 := by positivity
  have h3R : 3*(r/4) ≤ r := by linarith
  have h4R : 4*(r/4) = r := by ring
  have hval (y : E) (hy : y ∈ closedBall x (3*(r/4))) :
      ContinuousAt (fun p : Icc (0 : ℝ) 1 × E => u p.1 p.2) (s,y) := by
    have hyV := hball0 ((closedBall_subset_closedBall h3R) hy)
    apply hZ.continuousAt.congr_of_eventuallyEq
    filter_upwards [minkowskiDomain_joint_mem_nhds
      hA hB hρ hD hballA hballB hAb hBb (hV s) hyV] with p hp
    simp only [Set.indicator_of_mem hp]
  apply realHessian_family_continuousAt_of_values_CMA_isometric_boundary_upper
    (by norm_num : 2 ≤ 2) L J hR hM hval
  filter_upwards [hball,hboundary] with t hballt hbt
  rw [hLa',hLb']
  refine ⟨hV t,hK t,(hu t).1,(hu t).2.2.2.2,(hu t).2.2.1,(hu t).2.2.2.1,?_,hbt⟩
  rw [h4R]
  exact ball_subset_closedBall.trans hballt

end PowerConvexity
