import PowerConvexity.Calculus.MinkowskiSmoothBoundary

/-! # An actual jointly smooth inverse preserving a real parameter

The total graph map is locally inverted using the locked finite-dimensional
inverse theorem.  Its inverse preserves the parameter because the original
graph map does.  No continuity of a separately chosen family of inverses is
assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem parameterGraph_fderiv_injective
    {F : ℝ × E → E} {s : ℝ} {x : E}
    (hF : DifferentiableAt ℝ F (s,x))
    (hi : Function.Injective (fderiv ℝ (fun y => F (s,y)) x)) :
    Function.Injective (fderiv ℝ (fun p : ℝ × E => (p.1,F p)) (s,x)) := by
  let D := fderiv ℝ F (s,x)
  have hgraph : HasFDerivAt (fun p : ℝ × E => (p.1,F p))
      ((ContinuousLinearMap.fst ℝ ℝ E).prod D) (s,x) :=
    hasFDerivAt_fst.prodMk hF.hasFDerivAt
  have hfiber : fderiv ℝ (fun y => F (s,y)) x =
      D.comp (ContinuousLinearMap.inr ℝ ℝ E) :=
    (hF.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)).fderiv
  rw [hgraph.fderiv]
  intro p q hpq
  change (p.1,D p) = (q.1,D q) at hpq
  have hfirst' := congrArg (fun z : ℝ × E => z.1) hpq
  have hfirst : p.1 = q.1 := hfirst'
  have hsecond : D p = D q := congrArg Prod.snd hpq
  have hzero : p-q = (0,p.2-q.2) := by ext <;> simp [hfirst]
  have hDzero : D (0,p.2-q.2) = 0 := by
    rw [← hzero,map_sub,hsecond,sub_self]
  have hsecond' : p.2-q.2 = 0 := hi (by
    rw [hfiber]
    change D (0,p.2-q.2) = D 0
    simpa only [map_zero] using hDzero)
  exact Prod.ext hfirst (sub_eq_zero.mp hsecond')

theorem exists_parameter_preserving_smooth_localInverse
    {F : ℝ × E → E} {s : ℝ} {x : E}
    (hF : ContDiffAt ℝ ∞ F (s,x))
    (hi : Function.Injective (fderiv ℝ (fun y => F (s,y)) x)) :
    ∃ g : ℝ × E → E,
      ContDiffAt ℝ ∞ g (s,F (s,x)) ∧
      g (s,F (s,x)) = x ∧
      (∀ᶠ p in 𝓝 (s,F (s,x)), F (p.1,g p) = p.2) ∧
      (∀ᶠ p in 𝓝 (s,x), g (p.1,F p) = p.2) := by
  let G := fun p : ℝ × E => (p.1,F p)
  have hG : ContDiffAt ℝ ∞ G (s,x) := contDiffAt_fst.prodMk hF
  let L := fderiv ℝ G (s,x)
  have hLi : Function.Injective L :=
    parameterGraph_fderiv_injective (hF.differentiableAt (by norm_num)) hi
  let e : (ℝ × E) ≃L[ℝ] (ℝ × E) :=
    (LinearEquiv.ofInjectiveEndo L.toLinearMap hLi).toContinuousLinearEquiv
  have he : (e : (ℝ × E) →L[ℝ] (ℝ × E)) = L := by
    apply ContinuousLinearMap.ext
    intro p
    rfl
  have hGd : HasFDerivAt G (e : (ℝ × E) →L[ℝ] (ℝ × E)) (s,x) := by
    rw [he]
    exact (hG.differentiableAt (by norm_num)).hasFDerivAt
  let H := hG.localInverse hGd (by norm_num)
  have hH : ContDiffAt ℝ ∞ H (G (s,x)) := hG.to_localInverse hGd (by norm_num)
  have hHx : H (G (s,x)) = (s,x) := hG.localInverse_apply_image hGd (by norm_num)
  have hright : ∀ᶠ p in 𝓝 (G (s,x)), G (H p) = p :=
    (hG.hasStrictFDerivAt' hGd (by norm_num)).eventually_right_inverse
  have hleft : ∀ᶠ p in 𝓝 (s,x), H (G p) = p :=
    (hG.hasStrictFDerivAt' hGd (by norm_num)).eventually_left_inverse
  refine ⟨fun p => (H p).2,hH.snd,congrArg Prod.snd hHx,?_,?_⟩
  · filter_upwards [hright] with p hp
    change ((H p).1,F (H p)) = p at hp
    have hp1' := congrArg (fun z : ℝ × E => z.1) hp
    have hp1 : (H p).1 = p.1 := hp1'
    have hp2 : F (H p) = p.2 := congrArg Prod.snd hp
    simpa only [← hp1,Prod.mk.eta] using hp2
  · filter_upwards [hleft] with p hp
    exact congrArg Prod.snd hp

end PowerConvexity
