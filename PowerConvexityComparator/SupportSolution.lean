import PowerConvexityComparator.SupportProblem
import PowerConvexityComparator.SeparationSolution
import PowerConvexity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexityComparator.SupportSolution
open AppendixAProblem SeparationProblem SupportProblem PowerConvexity CHS.Calculus

theorem robustnessAnswer : RobustnessStatement := by
  intro n μ hμ K hK u x hu hx ε hε hfamily
  letI : IsFiniteMeasureOnCompacts μ := hμ
  apply L2_quadratic_robustness_of_local_convexity μ hK xAxis hu hx hε
  intro q hq hEq
  exact hfamily q ((SeparationSolution.class_eq q).mp hq) hEq

theorem sigma_eq {u : CN 2 → ℝ} {x : CN 2} (hu : ContDiffAt ℝ 2 u x) :
    modifiedSigmaTwo xAxis yAxis u x = sigma u x := by
  unfold modifiedSigmaTwo
  rw [SeparationSolution.quotient_eq hu]
  rfl

theorem touchAnswer : TouchStatement := by
  intro U hU u hu ρ hρ hdet hneg hpos x hx hx0 hgap hm
  let e := (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis
  have he : (e : Fin 2 → CN 2) = xAxis := by
    funext i; exact EuclideanSpace.basisFun_apply (Fin 2) ℂ i
  have her : (complexRealBasis e : (Fin 2 ⊕ Fin 2) → CN 2) = Sum.elim xAxis yAxis := by
    rw [complexRealBasis_eq_sum,he]
    rfl
  have hjet (y : CN 2) (hy : y ∈ U) : ContDiffAt ℝ 2 u y :=
    (hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)
  have hx0' : modifiedSigmaTwo xAxis yAxis u x = 0 := by rw [sigma_eq (hjet x hx)]; exact hx0
  have hgap' : 0 < eigenDiscriminantTwo (modifiedK xAxis yAxis u x) := by
    rw [SeparationSolution.quotient_eq (hjet x hx)]
    exact hgap
  have hm' : IsLocalMin (modifiedSigmaTwo xAxis yAxis u) x := by
    change ∀ᶠ y in 𝓝 x, modifiedSigmaTwo xAxis yAxis u x ≤ modifiedSigmaTwo xAxis yAxis u y
    filter_upwards [hm,hU.mem_nhds hx] with y hy hyU
    rw [sigma_eq (hjet x hx),sigma_eq (hjet y hyU)]
    exact hy
  have hout := modifiedSigmaTwo_zero_localMin_propagates xAxis yAxis (complexRealBasis e) her
    hU hu hρ
    (fun y hy => by rw [AppendixASolution.mixed_eq (hjet y hy)]; exact hdet y hy)
    hneg (fun y hy => by rw [AppendixASolution.mixed_eq (hjet y hy)]; exact hpos y hy)
    hx hx0' hgap' hm'
  filter_upwards [hout,hU.mem_nhds hx] with y hy hyU
  rw [← sigma_eq (hjet y hyU)]
  exact hy

theorem stabilityAnswer : StabilityStatement := by
  intro μ hμ hopen K hK hKi U hU hconv hconn hCU hne u hu ρ hρ hdet hpos ε hε hneg h0 hbd
  letI : IsFiniteMeasureOnCompacts μ := hμ
  letI : Measure.IsOpenPosMeasure μ := hopen
  let e := (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis
  have he : (e : Fin 2 → CN 2) = xAxis := by
    funext i; exact EuclideanSpace.basisFun_apply (Fin 2) ℂ i
  have him : (fun j => Complex.I • e j) = yAxis := by rw [he]; rfl
  have hclass (q : CN 2 → ℝ) :
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q ↔ PluriharmonicQuadratic q := by
    rw [him,he]
    exact SeparationSolution.class_eq q
  have hjet (y : CN 2) (hy : y ∈ closure U) : ContDiffAt ℝ 2 u y := (hu y hy).of_le (by norm_num)
  have hc := paper_perturbation_stability_two μ hK hKi e hU hconv hconn hCU hne hu hρ
    (fun y hy => by
      rw [him,he,AppendixASolution.mixed_eq (hjet y (subset_closure hy))]
      exact hdet y hy)
    (fun y hy => by rw [him,he,AppendixASolution.mixed_eq (hjet y hy)]; exact hpos y hy)
    hε (fun q hq hEq y hy => hneg q ((hclass q).mp hq) hEq y hy) h0
    (fun q hq hEq y hy => hbd q ((hclass q).mp hq) hEq y hy)
  exact ⟨fun q hq hEq => hc.1 q ((hclass q).mpr hq) hEq,hc.2⟩

end PowerConvexityComparator.SupportSolution
