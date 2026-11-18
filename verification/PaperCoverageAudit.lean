import PowerConvexity.C114Complete
import PowerConvexityComparator.ReleaseSolution
import Lean

open Lean Meta

-- Keep the map accountable to the current release import environment.
#eval show MetaM Unit from do
  let env ← getEnv
  let mapped : Array String := #[
    "PowerConvexity.HasSimpleLeastSpectrum.charpoly_factors",
    "PowerConvexity.L2_quadratic_robustness_of_local_convexity",
    "PowerConvexity.SimpleRealEigenvalueJet.real_derivatives",
    "PowerConvexity.actual_classical_minkowski_family_exists_two",
    "PowerConvexity.actual_classical_minkowski_intermediate_family_two",
    "PowerConvexity.actual_hessian_determinant_identity",
    "PowerConvexity.actual_hessian_determinant_identity_interleaved",
    "PowerConvexity.actual_inverse_mixed_cancellation",
    "PowerConvexity.actual_modifiedSigmaTwo_envelope_positive",
    "PowerConvexity.actual_original_route_mainTheorem",
    "PowerConvexity.actual_paper_family_common_collar_exhaustion_two",
    "PowerConvexity.appendixC_geometric_main_strictConvexOn",
    "PowerConvexity.appendixC_main_strictConvexOn",
    "PowerConvexity.arrowMatrixThree_posSemidef_iff",
    "PowerConvexity.classical_dirichlet_unique_two",
    "PowerConvexity.cma_first_derivative",
    "PowerConvexity.compensatedField_dzbar",
    "PowerConvexity.compensatedHessian_eq",
    "PowerConvexity.complexHessian_det_const_first",
    "PowerConvexity.complexHessian_det_const_second",
    "PowerConvexity.complexHessian_powerTransform",
    "PowerConvexity.contactFullQuadratic_eq",
    "PowerConvexity.contactQuadratic_eq",
    "PowerConvexity.dimensionTwo_scalar_coercive",
    "PowerConvexity.dimensionTwo_scalar_sign",
    "PowerConvexity.dimensionTwo_skew_equality_iff_zero",
    "PowerConvexity.dimensionTwo_skew_sign",
    "PowerConvexity.dimensionTwo_skew_uniform_coercive",
    "PowerConvexity.divided_power_sum_distinct",
    "PowerConvexity.divided_power_sum_equal",
    "PowerConvexity.dz_inv_at",
    "PowerConvexity.dz_mixed_inv_at",
    "PowerConvexity.dz_mixed_trace_power",
    "PowerConvexity.dz_trace_power",
    "PowerConvexity.exists_curved_quadratic_energy_decrease",
    "PowerConvexity.exists_pluriharmonic_quadratic_minimizer_general",
    "PowerConvexity.exists_pluriharmonic_quadratic_minimizer_with_gap",
    "PowerConvexity.generalized_eigenvalue_dz_mixed",
    "PowerConvexity.inverseDerivativeField_dzbar",
    "PowerConvexity.inverse_conjugate_pure_divergence_const",
    "PowerConvexity.inverse_return_divergence",
    "PowerConvexity.inverse_spectral_gap_coefficient",
    "PowerConvexity.inverse_spectral_mixed_sum_cancellation",
    "PowerConvexity.largestRealEigenvalue_jet",
    "PowerConvexity.linearized_secondDerivative_det_const",
    "PowerConvexity.lowerEnvelope_positive_of_local_branches",
    "PowerConvexity.mainTheorem",
    "PowerConvexity.mainTwo_geometric_target_positive_realHessian",
    "PowerConvexity.mainTwo_geometric_target_strict_chord",
    "PowerConvexity.matrixDZ_inverse_of_det_ne_zero",
    "PowerConvexity.matrixDZ_inverse_return_nonsingular",
    "PowerConvexity.matrixDZ_modifiedSchur",
    "PowerConvexity.matrixL_entry",
    "PowerConvexity.matrix_A_equation_AA",
    "PowerConvexity.matrix_A_equation_BB",
    "PowerConvexity.matrix_B_equation_AB",
    "PowerConvexity.matrix_B_equation_BA",
    "PowerConvexity.matrix_differential_identities_const",
    "PowerConvexity.minkowski_actual_deformation_from_actual_boundary_sigma_two",
    "PowerConvexity.minkowski_classicalDirichlet_strongConvexity_limit_two",
    "PowerConvexity.minkowski_family_quadratic_minimum_continuous_two",
    "PowerConvexity.modifiedA_contracted_second",
    "PowerConvexity.modifiedA_dz",
    "PowerConvexity.modifiedA_dzbar",
    "PowerConvexity.modifiedA_dzbar_dz",
    "PowerConvexity.modifiedB_contracted_second",
    "PowerConvexity.modifiedB_dz",
    "PowerConvexity.modifiedB_dz_dzbar",
    "PowerConvexity.modifiedB_dzbar",
    "PowerConvexity.modifiedCompensatedHessian",
    "PowerConvexity.modifiedCompensated_contact_first_column_general",
    "PowerConvexity.modifiedCompensated_first_column_defect",
    "PowerConvexity.modifiedCompensated_transpose_difference",
    "PowerConvexity.modifiedK_smallestRealEigenvalue_jet",
    "PowerConvexity.modifiedK_tracePowerRoot_first_limit",
    "PowerConvexity.modifiedK_tracePowerRoot_real_second_limit_actual_largest",
    "PowerConvexity.modifiedK_tracePowerRoot_second_limit",
    "PowerConvexity.modifiedK_tracePowerRoot_second_limit_actual_largest",
    "PowerConvexity.modifiedPositiveProduct_tracePower_second_local_uniform",
    "PowerConvexity.modifiedSchur_LM_const_evaluated",
    "PowerConvexity.modifiedSchur_LM_contact_general",
    "PowerConvexity.modifiedSchur_column_normalized_remainder",
    "PowerConvexity.modifiedSchur_dz_contact_column",
    "PowerConvexity.modifiedSchur_dz_normalized",
    "PowerConvexity.modifiedSchur_dz_normalized_remainder",
    "PowerConvexity.modifiedSigmaTwo_actual_local_zero",
    "PowerConvexity.modifiedSigmaTwo_eventually_gradient_estimate",
    "PowerConvexity.modifiedSigmaTwo_leadingQuadratic_bound",
    "PowerConvexity.modifiedSigmaTwo_mixed_normalized",
    "PowerConvexity.modifiedSigmaTwo_mixed_normalized_exact",
    "PowerConvexity.modifiedSigmaTwo_normalized_gradient_estimate_explicit",
    "PowerConvexity.modifiedSigmaTwo_zero_localMin_propagates",
    "PowerConvexity.modifiedSigmaTwo_zero_simple_branch",
    "PowerConvexity.modifiedSigma_contact_contraction_eq_quadratic",
    "PowerConvexity.modifiedSigma_contact_dzMii",
    "PowerConvexity.modifiedSigma_contact_mixed",
    "PowerConvexity.modifiedSigma_dz_mixed_normalized_exact",
    "PowerConvexity.modifiedSigma_final_fullQ_contact",
    "PowerConvexity.modifiedSigma_normalized_jet",
    "PowerConvexity.modified_four_residuals_const",
    "PowerConvexity.no_common_ball_minimum_of_opposite_derivatives",
    "PowerConvexity.normalizedTraceSecondContraction_tendsto",
    "PowerConvexity.originalHessian_inverse_eq_normalized_rankOne",
    "PowerConvexity.paper_B10_1_actual_inverse_term",
    "PowerConvexity.paper_B3_1_tracePowerRoot_first_limit",
    "PowerConvexity.paper_B3_1_tracePowerRoot_real_first_limit",
    "PowerConvexity.paper_B3_2_tracePowerRoot_real_second_limit",
    "PowerConvexity.paper_B3_2_tracePowerRoot_second_limit",
    "PowerConvexity.paper_B3_3_tracePowerRoot_second_limit_actual_largest",
    "PowerConvexity.paper_B4_1_tracePowerRoot",
    "PowerConvexity.paper_B4_2_diagonal_trace_sum",
    "PowerConvexity.paper_B9_B10_actual_cancellation",
    "PowerConvexity.paper_Q11_trace_square",
    "PowerConvexity.paper_Q12_Q13_split",
    "PowerConvexity.paper_Q13_Q421_cancel",
    "PowerConvexity.paper_Q1_split",
    "PowerConvexity.paper_Q422_complement",
    "PowerConvexity.paper_Q42_split",
    "PowerConvexity.paper_Q61_split",
    "PowerConvexity.paper_Q63_simplify",
    "PowerConvexity.paper_Q64_Q66_simplify",
    "PowerConvexity.paper_Q66_initial_simplify",
    "PowerConvexity.paper_Q6_completed_square",
    "PowerConvexity.paper_perturbation_stability_two",
    "PowerConvexity.paper_typeI_from_numbered_components",
    "PowerConvexity.pluriharmonic_quadratic_minimizer_has_gap",
    "PowerConvexity.pluriharmonic_quadratic_minimizer_unique_takagi_maximum",
    "PowerConvexity.pluriharmonic_quadratic_perturbation_Hessian_stable_two",
    "PowerConvexity.power_mixed_posDef_iff_modifiedA",
    "PowerConvexity.pureHessian_powerTransform",
    "PowerConvexity.quadraticFamily_repeated_positive_not_minimum_general",
    "PowerConvexity.quadraticL2Energy_curved_difference",
    "PowerConvexity.rankOneWeightTwo_trace_im",
    "PowerConvexity.rankOne_fourfold_trace_square",
    "PowerConvexity.rankOne_trace_constraint",
    "PowerConvexity.rankOne_weight_gap",
    "PowerConvexity.readingTable_contact_P_row_general",
    "PowerConvexity.readingTable_contact_Q_column_general",
    "PowerConvexity.readingTable_contact_S_entry_general",
    "PowerConvexity.residual_four_contact_entry",
    "PowerConvexity.scalarAlpha",
    "PowerConvexity.scalarAlpha_dz",
    "PowerConvexity.scalarAlpha_normalized_first_remainder",
    "PowerConvexity.scalarBeta",
    "PowerConvexity.scalarBeta_dzbar",
    "PowerConvexity.scalarCompensated",
    "PowerConvexity.scalarCompensated_corrected_contact",
    "PowerConvexity.scalarDirichlet_negative",
    "PowerConvexity.scalarMu",
    "PowerConvexity.scalarMu_dz",
    "PowerConvexity.scalarMu_dz_eq_sigma_product",
    "PowerConvexity.scalarMu_eq_alpha_sigma",
    "PowerConvexity.scalarMu_mixed_eq_sigma_product",
    "PowerConvexity.scalarMu_mixed_zero_at_sigma_critical_zero",
    "PowerConvexity.scalarRatio_dzbar",
    "PowerConvexity.scalarSigma",
    "PowerConvexity.scalarSigma_dz_from_mu",
    "PowerConvexity.scalarSigma_local_gradient_estimate",
    "PowerConvexity.scalar_C211_normalized_remainder",
    "PowerConvexity.scalar_C212_normalized_remainder",
    "PowerConvexity.scalar_C213_normalized_remainder",
    "PowerConvexity.scalar_C31_normalized_error_bound",
    "PowerConvexity.scalar_C31_normalized_gradient_remainder",
    "PowerConvexity.scalar_constDensity_contDiffAt",
    "PowerConvexity.scalar_det_one_strict_plurisubharmonic",
    "PowerConvexity.scalar_normalized_paper_residual_bounds",
    "PowerConvexity.schurField_contracted_residual",
    "PowerConvexity.schurField_mixed_expansion_nonsingular",
    "PowerConvexity.schurField_mixed_residual",
    "PowerConvexity.schur_linearization_eq",
    "PowerConvexity.schur_linearization_nonpos",
    "PowerConvexity.schur_minimum_eq_one_iff",
    "PowerConvexity.schur_minimum_le_one",
    "PowerConvexity.schur_positive_product_real_eigenvalue_lt_one",
    "PowerConvexity.schur_positive_product_similarity",
    "PowerConvexity.shifted_matrices_of_holomorphic_square_tests",
    "PowerConvexity.shifted_matrices_of_powerHessian_lower",
    "PowerConvexity.skewThirdHessian_trace_zero",
    "PowerConvexity.smallestRealEigenvalue_jet",
    "PowerConvexity.tracePowerRoot_dz",
    "PowerConvexity.tracePowerRoot_dz_mixed",
    "PowerConvexity.tracePowerRoot_value_tendsto",
    "PowerConvexity.traceRootMixedJet_uniform_error_le",
    "PowerConvexity.traceRoot_dominant_cancellation_tendsto",
    "PowerConvexity.trace_diagonal_convolution_sum",
    "PowerConvexity.trace_power_convolution_coefficient_normalize",
    "PowerConvexity.trace_power_denominator_factor",
    "PowerConvexity.trace_power_first_contraction_limit",
    "PowerConvexity.trace_power_first_contraction_normalize",
    "PowerConvexity.trace_power_rank_coefficient_normalize",
    "PowerConvexity.trace_power_root_factor",
    "PowerConvexity.trace_power_root_tendsto",
    "PowerConvexity.trace_power_second_denominator_factor",
    "PowerConvexity.uniform_L2_quadratic_robustness",
    "PowerConvexity.uniform_L2_shifted_matrices",
    "PowerConvexity.weightedSquare_completion_from_Q"
  ]
  let missing := mapped.filter (fun n => !env.contains n.toName)
  unless missing.isEmpty do
    throwError "Source-map declarations missing in the release environment: {missing}"
  logInfo m!"PASS: all {mapped.size} Lean names in the frozen manuscript map resolve."

#check @PowerConvexity.actual_original_route_mainTheorem
#check @PowerConvexity.appendixC_geometric_main_strictConvexOn
#check @PowerConvexity.modifiedSigmaTwo_eventually_gradient_estimate
#check @PowerConvexity.modifiedSigmaTwo_zero_localMin_propagates
#check @PowerConvexity.paper_perturbation_stability_two
#check @PowerConvexity.actual_hessian_determinant_identity_interleaved
#check @PowerConvexity.arrowMatrixThree_posSemidef_iff
#check @PowerConvexity.exists_pluriharmonic_quadratic_minimizer_with_gap
#check @PowerConvexity.L2_quadratic_robustness_of_local_convexity
#check @PowerConvexity.uniform_L2_quadratic_robustness
#check @PowerConvexity.largestRealEigenvalue_jet
#check @PowerConvexity.smallestRealEigenvalue_jet
#check @PowerConvexity.actual_classical_minkowski_intermediate_family_two
#check @PowerConvexity.actual_classical_minkowski_family_exists_two
#check @PowerConvexity.actual_paper_family_common_collar_exhaustion_two
#check @PowerConvexity.minkowski_actual_deformation_from_actual_boundary_sigma_two
#check @PowerConvexity.minkowski_family_quadratic_minimum_continuous_two
#check @PowerConvexity.modifiedSigma_local_fullQ_error_general
#check @PowerConvexity.modifiedPositiveProduct_tracePower_second_local_uniform
#check @PowerConvexityComparator.Targets.main_theorem
#check @PowerConvexityComparator.Targets.appendix_c
#check @PowerConvexityComparator.Targets.determinant_identity
#check @PowerConvexityComparator.Targets.arrow_matrix
#check @PowerConvexityComparator.Targets.maximum_eigenvalue_derivatives
#check @PowerConvexityComparator.Targets.minimum_eigenvalue_derivatives
#check @PowerConvexityComparator.Targets.perturbation_minimizer
#check @PowerConvexityComparator.Targets.every_perturbation_minimizer
#check @PowerConvexityComparator.Targets.robustness
#check @PowerConvexityComparator.Targets.zero_contact
#check @PowerConvexityComparator.Targets.perturbation_stability
#check @PowerConvexityComparator.Targets.sigma_estimate
#check @PowerConvexityComparator.Targets.uniform_robustness
#check @PowerConvexityComparator.Targets.scalar_algebra
#check @PowerConvexityComparator.Targets.higher_dimension_algebra

#print axioms PowerConvexity.actual_original_route_mainTheorem
#print axioms PowerConvexity.appendixC_geometric_main_strictConvexOn
#print axioms PowerConvexity.modifiedSigmaTwo_eventually_gradient_estimate
#print axioms PowerConvexity.modifiedSigmaTwo_zero_localMin_propagates
#print axioms PowerConvexity.paper_perturbation_stability_two
#print axioms PowerConvexity.actual_hessian_determinant_identity_interleaved
#print axioms PowerConvexity.arrowMatrixThree_posSemidef_iff
#print axioms PowerConvexity.exists_pluriharmonic_quadratic_minimizer_with_gap
#print axioms PowerConvexity.L2_quadratic_robustness_of_local_convexity
#print axioms PowerConvexity.uniform_L2_quadratic_robustness
#print axioms PowerConvexity.largestRealEigenvalue_jet
#print axioms PowerConvexity.smallestRealEigenvalue_jet
#print axioms PowerConvexity.actual_classical_minkowski_intermediate_family_two
#print axioms PowerConvexity.actual_classical_minkowski_family_exists_two
#print axioms PowerConvexity.actual_paper_family_common_collar_exhaustion_two
#print axioms PowerConvexity.minkowski_actual_deformation_from_actual_boundary_sigma_two
#print axioms PowerConvexity.minkowski_family_quadratic_minimum_continuous_two
#print axioms PowerConvexity.modifiedSigma_local_fullQ_error_general
#print axioms PowerConvexity.modifiedPositiveProduct_tracePower_second_local_uniform
#print axioms PowerConvexityComparator.Targets.main_theorem
#print axioms PowerConvexityComparator.Targets.appendix_c
#print axioms PowerConvexityComparator.Targets.determinant_identity
#print axioms PowerConvexityComparator.Targets.arrow_matrix
#print axioms PowerConvexityComparator.Targets.maximum_eigenvalue_derivatives
#print axioms PowerConvexityComparator.Targets.minimum_eigenvalue_derivatives
#print axioms PowerConvexityComparator.Targets.perturbation_minimizer
#print axioms PowerConvexityComparator.Targets.every_perturbation_minimizer
#print axioms PowerConvexityComparator.Targets.robustness
#print axioms PowerConvexityComparator.Targets.zero_contact
#print axioms PowerConvexityComparator.Targets.perturbation_stability
#print axioms PowerConvexityComparator.Targets.sigma_estimate
#print axioms PowerConvexityComparator.Targets.uniform_robustness
#print axioms PowerConvexityComparator.Targets.scalar_algebra
#print axioms PowerConvexityComparator.Targets.higher_dimension_algebra
