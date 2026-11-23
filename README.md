# Spatial scale space from hemigroup axioms: the theory of image pyramids — release pyramids-v0.1

This repository is the verification artifact of the article of the same name (the PDF is at the
root, with its supplement). It is an export of the development repository at revision `137e1c9`, restricted to
what the article's statements rest on; the development repository also holds the material of
other modules of the same theory and stays private until they are released.

## What is here

- `Formalization/` — the Lean 4 development: the transitive import closure of every module that a
  numbered statement of the article names (174 modules), with the toolchain pinned
  in-tree (`lean-toolchain`, `lake-manifest.json`).
- `Formalization/CIAxiomGuard.lean` — prints the axiom usage of every named declaration.
- `blueprint/trust-boundary.txt`, `blueprint/AXIOMS.md` — the 14 interface names of
  the full development, each with the page-verified citation it rests on and the step it carries
  beyond its source; `blueprint/AXIOMS-verbatim.md`, where it is present, sets the sources' own
  wording beside each entry. The headline theorem, `Pyramids.lattice_strata_2`, rests on 4 of them, and section 1.1 of the paper says what the other results rest on.
- `blueprint/src/parts/` — the statements and proofs of record of the article and its supplement (the
  blueprint's chapters 2–5 and Appendix A), with the `\lean{}` tag naming the declaration
  behind each statement; a chapter of another module is included where the article transcribes a
  statement from it.
- `paper/`, `figures/` — the article's sources.
- `notes/` — the process account, the external reviews verbatim, and the response plan.
- `scripts/make_figures_theory.py`, `scripts/grid_pyramid_exactness.py`, `scripts/sampled_gaussian_increments.py`, `scripts/theory_axioms_table.py`, `scripts/theory_axioms_lean.py` — the files that the article names by these paths.

## Verifying

    cd Formalization
    lake exe cache get        # Mathlib's prebuilt oleans
    lake build
    lake env lean CIAxiomGuard.lean

The last command prints, for `Pyramids.lattice_strata_2`, Lean's three logical axioms and
`AffineHemigroup.khintchine_null_array`, `AffineHemigroup.levy_khintchine_converse`, `AffineHemigroup.levy_khintchine_exists`, `AffineHemigroup.levy_khintchine_unique`, and nothing else (the block that the paper prints).

## Statements and declarations

| blueprint node (chapter) | declarations |
|---|---|
| `thm:cited-A1 (02)` | `Pyramids.cited_A1_repr`, `Pyramids.cited_A1_symm`, `Pyramids.cited_A1_converse` |
| `thm:cited-A9 (02)` | `Pyramids.cited_A9` |
| `def:self-decomposable (02)` | `Pyramids.IsSDResidual`, `Pyramids.IsSemiSelfDecomposableWithSpan`, `Pyramids.IsSemiSelfDecomposable` |
| `thm:cited-A4 (02)` | `Pyramids.cited_A4`, `Pyramids.cited_A4_exists`, `Pyramids.cited_A4_unique` |
| `thm:cited-A30 (02)` | `Pyramids.cited_A30_repr`, `Pyramids.cited_A30_converse`, `Pyramids.cited_A30_continuity` |
| `thm:cited-A31 (02)` | `Pyramids.cited_A31`, `Pyramids.cited_A31_unique` |
| `thm:cited-A34 (02)` | `Pyramids.cited_A34` |
| `thm:cited-A35 (02)` | `Pyramids.cited_A35_reading`, `Pyramids.cited_A35_unique`, `Pyramids.cited_A35_admissible`, `Pyramids.cited_A35_classA` |
| `thm:cited-A13 (02)` | `Pyramids.cited_A13` |
| `thm:cited-A15 (02)` | `Pyramids.cited_A15_admissible`, `Pyramids.cited_A15_injective`, `Pyramids.cited_A15_inverse`, `Pyramids.cited_A15_extreme` |
| `thm:cited-A19 (02)` | `Pyramids.cited_A19_transform`, `Pyramids.cited_A19_sections`, `Pyramids.cited_A19_forward`, `Pyramids.cited_A19_backward`, `Pyramids.cited_A19_gamma_one` |
| `thm:cited-A20 (02)` | `Pyramids.cited_A20_unique`, `Pyramids.cited_A20_product`, `Pyramids.cited_A20_profile`, `Pyramids.cited_A20_admissible`, `Pyramids.cited_A20_admissible_of_antitone` |
| `thm:cited-A22 (02)` | `Pyramids.cited_A22_variation`, `Pyramids.cited_A22_polya` |
| `thm:cited-A23 (02)` | `Pyramids.cited_A23` |
| `thm:cited-A39 (02)` | `Pyramids.cited_A39_exists`, `Pyramids.cited_A39_unique`, `Pyramids.cited_A39_converse` |
| `thm:cited-A40 (02)` | `Pyramids.cited_A40` |
| `thm:cited-A41 (02)` | `Pyramids.cited_A41` |
| `thm:cited-A42 (02)` | `Pyramids.cited_A42` |
| `thm:cited-A43 (02)` | `Pyramids.cited_A43_sd`, `Pyramids.cited_A43_semi`, `Pyramids.cited_A43_span` |
| `thm:cited-A44 (02)` | `Pyramids.cited_A44` |
| `thm:cited-A45 (02)` | `Pyramids.cited_A45` |
| `thm:cited-A46 (02)` | `Pyramids.cited_A46` |
| `thm:cited-A48 (02)` | `Pyramids.cited_A48`, `Pyramids.cited_A48_finite` |
| `thm:cited-A49 (02)` | `Pyramids.cited_A49` |
| `thm:cited-A50 (02)` | `Pyramids.cited_A50` |
| `def:complete-bernstein (02)` | `Pyramids.IsCompletelyMonotone`, `Pyramids.IsBernsteinFunction`, `Pyramids.IsCompleteBernstein` |
| `def:thorin-bernstein (02)` | `Pyramids.IsThorinBernstein` |
| `thm:cited-A55 (02)` | `Pyramids.cited_A55` |
| `thm:cited-A57 (02)` | `Pyramids.cited_A57` |
| `thm:cited-A24 (02)` | `Pyramids.cited_A24` |
| `thm:cited-A51 (02)` | `Pyramids.cited_A51_integral` |
| `def:q-covariant-line (02)` | `Pyramids.qPowers`, `Pyramids.IsQCovariantLine`, `Pyramids.IsCanonicalDiscreteGauge`, `Pyramids.IsFullyCovariantLine` |
| `lem:line-axioms-kernels (02)` | `Pyramids.line_axioms_kernels_1_exists`, `Pyramids.line_axioms_kernels_1`, `Pyramids.line_axioms_kernels_1_family`, `Pyramids.line_axioms_kernels_2`, `Pyramids.line_axioms_kernels_2_family`, `Pyramids.line_axioms_kernels_3`, `Pyramids.line_axioms_kernels_qcov` |
| `lem:closed-subgroups (02)` | `Pyramids.closed_subgroups_1`, `Pyramids.closed_subgroups_2` |
| `def:folded-data (02)` | `Pyramids.IsFoldedData` |
| `lem:discrete-covariance-line (02)` | `Pyramids.discrete_covariance_line`, `Pyramids.discrete_covariance_line_semi`, `Pyramids.discrete_covariance_line_annulus` |
| `thm:lattice-line (02)` | `Pyramids.lattice_line_1`, `Pyramids.lattice_line_1_converse`, `Pyramids.lattice_line_2`, `Pyramids.lattice_line_3`, `Pyramids.lattice_line_3_then` |
| `prop:lindeberg-stratum-one (02)` | `Pyramids.lindeberg_stratum_one_1`, `Pyramids.lindeberg_stratum_one_2`, `Pyramids.lindeberg_stratum_one_3` |
| `prop:discrete-gaussian-pyramid (02)` | `Pyramids.discrete_gaussian_pyramid_1`, `Pyramids.discrete_gaussian_pyramid_2`, `Pyramids.discrete_gaussian_pyramid_3` |
| `cor:lattice-line-strict (02)` | `Pyramids.lattice_line_strict_imp`, `Pyramids.lattice_line_strict_lower`, `Pyramids.lattice_line_strict_upper`, `Pyramids.lattice_line_strict` |
| `prop:no-lattice-kernel-line (02)` | `Pyramids.no_lattice_kernel_line_1`, `Pyramids.no_lattice_kernel_line_2` |
| `def:grid-pyramid-line (02)` | `Pyramids.IsGridMask`, `Pyramids.gridLadderStep`, `Pyramids.CarriesGridLadder`, `Pyramids.IsExactGridPyramid`, `Pyramids.IsExactGridPyramidThird` |
| `prop:grid-pyramids-infinitely-divisible (02)` | `Pyramids.grid_pyramids_id_1`, `Pyramids.grid_pyramids_id_2`, `Pyramids.grid_pyramids_id_2_knot`, `Pyramids.grid_pyramids_id_2_carrier`, `Pyramids.grid_pyramids_id_2_no_kernel`, `Pyramids.grid_pyramids_id_2_not_every`, `Pyramids.grid_pyramids_id_2_coupling`, `Pyramids.grid_pyramids_id_3`, `Pyramids.grid_pyramids_id_3_general`, `Pyramids.grid_pyramids_id_4`, `Pyramids.grid_pyramids_id_4_binomial`, `Pyramids.grid_pyramids_id_4_bounded` |
| `prop:recursion-helmholtz (02)` | `Pyramids.recursion_line_transforms`, `Pyramids.recursion_line_passes`, `Pyramids.recursion_line_increment`, `Pyramids.recursion_grid_transform`, `Pyramids.recursion_grid_green`, `Pyramids.recursion_grid_factor`, `Pyramids.recursion_grid_passes` |
| `prop:sampled-laplace-exact (02)` | `Pyramids.sampled_laplace_exact_sample`, `Pyramids.sampled_laplace_exact_transfer`, `Pyramids.sampled_laplace_exact_periodization`, `Pyramids.sampled_laplace_exact_1_factor`, `Pyramids.sampled_laplace_exact_1_hemigroup`, `Pyramids.sampled_laplace_exact_1_recursion`, `Pyramids.sampled_laplace_exact_1_powers`, `Pyramids.subsampling_sampled_laplace`, `Pyramids.sampled_laplace_exact_2_array`, `Pyramids.sampled_laplace_exact_2_restriction`, `Pyramids.sampled_laplace_exact_2_first`, `Pyramids.sampled_laplace_exact_2_later`, `Pyramids.sampled_laplace_exact_3` |
| `def:family-dimension-d (03)` | `Pyramids.IsLawHemigroup`, `Pyramids.IsNondegenerateLaws`, `Pyramids.IsFamily`, `Pyramids.IsSymmetricLaws`, `Pyramids.IsSymmetricFamily`, `Pyramids.IsRotationInvariantLaws`, `Pyramids.IsIsotropicFamily`, `Pyramids.IsCovariantAt`, `Pyramids.IsLamCovariant` |
| `lem:isotropic-symmetric (03)` | `Pyramids.isotropicFamily_isSymmetricFamily` |
| `lem:steps-infinitely-divisible (03)` | `Pyramids.isLawHemigroup_infinitelyDivisible` |
| `lem:symmetric-levy-khintchine (03)` | `Pyramids.symmetric_levy_khintchine` |
| `lem:family-structure (03)` | `Pyramids.family_structure_id`, `Pyramids.family_structure_exists`, `Pyramids.family_structure_data`, `Pyramids.family_structure_monotone`, `Pyramids.family_structure_isotropic` |
| `lem:family-dilations (03)` | `Pyramids.family_dilations_1`, `Pyramids.family_dilations_2`, `Pyramids.family_dilations_3_exists`, `Pyramids.family_dilations_3_relabel`, `Pyramids.family_dilations_3_unique`, `Pyramids.family_dilations_4` |
| `def:knots-and-ladder (03)` | `Pyramids.knotKernel`, `Pyramids.ladder` |
| `lem:lattice-infinitely-divisible (03)` | `Pyramids.lattice_infinitely_divisible` |
| `lem:discrete-covariance-levy (03)` | `Pyramids.discrete_covariance_levy`, `Pyramids.discrete_covariance_levy_semi`, `Pyramids.discrete_covariance_levy_determined` |
| `lem:synthesis (03)` | `Pyramids.synthesis` |
| `def:strata (03)` | `Pyramids.IsFullyCovariantLaws` |
| `thm:lattice-strata (03)` | `Pyramids.lattice_strata_1`, `Pyramids.lattice_strata_1_converse`, `Pyramids.lattice_strata_2`, `Pyramids.lattice_strata_3` |
| `prop:stratum-one-example (03)` | `Pyramids.stratum_one_example_data`, `Pyramids.stratum_one_example` |
| `prop:stratum-two-example (03)` | `Pyramids.stratum_two_example_data`, `Pyramids.stratum_two_example` |
| `thm:lattice-strata-strict (03)` | `Pyramids.lattice_strata_strict_imp`, `Pyramids.lattice_strata_strict`, `Pyramids.lattice_strata_strict_canonical` |
| `lem:reduction-keeps-stratum (03)` | `Pyramids.reduction_keeps_stratum` |
| `prop:what-does-not-lift (03)` | `Pyramids.what_does_not_lift`, `Pyramids.what_does_not_lift_atom` |
| `prop:what-does-not-lift-chain (03)` | `Pyramids.what_does_not_lift_chain_1`, `Pyramids.what_does_not_lift_chain_2`, `Pyramids.what_does_not_lift_chain_strict` |
| `prop:no-lattice-kernel (03)` | `Pyramids.no_lattice_kernel` |
| `prop:ladder-knot-kernel (03)` | `Pyramids.ladder_knot_kernel_1`, `Pyramids.ladder_knot_kernel_2_moments`, `Pyramids.ladder_knot_kernel_2`, `Pyramids.ladder_knot_kernel_2_not_unique`, `Pyramids.ladder_knot_kernel_2_unique_iff`, `Pyramids.ladder_knot_kernel_2_unique_iff_rot`, `Pyramids.ladder_knot_kernel_2_split`, `Pyramids.ladder_knot_kernel_2_split_rot`, `Pyramids.ladder_knot_kernel_3`, `Pyramids.ladder_knot_kernel_4a`, `Pyramids.ladder_knot_kernel_4b_equation`, `Pyramids.ladder_knot_kernel_4b_classA`, `Pyramids.ladder_knot_kernel_4b_family`, `Pyramids.ladder_knot_kernel_4c` |
| `prop:ladder-not-every-frequency (03)` | `Pyramids.ladder_not_every_frequency` |
| `prop:no-bounded-step (03)` | `Pyramids.no_bounded_step` |
| `prop:equivalent-weights (03)` | `Pyramids.equivalent_weights_1`, `Pyramids.equivalent_weights_2` |
| `def:matern-pyramid-data (04)` | `Pyramids.maternStep`, `Pyramids.maternExponent`, `Pyramids.besselProfile` |
| `lem:bessel-profile (04)` | `Pyramids.bessel_profile_1`, `Pyramids.bessel_profile_1_green`, `Pyramids.bessel_profile_2`, `Pyramids.bessel_profile_3`, `Pyramids.bessel_profile_3_closed` |
| `lem:bessel-k (04)` | `Pyramids.bessel_k_1`, `Pyramids.bessel_k_1_profile`, `Pyramids.bessel_k_2`, `Pyramids.bessel_k_3` |
| `thm:matern-pyramid (04)` | `Pyramids.matern_pyramid_5_limit_exists`, `Pyramids.matern_pyramid_1_admissible`, `Pyramids.matern_pyramid_1_exists`, `Pyramids.matern_pyramid_1_family`, `Pyramids.matern_pyramid_1_mixture`, `Pyramids.matern_pyramid_2_equation`, `Pyramids.matern_pyramid_2_family`, `Pyramids.matern_pyramid_3_marginal`, `Pyramids.matern_pyramid_3_polya`, `Pyramids.matern_pyramid_3_counts`, `Pyramids.matern_pyramid_4_series`, `Pyramids.matern_pyramid_4`, `Pyramids.matern_pyramid_5_limit`, `Pyramids.matern_pyramid_5_classA`, `Pyramids.matern_pyramid_5_multiples`, `Pyramids.matern_pyramid_5_weak`, `Pyramids.matern_pyramid_5_kernels` |
| `lem:cm-log-convex (04)` | `Pyramids.completelyMonotone_sub_shift`, `Pyramids.completelyMonotone_sq_le_mul` |
| `lem:cm-exponential-rate (04)` | `Pyramids.completelyMonotone_antitoneOn_exp_mul`, `Pyramids.not_isCompletelyMonotone_of_growth` |
| `lem:cm-uncancelled-atom (04)` | `Pyramids.not_isCompletelyMonotone_expDiff` |
| `prop:matern-increments (04)` | `Pyramids.matern_increments_1`, `Pyramids.matern_increments_2`, `Pyramids.matern_increments_2_levy_exists`, `Pyramids.matern_increments_2_poisson`, `Pyramids.matern_increments_3_levy_exists`, `Pyramids.matern_increments_3`, `Pyramids.matern_increments_3_thorin`, `Pyramids.matern_increments_3_sum` |
| `prop:thorin-in-dimension-d (04)` | `Pyramids.thorin_dimension_1`, `Pyramids.thorin_dimension_1_line`, `Pyramids.thorin_dimension_2_profile`, `Pyramids.thorin_dimension_2_low`, `Pyramids.thorin_dimension_2_high`, `Pyramids.thorin_dimension_2_profile_integrable` |
| `lem:no-first-order-factorization (04)` | `Pyramids.no_first_order_factorization`, `Pyramids.first_order_factorization_line` |
| `prop:matern-generator-octave (04)` | `Pyramids.matern_generator_octave_1_terms`, `Pyramids.matern_generator_octave_1_symbol`, `Pyramids.matern_generator_octave_1_size`, `Pyramids.matern_generator_octave_2`, `Pyramids.matern_generator_octave_3`, `Pyramids.matern_generator_octave_3_plane`, `Pyramids.matern_generator_octave_3_high`, `Pyramids.matern_generator_octave_3_periodization` |
| `prop:laplacian-pyramid (04)` | `Pyramids.laplacian_pyramid` |
| `def:frame-matern-pyramid (04)` | `Pyramids.IsFrameMaternPyramid` |
| `prop:frame-matern-pyramid-exists (04)` | `Pyramids.frame_matern_pyramid_exists` |
| `prop:creation-plane (04)` | `Pyramids.creation_plane_1`, `Pyramids.creation_plane_2`, `Pyramids.creation_plane_3`, `Pyramids.creation_plane_3_frame`, `Pyramids.creation_plane_4`, `Pyramids.creation_plane_5` |
| `prop:creation-grid (04)` | `Pyramids.creation_grid_1`, `Pyramids.creation_grid_2`, `Pyramids.creation_grid_3` |
| `def:implicit-euler-principle (04)` | `Pyramids.HasImplicitEulerPrinciple`, `Pyramids.IsNMax`, `Pyramids.IsNMin`, `Pyramids.HasGridImplicitEulerPrinciple` |
| `prop:stage-lemma (04)` | `Pyramids.stage_lemma_1`, `Pyramids.stage_lemma_1_helmholtz`, `Pyramids.stage_lemma_2`, `Pyramids.stage_lemma_3`, `Pyramids.stage_lemma_3_rotation` |
| `thm:selection-stratum-two (04)` | `Pyramids.selection_stratum_two_1`, `Pyramids.selection_stratum_two_1_ladder`, `Pyramids.selection_stratum_two_1_free`, `Pyramids.selection_stratum_two_2`, `Pyramids.selection_stratum_two_2_converse`, `Pyramids.selection_stratum_two_3`, `Pyramids.selection_stratum_two_4_gaussian`, `Pyramids.selection_stratum_two_4_frame`, `Pyramids.selection_stratum_two_4_axis`, `Pyramids.selection_stratum_two_2_converse_family`, `Pyramids.maternPyramid_gauge_family`, `Pyramids.selection_stratum_two_2_converse_gauge` |
| `prop:principle-other-readings (04)` | `Pyramids.principle_other_readings_1`, `Pyramids.principle_other_readings_2` |
| `prop:principle-after-decimation (04)` | `Pyramids.principle_after_decimation` |
| `def:grid-family (05)` | `Pyramids.IsStencilResolvent`, `Pyramids.stencilFamily`, `Pyramids.maskPowers` |
| `def:exact-senses (05)` | `Pyramids.IsExactLawArray`, `Pyramids.IsExactSampleArray`, `Pyramids.latticePt`, `Pyramids.IsExactSubsampleIn`, `Pyramids.IsExactLatticePyramid` |
| `def:exact-grid-pyramid (05)` | `Pyramids.IsLatticeMask`, `Pyramids.dilLadder`, `Pyramids.CarriesLatticeLadder`, `Pyramids.IsSORotationInvariant`, `Pyramids.IsIsotropicCarrier` |
| `lem:knot-data (05)` | `Pyramids.knot_kernel_data` |
| `prop:grid-pyramid-not-isotropic (05)` | `Pyramids.grid_pyramid_not_isotropic_union`, `Pyramids.grid_pyramid_not_isotropic_1`, `Pyramids.grid_pyramid_not_isotropic_2`, `Pyramids.grid_pyramid_not_isotropic_3` |
| `prop:expanding-grid-pyramid-not-isotropic (05)` | `Pyramids.matrix_grid_pyramid_not_isotropic` |
| `prop:grid-pyramid-singular-kernels (05)` | `Pyramids.grid_pyramid_singular_kernels_1`, `Pyramids.grid_pyramid_singular_kernels_2`, `Pyramids.grid_pyramid_singular_kernels_3` |
| `prop:grid-frame-step-not-selected (05)` | `Pyramids.grid_frame_step_not_selected_1`, `Pyramids.grid_frame_step_not_selected_2` |
| `prop:exact-masks (05)` | `Pyramids.exact_masks_1`, `Pyramids.exact_masks_1_poisson`, `Pyramids.exact_masks_2` |
| `prop:resolvent-masks-exact (05)` | `Pyramids.resolvent_masks_exact_1`, `Pyramids.resolvent_masks_exact_2`, `Pyramids.resolvent_masks_exact_3`, `Pyramids.resolvent_masks_exact_4_five`, `Pyramids.resolvent_masks_exact_4_nine`, `Pyramids.resolvent_masks_exact_4_general` |
| `def:level-records (05)` | `Pyramids.decimRecord` |
| `lem:records-creation (05)` | `Pyramids.records_creation` |
| `prop:creation-grid-masks (05)` | `Pyramids.zdLaw_tensorIdx_eq_tensorPow`, `Pyramids.creation_grid_masks_1`, `Pyramids.creation_grid_masks_2`, `Pyramids.creation_grid_masks_3_resolvent`, `Pyramids.creation_grid_masks_3_frame` |
| `prop:binomial-records (05)` | `Pyramids.binomial_records_1`, `Pyramids.binomial_records_2` |
| `prop:line-and-arrays (05)` | `Pyramids.line_and_arrays_1`, `Pyramids.line_and_arrays_2` |
| `prop:binomial-knot-relation (05)` | `Pyramids.binomial_knot_relation`, `Pyramids.binomial_knot_relation_tensor` |
| `prop:no-isotropic-refinable-finite-mask (05)` | `Pyramids.no_isotropic_refinable_mask_exp`, `Pyramids.no_isotropic_refinable_signed_finite_mask`, `Pyramids.no_isotropic_refinable_finite_mask` |
| `prop:band-limited-refinable-mask (05)` | `Pyramids.band_limited_density_exists`, `Pyramids.band_limited_refinable_mask_1`, `Pyramids.band_limited_refinable_mask_2`, `Pyramids.band_limited_refinable_mask_3` |
| `lem:cosine-bounds (05)` | `Pyramids.cosine_bounds` |
| `prop:discrete-helmholtz (05)` | `Pyramids.discrete_helmholtz_kernel`, `Pyramids.discrete_helmholtz_cascade`, `Pyramids.discrete_helmholtz_invariance`, `Pyramids.discrete_helmholtz_symbol`, `Pyramids.discrete_helmholtz_line`, `Pyramids.discrete_helmholtz_increment_translation` |
| `def:nine-point-laplacian (05)` | `Pyramids.gcos`, `Pyramids.fivePointSymbol`, `Pyramids.ninePointLap`, `Pyramids.ninePointSymbol`, `Pyramids.ninePointPhase` |
| `lem:nine-point-symbol (05)` | `Pyramids.nine_point_symbol` |
| `prop:nine-point-family (05)` | `Pyramids.nine_point_family_1`, `Pyramids.nine_point_family_2`, `Pyramids.nine_point_family_2_invariance` |
| `lem:line-exponent-data (A1)` | `Pyramids.line_exponent_data_1`, `Pyramids.line_exponent_data_1_converse`, `Pyramids.line_exponent_data_1_unique`, `Pyramids.line_exponent_data_2`, `Pyramids.line_exponent_data_3` |
| `lem:gauge-group (A1)` | `Pyramids.gauge_group_1`, `Pyramids.gauge_group_2`, `Pyramids.gauge_group_3`, `Pyramids.gauge_group_4` |
| `thm:annulus-parametrization (A1)` | `Pyramids.annulus_parametrization_map`, `Pyramids.annulus_parametrization_recover`, `Pyramids.annulus_parametrization_injective`, `Pyramids.annulus_parametrization_surjective` |
| `thm:annulus-parametrization-phase (A1)` | `Pyramids.annulus_phase_1`, `Pyramids.annulus_phase_1_converse`, `Pyramids.annulus_phase_2`, `Pyramids.annulus_phase_3` |
| `lem:averaging-bound (A1)` | `Pyramids.min_one_sq_le_avg`, `Pyramids.lintegral_min_one_sq_le`, `Pyramids.SymLevyPair_a_le_exponent_one`, `Pyramids.levy_integrable_of_cos_le` |
| `thm:surface-measure (A1)` | `Pyramids.surface_measure_family`, `Pyramids.surface_measure_unique`, `Pyramids.surface_measure_pair`, `Pyramids.surface_measure_injective`, `Pyramids.surface_measure_exponent`, `Pyramids.surface_measure_integrable_iff` |
| `lem:null-conull-point-mass (A1)` | `Pyramids.eq_smul_dirac_of_zero_one`, `Pyramids.eq_smul_dirac_prod_of_zero_one` |
| `thm:knot-atom-cascades (A1)` | `Pyramids.knot_atom_cascades_1_action`, `Pyramids.knot_atom_cascades_1_orbits`, `Pyramids.knot_atom_cascades_2_bij`, `Pyramids.knot_atom_cascades_2_integrable`, `Pyramids.knot_atom_cascades_2_gaussian`, `Pyramids.knot_atom_cascades_3`, `Pyramids.knot_atom_cascades_3_gaussian`, `Pyramids.knot_atom_cascades_4`, `Pyramids.knot_atom_cascades_4_gaussian`, `Pyramids.knot_atom_cascades_4_families` |
| `prop:strata-cylinder-coordinates (A1)` | `Pyramids.strata_cylinder_1_jump`, `Pyramids.strata_cylinder_1_then`, `Pyramids.strata_cylinder_1_integrability`, `Pyramids.strata_cylinder_1_gaussian`, `Pyramids.strata_cylinder_1_both`, `Pyramids.strata_cylinder_2`, `Pyramids.strata_cylinder_3` |
| `prop:strata-cylinder-coordinates-q-cin (A1)` | `Pyramids.qcin_1_cone`, `Pyramids.qcin_1_repr`, `Pyramids.qcin_1_range`, `Pyramids.qcin_1_rays`, `Pyramids.qcin_2`, `Pyramids.qcin_2_limit`, `Pyramids.qcin_3` |
| `lem:step-field-determines-family (A1)` | `Pyramids.step_field_1`, `Pyramids.step_field_2`, `Pyramids.step_field_2_knots` |
| `def:modulation-orbit (A1)` | `Pyramids.knotStep`, `Pyramids.IsKnotExponent`, `Pyramids.IsKnotLadder`, `Pyramids.IsStepMeasure`, `Pyramids.HasNoGaussianStep`, `Pyramids.modulationOrbit` |
| `lem:knot-exponent-ladder (A1)` | `Pyramids.knot_exponent_ladder_1`, `Pyramids.knot_exponent_ladder_1_determines`, `Pyramids.knot_exponent_ladder_2`, `Pyramids.knot_exponent_ladder_3` |
| `lem:member-gaussian-part (A1)` | `Pyramids.exists_step_gauss`, `Pyramids.gauss_eq_zero_of_noGaussianStep` |
| `lem:kl-measurable (A1)` | `Pyramids.measurable_klDiv_kernel` |
| `lem:phase-disintegration-exists (A1)` | `Pyramids.phase_disintegration_exists`, `Pyramids.exists_phaseDisintegration`, `Pyramids.phaseDisintegration_ae_eq` |
| `def:phase-entropy (A1)` | `Pyramids.haarPhase`, `Pyramids.rMarginal`, `Pyramids.IsPhaseDisintegration`, `Pyramids.phaseEntropy` |
| `prop:phase-entropy-scale-unit (A1)` | `Pyramids.phase_entropy_scale_unit` |
| `thm:phase-entropy-selection (A1)` | `Pyramids.phase_entropy_selection_1`, `Pyramids.phase_entropy_selection_2`, `Pyramids.phase_entropy_selection_3`, `Pyramids.phase_entropy_selection_4` |
| `lem:haar-smearing-density (A1)` | `Pyramids.map_haarPhase_prod_mul_apply`, `Pyramids.measurable_measure_Ioc_div` |
| `lem:haar-smearing-injective (A1)` | `Pyramids.haar_smearing_injective` |
| `prop:phase-entropy-ladder-bound (A1)` | `Pyramids.ladder_bound_1`, `Pyramids.ladder_bound_2`, `Pyramids.ladder_bound_3` |
| `thm:phase-entropy-modulated-selection (A1)` | `Pyramids.phase_entropy_modulated_selection`, `Pyramids.phase_entropy_modulated_selection_converse`, `Pyramids.phase_entropy_modulated_selection_iff` |
| `prop:modulated-selection-strict (A1)` | `Pyramids.modulated_selection_strict` |
| `prop:appearance-entropy (A1)` | `Pyramids.appearance_entropy_1`, `Pyramids.appearance_entropy_2`, `Pyramids.appearance_entropy_3`, `Pyramids.appearance_entropy_3_unique`, `Pyramids.appearance_entropy_4` |
| `prop:classical-kernels-no-exact-cascade (A1)` | `Pyramids.classical_kernels_no_exact_cascade`, `Pyramids.classical_kernels_no_exact_cascade_masks`, `Pyramids.classical_kernels_no_exact_cascade_burt`, `Pyramids.classical_kernels_no_exact_cascade_pyramid` |
| `lem:laplace-atoms-admissible (A1)` | `Pyramids.laplace_atoms_admissible_1`, `Pyramids.laplace_atoms_admissible_2` |
| `thm:matern-pyramid-line (A1)` | `Pyramids.matern_pyramid_line_display`, `Pyramids.matern_pyramid_line_1`, `Pyramids.matern_pyramid_line_2`, `Pyramids.matern_pyramid_line_2_direct`, `Pyramids.matern_pyramid_line_3`, `Pyramids.matern_pyramid_line_4_bound`, `Pyramids.matern_pyramid_line_4_limit`, `Pyramids.matern_pyramid_line_4_laws` |
| `thm:matern-pyramid-line-noncreation (A1)` | `Pyramids.matern_pyramid_line_noncreation` |
| `prop:ladder-non-creation-line (A1)` | `Pyramids.ladder_non_creation_line`, `Pyramids.ladder_non_creation_line_matern` |
| `prop:classical-pyramids-approximate (A1)` | `Pyramids.classical_pyramids_approximate_1`, `Pyramids.classical_pyramids_approximate_2`, `Pyramids.classical_pyramids_approximate_3`, `Pyramids.classical_pyramids_approximate_4`, `Pyramids.classical_pyramids_approximate_5` |
| `prop:classical-pyramids-approximate-discrete-gaussian (A1)` | `Pyramids.discrete_gaussian_neither` |
| `prop:extreme-rays-random-walks (A1)` | `Pyramids.extreme_rays_random_walks_1`, `Pyramids.extreme_rays_random_walks_2`, `Pyramids.extreme_rays_random_walks_3`, `Pyramids.extreme_rays_random_walks_4`, `Pyramids.extreme_rays_random_walks_5`, `Pyramids.extreme_rays_random_walks_5_finite` |

## Licence

Lean sources under Apache 2.0, text under CC BY 4.0 (`LICENSES/`).
