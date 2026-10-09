import DeletedPrimes

/-! Axiom check for the Lean names cited in `../paper/DeletedPrimes.tex` §9.3 and listed in `README.md`.
Run after `lake build`:  `lake env lean AxiomCheck.lean`.
Expected: every line reads `depends on axioms: [propext, Classical.choice, Quot.sound]`. -/

open DeletedPrimes

-- Definitions and basic facts (§1.1)
#print axioms theta2_le_theta
#print axioms theta_le_one
#print axioms isRegular_of_theta_lt
#print axioms isMSRegular_of_theta2_lt
#print axioms le_of_frequently_rpow_le
-- §5.1: Legendre's identity, Rankin's bound, θ ≤ α
#print axioms sum_divisors_muS
#print axioms count_eq_sum
#print axioms muS_mul_of_coprime
#print axioms muS_mul_of_not_coprime
#print axioms summable_units
#print axioms summable_muS_div
#print axioms density_eq_tprod
#print axioms rankin_count
#print axioms rankin_tail
#print axioms legendre
#print axioms abs_err_le_rankin
#print axioms theta_le_dim
-- §5: Lemma 5.2 and the frame arithmetic (Steps 3, 4, 6; Lemma 5.1)
#print axioms window_rigidity
#print axioms card_primes_dvd_le
#print axioms lt_pow_floor_log
#print axioms prod_injOn
#print axioms resonance_dvd
#print axioms sep_of_ne
#print axioms sep_of_pair_ne
#print axioms near_unique
#print axioms near_witness
-- §5: Lemma 5.3 (the exponent) and the properties of κ_k
#print axioms errExp_le_maxExp
#print axioms errExp_argmax
#print axioms maxExp_neg_iff
#print axioms errExp_neg_iff
#print axioms errExp_one
#print axioms kappaK_one
#print axioms kappaK_pos
#print axioms kappaK_lt_half
#print axioms kappaK_lt_one_sub
#print axioms boundary_neg
#print axioms hitExp_perturb
#print axioms kappaK_mono
#print axioms tendsto_kappaK
#print axioms floor_of_forall_k
#print axioms kappaOne_closed
#print axioms window_root
#print axioms counterexample_window
-- (5.4) and Proposition 4.1: dense blocks
#print axioms frequently_dense_block
#print axioms good_scale
#print axioms good_scales
#print axioms primeCount_ge
-- Theorem 6 and Corollaries 7, 8 (from Frame, Quantization, LandauAtOne)
#print axioms meanSq_lower_prime
#print axioms prime_floor
#print axioms meanSq_lower_composite
#print axioms composite_floor
#print axioms floor_theta2
#print axioms floor_theta
#print axioms counterexample_window_of_deletion
#print axioms dim_eq_zero_of_theta2
#print axioms dim_eq_zero_of_theta
-- Theorem 5 (last step)
#print axioms smooth_lower
#print axioms smooth_half_le
-- Theorem 1, Corollaries 3 and 4 (deductions), Propositions 7.2 and 7.3 (exponent arithmetic)
#print axioms moment_exponent
#print axioms moment_summable
#print axioms split_balance
#print axioms split_total
#print axioms ae_theta_le_of_forall
#print axioms ae_theta_eq
#print axioms isRegular_empty
#print axioms quarter_threshold
-- Corollary 3(3): the exponent arithmetic of the adjoined system
#print axioms hyperbola_exponent_lt
#print axioms hyperbola_exponent_mem
#print axioms hyperbola_y_mem
#print axioms hyperbola_balance
#print axioms cross_terms_cancel
#print axioms partial_summation_constant
#print axioms tail_coefficient
#print axioms hyperbola_tail_terms
#print axioms zero_shift_re_lt
#print axioms zero_double_shift_re_lt
#print axioms pole_mem_halfplane
#print axioms prime_term_dominates
#print axioms band_nonempty
#print axioms band_contains_BDR
#print axioms BDR_region_iff
#print axioms exact_exponent_of_two_terms
