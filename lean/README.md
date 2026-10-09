# Lean library `DeletedPrimes`

The formal companion to `../paper/DeletedPrimes.tex` (version 3). It is written in Lean 4 (`v4.35.0-rc3`) with
Mathlib at the matching tag.

## Build and check

These commands run from this folder.

```bash
lake exe cache get
```

```bash
lake build
```

```bash
lake env lean AxiomCheck.lean
```

- `lake exe cache get` downloads a compiled Mathlib (several GB). Skip it if `.lake/packages` is already present.
- `lake build` checks the eight modules.
- `AxiomCheck.lean` prints the axioms of the 82 names that the paper relies on (§9.3 of the paper and the table
  below).

**Checked on 2026-10-09:**
- `lake build` finished with no errors and no warnings.
- `AxiomCheck.lean` reported all 82 names as `depends on axioms: [propext, Classical.choice, Quot.sound]`.
- The sources contain no `sorry`, `admit`, `native_decide` or `axiom`.

## Files

| File | Content |
|---|---|
| `DeletedPrimes/Basic.lean` | the definitions; `θ₂ ≤ θ ≤ 1`; comparison of power laws |
| `DeletedPrimes/Legendre.lean` | `1_{𝒩_S} = 1 ∗ μ_S`, Legendre's identity (5.1), Rankin's bounds, `a_S = ∏(1 − 1/p)`, `θ(S) ≤ α(S)` (§5.1) |
| `DeletedPrimes/Rigidity.lean` | Lemma 5.2 (composite window rigidity) and the arithmetic of Steps 3, 4, 6 and Lemma 5.1 |
| `DeletedPrimes/Exponents.lean` | Lemma 5.3 and the properties of `κ_k(α)`; the arithmetic of Corollary 7 |
| `DeletedPrimes/GoodScales.lean` | the dense blocks (5.4) and Proposition 4.1 |
| `DeletedPrimes/CompositeFloor.lean` | Theorem 6 and Corollaries 7 and 8, from the named hypotheses below |
| `DeletedPrimes/Smooth.lean` | Theorem 5: the lower count from a smooth `π_S`, and the last step |
| `DeletedPrimes/RandomDeletions.lean` | Theorem 1 and Corollaries 3 and 4 as deductions; the exponents of Propositions 7.2 and 7.3; the exponent arithmetic of Corollary 3(3) |
| `DeletedPrimes.lean` | imports everything |
| `AxiomCheck.lean` | `#print axioms` for the 82 cited names |

## Definitions

Every definition is for an arbitrary `S : Set ℕ`. Hypotheses such as "`S` is a set of primes" are added only where a
proof uses them.

| Paper | Lean |
|---|---|
| `N_S(x)` | `count S x` |
| `μ_S(d)` | `muS S d` |
| `a_S = ∑_d μ_S(d)/d` | `density S` (and `density_eq_tprod` gives `= ∏_{p∈S}(1 − 1/p)`) |
| `E(x) = N_S(x) − a_S x` | `err S x` |
| `b(u) = {u} − 1/2` | `saw u` |
| `α(S)` | `dim S`: `sInf {σ ≥ 0 : ∑_{p∈S} p^{−σ} < ∞}` |
| `θ(S)` | `theta S`: `sInf {θ ≥ 0 : ∃ C, ∀ x ≥ 1, |E(x)| ≤ C x^θ}` |
| `X⁻¹∫_X^{2X} E²` | `meanSq S X` |
| `θ₂(S)` | `theta2 S`: `sInf {θ ≥ 0 : ∃ C, ∀ X ≥ 1, meanSq S X ≤ C X^{2θ}}` |
| `κ_k(α)`, `κ_1(α)` | `kappaK k α`, `kappaOne α` |
| `f_k(τ)`, `h_k(τ)` (Lemma 5.3) | `errExp k α κ τ`, `hitExp k α κ τ` |
| `#(S ∩ [Y, 2Y))`, `π_S(x)` | `blockCount S Y`, `primeCount S x` (also `piS S x` in `Smooth.lean`) |

## What is proved outright, and what enters as a hypothesis

**Proved outright** (no hypothesis beyond the statement):
- Legendre's identity and Rankin's bounds.
- `θ(S) ≤ α(S)` and `θ₂(S) ≤ θ(S)`.
- Lemmas 5.2 and 5.3, and the arithmetic of the frame.
- The properties of `κ_k`.
- Proposition 4.1, from a Mertens law.
- The dense blocks (5.4).
- The lower count in Theorem 5.
- The exponent conditions of Propositions 7.2 and 7.3.
- The exponent arithmetic of Corollary 3(3): the hyperbola exponent and its balance point, the cancellation of the
  cross terms, the partial-summation constant, the tail terms, the real parts of the shifted zeros under RH, the
  band and its containment of the region of [BDR], and the exactness of a two-term asymptotic.

**Named analytic hypotheses** (`CompositeFloor.lean`):
- `Frame S`: Steps 1–7 of §5, in the form of (5.10). Take `k ≥ 1` and a level `κ` with `κ < 1/2`, `κ < 1 − α`, and
  every error exponent `errExp k α κ τ ≤ −μ < 0`. Then there are a share tolerance `δ > 0` and a range `η < η₀` with
  the following property. Every configuration of `k` increasing dense dyadic blocks with `#T_i ≥ (2^{j_i})^{α−η}`,
  shares `log 2^{j_i}/log Y` within `δ` of `1/k`, and `Y = ∏ 2^{j_i}` large has mean square `≥ c ∏ #T_i` at
  `X = Y^{1/κ}`. This is what §5.4 proves.
- `Quantization S`: Theorem 9. If `θ₂ < α`, the Mertens law holds with an integer `m ≥ 1`. Its proof uses Landau's
  and Karamata's theorems.
- `LandauAtOne S`: the first part of Corollary 8. `θ₂ < 1` forces `α < 1`, by Landau's theorem at `s = 1`.

**Theorem-local hypotheses:**
- Theorem 5: `hcount` is the count bound (1.3), whose proof uses Plancherel and Lemmas 3.1–3.3.
- Theorem 1: `ae_theta_le_of_forall` takes the output of Propositions 7.2 and 7.3 ("for every `β > α/2`, almost
  surely `O(x^β)`").
- Corollary 3(1): Theorems 1 and 2 are hypotheses.
- Corollary 4: `hnotRH` (if RH fails, `ζ` has a zero right of the critical line) and `hRH` (Corollary 3 under RH) are
  hypotheses. `RiemannHypothesis` is Mathlib's.

**Not formalised:**
- The Fourier analysis of Steps 1–7.
- Landau's and Karamata's theorems.
- Plancherel's identity and Lemmas 3.1–3.3.
- The contour shifts and the bounds for `ζ`.
- The probabilistic arguments of §§6–7: Kolmogorov, Borel–Cantelli, Fatou, the chaos expansion and the moment bound.
- Proposition 2.2.
- Corollary 3(2) and (3), the `[α, α/2]`- and `[α, β]`-systems themselves. The library has no Beurling systems (no `ψ`
  or `N` of a system of generalized primes), and the hyperbola computation of §8 and the nonvanishing of `ζ_S(β)` for
  `α/2 < β < 1/2`, which rests on the continuation of Lemma 6.2, are not checked; only their arithmetic is (above).

## Paper → Lean

| Paper | Lean name(s) | Kind |
|---|---|---|
| §1.1: `θ₂ ≤ θ ≤ 1`; exponents above `θ`, `θ₂` admissible | `theta2_le_theta`, `theta_le_one`, `isRegular_of_theta_lt`, `isMSRegular_of_theta2_lt` | proved |
| comparing power laws (used throughout) | `le_of_frequently_rpow_le` | proved |
| §2.1: `1_{𝒩_S} = ∑_{d∣n} μ_S(d)`; `a_S = ∏(1 − 1/p)` | `sum_divisors_muS`, `density_eq_tprod` | proved |
| (5.1) Legendre's identity | `count_eq_sum`, `legendre` | proved |
| (5.2) Rankin's bounds (count of `𝒟_S`, tail) | `summable_units`, `summable_muS_div`, `rankin_count`, `rankin_tail` | proved |
| §5.1: `|E(x)| ≤ 2K x^σ`, `θ(S) ≤ α(S)` | `abs_err_le_rankin`, `theta_le_dim` | proved |
| Step 5: `μ_S(qd') = μ_S(q)μ_S(d')`, `qd' ∉ 𝒟` otherwise | `muS_mul_of_coprime`, `muS_mul_of_not_coprime` | proved |
| Step 3: exact resonance forces `q ∣ d`; separation `1/(dq)` | `resonance_dvd`, `sep_of_ne` | proved |
| Lemma 5.1: one near `ℓ`; nonzero witness `j` | `near_unique`, `near_witness` | proved |
| Lemma 5.2 (composite window rigidity) | `window_rigidity`, with `card_primes_dvd_le`, `lt_pow_floor_log`, `prod_injOn` | proved |
| Step 6: distinct `m/q` are `1/(qq')`-separated | `sep_of_pair_ne` | proved |
| Lemma 5.3: maximum of `f_k`, attained; negative iff `κ < κ_k` | `errExp_le_maxExp`, `errExp_argmax`, `maxExp_neg_iff`, `errExp_neg_iff`; `errExp_one`, `kappaK_one` (`k = 1`) | proved |
| §5.2: `κ_k < min(1/2, 1−α)`; `κ_k > 0` | `kappaK_lt_half`, `kappaK_lt_one_sub`, `kappaK_pos` | proved |
| Step 5: the `+1` term on `(κ, κ+η]`; unequal blocks cost `(1+α)κδ` | `boundary_neg`, `hitExp_perturb` | proved |
| `κ_k ↑ min(1/2, 1−α)`; the floor from all `k` | `kappaK_mono`, `tendsto_kappaK`, `floor_of_forall_k` | proved |
| `ακ_1/2 = α(1−α)/(2(1+(1−α)²))` | `kappaOne_closed` | proved |
| (5.4) dense blocks below the dimension | `frequently_dense_block` | proved |
| Proposition 4.1(1), (2), (3) | `good_scale`, `good_scales`, `primeCount_ge` | proved (from the Mertens law) |
| Theorem 6(1); prime floor | `meanSq_lower_prime`, `prime_floor` | from `Frame` |
| Theorem 6(2) | `meanSq_lower_composite`, `composite_floor` | from `Frame`, `Quantization` |
| Theorem 6(3) | `floor_theta2`, `floor_theta` | from `Frame`, `Quantization` |
| Corollary 7 | `counterexample_window` (arithmetic), `window_root`; `counterexample_window_of_deletion` | proved; from `Frame`, `Quantization`, `LandauAtOne` |
| Corollary 8 | `dim_eq_zero_of_theta2`, `dim_eq_zero_of_theta` | from `Frame`, `Quantization`, `LandauAtOne` |
| Theorem 5: `#(S ∩ (X,2X]) ≫ X^α/log X`; `θ ≥ α/2` | `smooth_lower`; `smooth_half_le` | proved; from (1.3) |
| Proposition 7.2: convergence condition | `moment_exponent`, `moment_summable` | proved |
| Proposition 7.3: the balance `K = y^{1/2}` | `split_balance`, `split_total` | proved |
| Theorem 1 from Propositions 7.2–7.3 | `ae_theta_le_of_forall` | deduction |
| Corollary 3(1) | `ae_theta_eq` | deduction |
| Corollary 3(3), arithmetic: hyperbola exponent `β/(1+β−γ) < β`, `y ∈ [1, x]`, balance of the error terms | `hyperbola_exponent_lt`, `hyperbola_exponent_mem`, `hyperbola_y_mem`, `hyperbola_balance` | proved |
| Corollary 3(3), arithmetic: cross terms, partial-summation constant, tail terms | `cross_terms_cancel`, `partial_summation_constant`, `tail_coefficient`, `hyperbola_tail_terms` | proved |
| Corollary 3(3), arithmetic: real parts of the shifted zeros and pole under RH; the prime term | `zero_shift_re_lt`, `zero_double_shift_re_lt`, `pole_mem_halfplane`, `prime_term_dominates` | proved |
| Corollary 3(3), arithmetic: the band `α/2 ≤ β < 1/2` and the region of [BDR] | `band_nonempty`, `band_contains_BDR`, `BDR_region_iff` | proved |
| Corollary 3(3): a two-term asymptotic `ax + cx^β + O(x^{β'})`, `c ≠ 0`, has exponent exactly `β` | `exact_exponent_of_two_terms` | proved |
| Corollary 3(2), (3): the `[α, α/2]`- and `[α, β]`-systems themselves | — | not formalised |
| Corollary 4 | `isRegular_empty`, `quarter_threshold` | deduction (case split on `RiemannHypothesis`) |

## History

This library replaces the six corpus files that version 2 cited. Those were `SawtoothNoise`, `PowerRegular`,
`MeanSquareN0`, `WindowN0`, `EnergyN0` and `QuantizationN0`; they are not included in this repository. They checked the exponent
arithmetic of version 2, including Theorems 6 and 9, which version 3 drops. They took the analytic theorems as
hypotheses over an abstract type of systems. This library instead works with concrete definitions of `N_S`, `α(S)`,
`θ(S)` and `θ₂(S)`. It also proves Legendre's identity, Rankin's bounds, `θ ≤ α`, Lemma 5.2, Lemma 5.3 for every `k`
and the good-scales selection.
