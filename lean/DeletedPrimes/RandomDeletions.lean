import DeletedPrimes.Basic

/-!
# Random deletions: the deductions of Theorem 1 and Corollaries 3 and 4

The analytic and probabilistic arguments of §§6–7 (the chaos expansion, the moment bound, the Perron estimate under
RH, Kolmogorov's criterion) are not formalised; their outputs enter as hypotheses. Proved here:
- the convergence condition of Proposition 7.2: `∑_n n^{α−1−2b} < ∞` iff `α/2 < b` (`moment_summable`,
  `moment_exponent`);
- the balance `K = y^{1/2}` of Proposition 7.3 and the resulting bound (`split_balance`, `split_total`);
- the passage from "for every `β > β₀`, almost surely `O(x^β)`" to "almost surely `θ(S) ≤ β₀`"
  (`ae_theta_le_of_forall`), and Corollary 3(1) from Theorems 1 and 2 (`ae_theta_eq`);
- the empty deletion is regular at every exponent (`isRegular_empty`);
- Corollary 4, by the case split on RH (`quarter_threshold`), with Mathlib's `RiemannHypothesis`;
- the exponent arithmetic of Corollary 3(3), the `[α, β]`-systems obtained by adjoining the generalized primes
  `p^{1/β}`: the hyperbola exponent `β/(1+β−γ) < β` and its balance point (`hyperbola_exponent_lt`,
  `hyperbola_y_mem`, `hyperbola_balance`), the cancellation of the cross terms (`cross_terms_cancel`), the
  partial-summation constant (`partial_summation_constant`), the tail terms (`tail_coefficient`,
  `hyperbola_tail_terms`), the real parts of the shifted zeros under RH (`zero_shift_re_lt`,
  `zero_double_shift_re_lt`, `pole_mem_halfplane`), the prime term (`prime_term_dominates`), the band
  (`band_nonempty`, `band_contains_BDR`, `BDR_region_iff`), and the exactness of a two-term asymptotic
  (`exact_exponent_of_two_terms`).
-/

open Real Filter Topology MeasureTheory

namespace DeletedPrimes

noncomputable section

/-- Proposition 7.2: `α − 1 − 2b < −1 ↔ α/2 < b`. -/
theorem moment_exponent {α b : ℝ} : α - 1 - 2 * b < -1 ↔ α / 2 < b := by
  constructor <;> intro h <;> linarith

/-- Proposition 7.2: `∑_n n^{α−1−2b}` converges iff `α/2 < b`. -/
theorem moment_summable {α b : ℝ} :
    Summable (fun n : ℕ => (n : ℝ) ^ (α - 1 - 2 * b)) ↔ α / 2 < b := by
  rw [Real.summable_nat_rpow, moment_exponent]

/-- Proposition 7.3, step 4: with `K = y^{1/2}`, `K^α = y^{1/2} K^{α−1} = y^{α/2}`. -/
theorem split_balance {y α : ℝ} (hy : 0 < y) :
    (y ^ (1 / 2 : ℝ)) ^ α = y ^ (α / 2) ∧ y ^ (1 / 2 : ℝ) * (y ^ (1 / 2 : ℝ)) ^ (α - 1) = y ^ (α / 2) := by
  constructor
  · rw [← Real.rpow_mul hy.le]; ring_nf
  · rw [← Real.rpow_mul hy.le, ← Real.rpow_add hy]; ring_nf

/-- Proposition 7.3, step 4: `K^α + y^{1/2+4ε} K^{α−1} + y^{2ε} ≤ 3 y^{α/2+4ε}` for `K = y^{1/2}`, `y ≥ 1`. -/
theorem split_total {y α ε : ℝ} (hy : 1 ≤ y) (hα : 0 ≤ α) (hε : 0 ≤ ε) :
    (y ^ (1 / 2 : ℝ)) ^ α + y ^ (1 / 2 + 4 * ε) * (y ^ (1 / 2 : ℝ)) ^ (α - 1) + y ^ (2 * ε)
      ≤ 3 * y ^ (α / 2 + 4 * ε) := by
  have hy0 : 0 < y := by linarith
  have h1 : (y ^ (1 / 2 : ℝ)) ^ α = y ^ (α / 2) := by
    rw [← Real.rpow_mul hy0.le]; ring_nf
  have h2 : y ^ (1 / 2 + 4 * ε) * (y ^ (1 / 2 : ℝ)) ^ (α - 1) = y ^ (α / 2 + 4 * ε) := by
    rw [← Real.rpow_mul hy0.le, ← Real.rpow_add hy0]; ring_nf
  rw [h1, h2]
  have h3 : y ^ (α / 2) ≤ y ^ (α / 2 + 4 * ε) := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  have h4 : y ^ (2 * ε) ≤ y ^ (α / 2 + 4 * ε) := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  linarith

/-- Theorem 1 from Proposition 7.2: if for every `β > β₀` almost surely `N_S(x) = a_S x + O(x^β)`, then almost surely
`θ(S) ≤ β₀`. -/
theorem ae_theta_le_of_forall {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (S : Ω → Set ℕ) {β₀ : ℝ}
    (hβ₀ : 0 ≤ β₀) (h : ∀ β : ℝ, β₀ < β → ∀ᵐ ω ∂P, IsRegular (S ω) β) :
    ∀ᵐ ω ∂P, theta (S ω) ≤ β₀ := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, IsRegular (S ω) (β₀ + 1 / ((n : ℝ) + 1)) :=
    ae_all_iff.mpr fun n => h _ (by linarith [hpos n])
  filter_upwards [hall] with ω hω
  have hle : ∀ n : ℕ, theta (S ω) ≤ β₀ + 1 / ((n : ℝ) + 1) := fun n =>
    theta_le_of_isRegular (by linarith [hpos n]) (hω n)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  linarith [hle n]

/-- Corollary 3(1) from Theorems 1 and 2. -/
theorem ae_theta_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (S : Ω → Set ℕ) {α : ℝ}
    (hup : ∀ᵐ ω ∂P, theta (S ω) ≤ α / 2) (hlow : ∀ᵐ ω ∂P, α / 2 ≤ theta (S ω)) :
    ∀ᵐ ω ∂P, theta (S ω) = α / 2 := by
  filter_upwards [hup, hlow] with ω h1 h2
  exact le_antisymm h1 h2

/-- `N_∅(x) = ⌊x⌋`. -/
theorem count_empty {x : ℝ} : count ∅ x = ⌊x⌋₊ := by
  classical
  unfold count
  have hall : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, SFree ∅ n := fun n _ p hp => absurd hp (Set.notMem_empty p)
  rw [Finset.filter_true_of_mem hall]
  simp

/-- `μ_∅(d) = 0` for `d ≠ 1`. -/
theorem muS_empty_ne_one {d : ℕ} (hd : d ≠ 1) : muS ∅ d = 0 := by
  unfold muS
  rcases Nat.lt_or_ge d 2 with h | h
  · interval_cases d
    · simp
    · exact absurd rfl hd
  · obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < d)
    split_ifs with hall
    · exact absurd (hall p hp) (Set.notMem_empty p)
    · rfl

/-- `a_∅ = 1`. -/
theorem density_empty : density ∅ = 1 := by
  unfold density
  rw [tsum_eq_single 1]
  · simp [muS]
  · intro d hd
    rw [muS_empty_ne_one hd]; simp

/-- The empty deletion: `N_∅(x) = ⌊x⌋` and `a_∅ = 1`, so `|E(x)| ≤ 1`. -/
theorem isRegular_empty {θ : ℝ} (hθ : 0 ≤ θ) : IsRegular ∅ θ := by
  refine ⟨1, fun x hx => ?_⟩
  unfold err
  rw [count_empty, density_empty, one_mul]
  have hx0 : 0 ≤ x := by linarith
  have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have h3 : 1 ≤ x ^ θ := Real.one_le_rpow hx hθ
  rw [abs_le]
  constructor <;> linarith

/-- **Corollary 4.** For every `θ > 1/4` some deletion is `θ`-regular and its zeta function has a zero with real part
`> 1/2` (`ZeroRight S`). If RH fails, `S = ∅` works (`hnotRH`); if RH holds, the random deletions of Corollary 3 with
`1/2 < α < 2θ` work (`hRH`). -/
theorem quarter_threshold (ZeroRight : Set ℕ → Prop)
    (hnotRH : ¬ RiemannHypothesis → ZeroRight ∅)
    (hRH : RiemannHypothesis → ∀ α : ℝ, 1 / 2 < α → α < 1 → ∃ S : Set ℕ, theta S = α / 2 ∧ ZeroRight S) :
    ∀ θ : ℝ, 1 / 4 < θ → ∃ S : Set ℕ, IsRegular S θ ∧ ZeroRight S := by
  intro θ hθ
  by_cases hR : RiemannHypothesis
  · set m := min 1 (2 * θ) with hm
    have hm1 : m ≤ 1 := min_le_left _ _
    have hm2 : m ≤ 2 * θ := min_le_right _ _
    have hm3 : 1 / 2 < m := lt_min (by norm_num) (by linarith)
    obtain ⟨S, hS, hZ⟩ := hRH hR ((1 / 2 + m) / 2) (by linarith) (by linarith)
    refine ⟨S, isRegular_of_theta_lt ?_, hZ⟩
    rw [hS]; linarith
  · exact ⟨∅, isRegular_empty (by linarith), hnotRH hR⟩

/-! ### Corollary 3(3): the exponent arithmetic of the adjoined system

In the proof of Corollary 3(3) the integers of the system `P_β` are counted by the hyperbola method with
`N_S(x) = a x + O(x^γ)`, `α/2 < γ < β < 1/2`, and the parameter `y = x^{β/(1+β−γ)}`. The facts below are the
arithmetic of that proof. -/

/-- The hyperbola exponent `β/(1+β−γ)` is strictly below `β` when `0 < β` and `γ < β`. -/
theorem hyperbola_exponent_lt {β γ : ℝ} (hβ : 0 < β) (hγβ : γ < β) : β / (1 + β - γ) < β := by
  have hpos : 0 < 1 + β - γ := by linarith
  rw [div_lt_iff₀ hpos]
  nlinarith

/-- `0 < β/(1+β−γ) ≤ 1` for `0 ≤ γ < β ≤ 1`. -/
theorem hyperbola_exponent_mem {β γ : ℝ} (hγ0 : 0 ≤ γ) (hγβ : γ < β) (hβ1 : β ≤ 1) :
    0 < β / (1 + β - γ) ∧ β / (1 + β - γ) ≤ 1 := by
  have hpos : 0 < 1 + β - γ := by linarith
  refine ⟨div_pos (by linarith) hpos, ?_⟩
  rw [div_le_iff₀ hpos]
  linarith

/-- The hyperbola parameter `y = x^{β/(1+β−γ)}` lies in `[1, x]` for `x ≥ 1`. -/
theorem hyperbola_y_mem {β γ x : ℝ} (hγ0 : 0 ≤ γ) (hγβ : γ < β) (hβ1 : β ≤ 1) (hx : 1 ≤ x) :
    1 ≤ x ^ (β / (1 + β - γ)) ∧ x ^ (β / (1 + β - γ)) ≤ x := by
  obtain ⟨h0, h1⟩ := hyperbola_exponent_mem hγ0 hγβ hβ1
  refine ⟨Real.one_le_rpow hx h0.le, ?_⟩
  calc x ^ (β / (1 + β - γ)) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx h1
    _ = x := Real.rpow_one x

/-- At `y = x^{β/(1+β−γ)}` the two error terms `x^β y^{γ−β}` and `y` coincide. -/
theorem hyperbola_balance {β γ x : ℝ} (hx : 0 < x) (hγβ : γ < β) :
    x ^ β * (x ^ (β / (1 + β - γ))) ^ (γ - β) = x ^ (β / (1 + β - γ)) := by
  have hne : 1 + β - γ ≠ 0 := by linarith
  rw [← Real.rpow_mul hx.le, ← Real.rpow_add hx]
  congr 1
  field_simp
  ring

/-- The three cross terms in `a x^β y^{1−β}` cancel: `1/(1−β) − β/(1−β) − 1 = 0`. -/
theorem cross_terms_cancel {a β : ℝ} (hβ : β ≠ 1) : a / (1 - β) - a * β / (1 - β) - a = 0 := by
  have h : (1 : ℝ) - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  field_simp
  ring

/-- Partial summation: with `Y = y^{1−β}`, `a Y + aβ(Y − 1)/(1−β) = a Y/(1−β) + aβ/(β−1)`; the constant
`aβ/(β−1)` is the first term of `ζ_S(β)` in (2.1). -/
theorem partial_summation_constant {a β Y : ℝ} (hβ : β ≠ 1) :
    a * Y + a * β * (Y - 1) / (1 - β) = a * Y / (1 - β) + a * β / (β - 1) := by
  have h1 : (1 : ℝ) - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  have h2 : β - 1 ≠ 0 := sub_ne_zero.mpr hβ
  field_simp
  ring

/-- The tail of `ζ(1/β)`: `1/(1/β − 1) = β/(1−β)`. -/
theorem tail_coefficient {β : ℝ} (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) : 1 / (1 / β - 1) = β / (1 - β) := by
  have h : (1 : ℝ) - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ1)
  rw [show 1 / β - 1 = (1 - β) / β by field_simp, one_div_div]

/-- With `L = (x/y)^β`: `x L^{1−1/β} = x^β y^{1−β}`, `x L^{−1/β} = y`, `x^γ L^{1−γ/β} = x^β y^{γ−β}`,
`y L = x^β y^{1−β}` and `y^γ L = x^β y^{γ−β}`. -/
theorem hyperbola_tail_terms {x y β γ : ℝ} (hx : 0 < x) (hy : 0 < y) (hβ : 0 < β) :
    x * ((x / y) ^ β) ^ (1 - 1 / β) = x ^ β * y ^ (1 - β) ∧
    x * ((x / y) ^ β) ^ (-(1 / β)) = y ∧
    x ^ γ * ((x / y) ^ β) ^ (1 - γ / β) = x ^ β * y ^ (γ - β) ∧
    y * (x / y) ^ β = x ^ β * y ^ (1 - β) ∧
    y ^ γ * (x / y) ^ β = x ^ β * y ^ (γ - β) := by
  have hxy : 0 ≤ x / y := (div_pos hx hy).le
  have hβ0 : β ≠ 0 := hβ.ne'
  have hL : ∀ z : ℝ, ((x / y) ^ β) ^ z = x ^ (β * z) * y ^ (-(β * z)) := by
    intro z
    rw [← Real.rpow_mul hxy, Real.div_rpow hx.le hy.le, div_eq_mul_inv, ← Real.rpow_neg hy.le]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hL, show β * (1 - 1 / β) = β - 1 by field_simp, show -(β - 1) = 1 - β by ring,
      Real.rpow_sub_one hx.ne']
    field_simp
  · rw [hL, show β * (-(1 / β)) = -1 by field_simp, neg_neg, Real.rpow_neg_one, Real.rpow_one]
    field_simp
  · rw [hL, show β * (1 - γ / β) = β - γ by field_simp, show -(β - γ) = γ - β by ring,
      ← mul_assoc, ← Real.rpow_add hx]; ring_nf
  · rw [Real.div_rpow hx.le hy.le, div_eq_mul_inv, ← Real.rpow_neg hy.le,
      show (1 : ℝ) - β = -β + 1 by ring, Real.rpow_add hy, Real.rpow_one]
    ring
  · rw [Real.div_rpow hx.le hy.le, div_eq_mul_inv, ← Real.rpow_neg hy.le,
      show γ - β = γ + -β by ring, Real.rpow_add hy]
    ring

/-- Under RH a zero `ρ` of `ζ` has `Re ρ ≤ 1/2`; the corresponding zero `s = ρ − 1 + α` of `ζ(s+1−α)` has
`Re s < α/2` when `α < 1`. -/
theorem zero_shift_re_lt {α : ℝ} {s ρ : ℂ} (hα1 : α < 1) (hρ : ρ.re ≤ 1 / 2) (h : s + 1 - α = ρ) :
    s.re < α / 2 := by
  have := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re] at this
  linarith

/-- The zero `s = (ρ − 1 + α)/2` of `ζ(2s+1−α)` has `Re s < α/2` whenever `Re ρ ≤ 1/2`. -/
theorem zero_double_shift_re_lt {α : ℝ} {s ρ : ℂ} (hρ : ρ.re ≤ 1 / 2) (h : 2 * s + 1 - α = ρ) :
    s.re < α / 2 := by
  have := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at this
  linarith

/-- The pole `s = α` of `ζ(s+1−α)` lies in `Re s > α/2` when `α > 0`. -/
theorem pole_mem_halfplane {α : ℝ} (hα0 : 0 < α) : α / 2 < α := by linarith

/-- The prime term: for `β < 1/2 < α` and `x ≥ 1`, `x^β ≤ x^α` and `x^{1/2} ≤ x^α`. -/
theorem prime_term_dominates {α β x : ℝ} (hβ : β < 1 / 2) (hα : 1 / 2 < α) (hx : 1 ≤ x) :
    x ^ β ≤ x ^ α ∧ x ^ (1 / 2 : ℝ) ≤ x ^ α :=
  ⟨Real.rpow_le_rpow_of_exponent_le hx (by linarith), Real.rpow_le_rpow_of_exponent_le hx hα.le⟩

/-- The band `α/2 ≤ β < 1/2` is nonempty for `α < 1`. -/
theorem band_nonempty {α : ℝ} (hα1 : α < 1) : α / 2 < 1 / 2 := by linarith

/-- The band contains the region of [BDR]: `α/2 < 2α/(α+2)` for `0 < α < 2`. -/
theorem band_contains_BDR {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) : α / 2 < 2 * α / (α + 2) := by
  rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
  nlinarith

/-- The region of [BDR] is nonempty, `2α/(α+2) < 1/2`, exactly when `α < 2/3`. -/
theorem BDR_region_iff {α : ℝ} (hα0 : 0 < α) : 2 * α / (α + 2) < 1 / 2 ↔ α < 2 / 3 := by
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- A two-term asymptotic `f(x) = a x + c x^β + O(x^{β'})` with `c ≠ 0` and `β' < β` has exponent exactly `β`:
`f(x) − a x = O(x^β)`, and `f(x) − a x` is not `O(x^θ)` for any `θ < β`. This is the "for every `ε > 0` and for no
`ε < 0`" step for the integers of `P_β`. -/
theorem exact_exponent_of_two_terms {f : ℝ → ℝ} {a c β β' C : ℝ} (hc : c ≠ 0) (hβ' : β' < β)
    (h : ∀ x : ℝ, 1 ≤ x → |f x - a * x - c * x ^ β| ≤ C * x ^ β') :
    (∃ C' : ℝ, ∀ x : ℝ, 1 ≤ x → |f x - a * x| ≤ C' * x ^ β) ∧
    ∀ θ : ℝ, θ < β → ¬ ∃ C' : ℝ, ∀ x : ℝ, 1 ≤ x → |f x - a * x| ≤ C' * x ^ θ := by
  have hC : 0 ≤ C := by
    have := h 1 le_rfl
    simp only [Real.one_rpow, mul_one] at this
    exact le_trans (abs_nonneg _) this
  refine ⟨⟨|c| + C, fun x hx => ?_⟩, fun θ hθ ⟨C', hC'⟩ => ?_⟩
  · have h1 := h x hx
    have h2 : x ^ β' ≤ x ^ β := Real.rpow_le_rpow_of_exponent_le hx hβ'.le
    have h3 : 0 ≤ x ^ β := by positivity
    have e : |f x - a * x| = |(f x - a * x - c * x ^ β) + c * x ^ β| := by congr 1; ring
    rw [e]
    calc |(f x - a * x - c * x ^ β) + c * x ^ β|
        ≤ |f x - a * x - c * x ^ β| + |c * x ^ β| := by
          have h7 := abs_sub (f x - a * x - c * x ^ β) (-(c * x ^ β))
          rwa [sub_neg_eq_add, abs_neg] at h7
      _ ≤ C * x ^ β' + |c| * x ^ β := by rw [abs_mul, abs_of_nonneg h3]; linarith
      _ ≤ (|c| + C) * x ^ β := by nlinarith
  · set m := max θ β' with hm
    have hmβ : m < β := max_lt hθ hβ'
    have hfreq : ∃ᶠ X in atTop, |c| * X ^ β ≤ (|C'| + C) * X ^ m := by
      refine Filter.Eventually.frequently ?_
      filter_upwards [eventually_ge_atTop 1] with x hx
      have h1 := h x hx
      have h2 := hC' x hx
      have h3 : 0 ≤ x ^ β := by positivity
      have hθm : x ^ θ ≤ x ^ m := Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
      have hβ'm : x ^ β' ≤ x ^ m := Real.rpow_le_rpow_of_exponent_le hx (le_max_right _ _)
      have hxθ : 0 ≤ x ^ θ := by positivity
      have e : |c| * x ^ β = |c * x ^ β| := by rw [abs_mul, abs_of_nonneg h3]
      have htri : |c * x ^ β| ≤ |f x - a * x| + |f x - a * x - c * x ^ β| := by
        have h6 := abs_sub (f x - a * x) (f x - a * x - c * x ^ β)
        rwa [show f x - a * x - (f x - a * x - c * x ^ β) = c * x ^ β by ring] at h6
      have h4 : C' * x ^ θ ≤ |C'| * x ^ m :=
        calc C' * x ^ θ ≤ |C'| * x ^ θ := mul_le_mul_of_nonneg_right (le_abs_self _) hxθ
          _ ≤ |C'| * x ^ m := mul_le_mul_of_nonneg_left hθm (abs_nonneg _)
      have h5 : C * x ^ β' ≤ C * x ^ m := mul_le_mul_of_nonneg_left hβ'm hC
      rw [e]
      linarith
    have := le_of_frequently_rpow_le (abs_pos.mpr hc) hfreq
    linarith

end

end DeletedPrimes
