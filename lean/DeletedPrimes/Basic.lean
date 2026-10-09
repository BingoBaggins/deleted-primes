import Mathlib

/-!
# Deleting primes from the integers: definitions

The objects of the paper, defined concretely for a set `S ⊆ ℕ` (in the paper `S` is a set of primes with
`∑_{p∈S} 1/p < ∞`; the definitions make sense for every `S`, and the hypotheses are added where they are used).

| Paper | Lean |
|---|---|
| `n` has no prime factor in `S` | `SFree S n` |
| `N_S(x) = #{n ≤ x : n ∈ 𝒩_S}` | `count S x` |
| `μ_S(d)` | `muS S d` |
| `a_S = ∑_d μ_S(d)/d` | `density S` |
| `E(x) = N_S(x) − a_S x` | `err S x` |
| `b(u) = {u} − 1/2` | `saw u` |
| `α(S)`, the abscissa of convergence of `∑_{p∈S} p^{−σ}` | `dim S` |
| `θ(S)`, the integer exponent | `theta S` |
| `X⁻¹∫_X^{2X} E(x)² dx` | `meanSq S X` |
| `θ₂(S)`, the mean-square exponent | `theta2 S` |

Basic facts proved here: `θ(S), θ₂(S) ∈ [0, 1]`, `θ₂(S) ≤ θ(S)`, the regularity bounds hold at every exponent above
`θ(S)` (resp. `θ₂(S)`), and the comparison of power laws used in every deduction of the paper
(`le_of_frequently_rpow_le`).
-/

open Real Filter Topology MeasureTheory

namespace DeletedPrimes

noncomputable section

open Classical

/-- `n` is `S`-free: no element of `S` divides `n`. -/
def SFree (S : Set ℕ) (n : ℕ) : Prop := ∀ p ∈ S, ¬ p ∣ n

/-- `N_S(x)`: the number of `S`-free integers in `[1, x]`. -/
def count (S : Set ℕ) (x : ℝ) : ℕ := ((Finset.Icc 1 ⌊x⌋₊).filter (SFree S)).card

/-- `μ_S(d)`: the Möbius function at `d` if every prime factor of `d` lies in `S`, and `0` otherwise. -/
def muS (S : Set ℕ) (d : ℕ) : ℤ :=
  if ∀ p ∈ d.primeFactors, p ∈ S then ArithmeticFunction.moebius d else 0

/-- `a_S = ∑_d μ_S(d)/d`, the density of the `S`-free integers. -/
def density (S : Set ℕ) : ℝ := ∑' d : ℕ, (muS S d : ℝ) / d

/-- `E(x) = N_S(x) − a_S x`. -/
def err (S : Set ℕ) (x : ℝ) : ℝ := (count S x : ℝ) - density S * x

/-- The sawtooth function `b(u) = {u} − 1/2`. -/
def saw (u : ℝ) : ℝ := Int.fract u - 1 / 2

/-- `α(S)`: the abscissa of convergence of `∑_{p∈S} p^{−σ}`, taken in `[0, ∞)` (so `α(S) = 0` for finite `S`). -/
def dim (S : Set ℕ) : ℝ :=
  sInf {σ : ℝ | 0 ≤ σ ∧ Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-σ))}

/-- `N_S(x) = a_S x + O(x^θ)` on `x ≥ 1`. -/
def IsRegular (S : Set ℕ) (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |err S x| ≤ C * x ^ θ

/-- `θ(S)`: the infimum of the `θ ≥ 0` with `N_S(x) = a_S x + O(x^θ)`. -/
def theta (S : Set ℕ) : ℝ := sInf {θ : ℝ | 0 ≤ θ ∧ IsRegular S θ}

/-- The mean square `X⁻¹ ∫_X^{2X} E(x)² dx`. -/
def meanSq (S : Set ℕ) (X : ℝ) : ℝ := X⁻¹ * ∫ x in X..2 * X, err S x ^ 2

/-- `X⁻¹ ∫_X^{2X} E(x)² dx = O(X^{2θ})` on `X ≥ 1`. -/
def IsMSRegular (S : Set ℕ) (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X → meanSq S X ≤ C * X ^ (2 * θ)

/-- `θ₂(S)`: the infimum of the `θ ≥ 0` with `X⁻¹ ∫_X^{2X} E(x)² dx = O(X^{2θ})`. -/
def theta2 (S : Set ℕ) : ℝ := sInf {θ : ℝ | 0 ≤ θ ∧ IsMSRegular S θ}

/-! ### The counting function -/

theorem count_le (S : Set ℕ) {x : ℝ} (hx : 0 ≤ x) : (count S x : ℝ) ≤ x := by
  unfold count
  have h1 : ((Finset.Icc 1 ⌊x⌋₊).filter (SFree S)).card ≤ ⌊x⌋₊ := by
    calc ((Finset.Icc 1 ⌊x⌋₊).filter (SFree S)).card ≤ (Finset.Icc 1 ⌊x⌋₊).card :=
          Finset.card_filter_le _ _
      _ = ⌊x⌋₊ := by simp
  calc (((Finset.Icc 1 ⌊x⌋₊).filter (SFree S)).card : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ x := Nat.floor_le hx

theorem count_mono (S : Set ℕ) : Monotone (count S) := by
  intro x y hxy
  unfold count
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, le_trans hn.1.2 (Nat.floor_le_floor hxy)⟩, hn.2⟩

theorem abs_err_le (S : Set ℕ) {x : ℝ} (hx : 0 ≤ x) : |err S x| ≤ (1 + |density S|) * x := by
  unfold err
  have h0 : (0 : ℝ) ≤ count S x := Nat.cast_nonneg _
  have h1 := count_le S hx
  calc |(count S x : ℝ) - density S * x| ≤ |(count S x : ℝ)| + |density S * x| := abs_sub _ _
    _ = (count S x : ℝ) + |density S| * x := by rw [abs_of_nonneg h0, abs_mul, abs_of_nonneg hx]
    _ ≤ x + |density S| * x := by linarith
    _ = (1 + |density S|) * x := by ring

/-! ### Measurability of the error term -/

theorem intervalIntegrable_count (S : Set ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => (count S x : ℝ)) volume a b := by
  have hm : Monotone (fun x => (count S x : ℝ)) := fun x y h => Nat.cast_le.mpr (count_mono S h)
  exact hm.intervalIntegrable

theorem intervalIntegrable_err (S : Set ℕ) (a b : ℝ) :
    IntervalIntegrable (err S) volume a b := by
  have h2 : IntervalIntegrable (fun x : ℝ => density S * x) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable a b
  exact (intervalIntegrable_count S a b).sub h2

theorem aestronglyMeasurable_err (S : Set ℕ) : AEStronglyMeasurable (err S) volume := by
  have hm : Monotone (fun x => (count S x : ℝ)) := fun x y h => Nat.cast_le.mpr (count_mono S h)
  have h1 : Measurable (fun x => (count S x : ℝ)) := hm.measurable
  have h2 : Measurable (fun x : ℝ => density S * x) := (continuous_const.mul continuous_id).measurable
  exact (h1.sub h2).aestronglyMeasurable

theorem intervalIntegrable_err_sq (S : Set ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => err S x ^ 2) volume a b := by
  have hb : 0 ≤ b := le_trans ha hab
  set M := (1 + |density S|) * b with hM
  have hbound : ∀ x ∈ Set.uIoc a b, ‖err S x ^ 2‖ ≤ M ^ 2 := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have hx0 : 0 ≤ x := le_trans ha (le_of_lt hx.1)
    have h1 := abs_err_le S hx0
    have h2 : (1 + |density S|) * x ≤ M := by
      rw [hM]; exact mul_le_mul_of_nonneg_left hx.2 (by positivity)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_trans h1 h2) 2
  refine IntervalIntegrable.mono_fun' (g := fun _ => M ^ 2) intervalIntegrable_const ?_ ?_
  · exact ((aestronglyMeasurable_err S).pow 2).restrict
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    exact Filter.Eventually.of_forall hbound

/-! ### The exponents `θ(S)` and `θ₂(S)` -/

theorem IsRegular.nonneg_const {S : Set ℕ} {θ C : ℝ} (h : ∀ x : ℝ, 1 ≤ x → |err S x| ≤ C * x ^ θ) :
    0 ≤ C := by
  have := h 1 le_rfl
  rw [Real.one_rpow, mul_one] at this
  exact le_trans (abs_nonneg _) this

theorem IsRegular.mono {S : Set ℕ} {θ θ' : ℝ} (h : IsRegular S θ) (hθ : θ ≤ θ') : IsRegular S θ' := by
  obtain ⟨C, hC⟩ := h
  have hC0 := IsRegular.nonneg_const hC
  refine ⟨C, fun x hx => le_trans (hC x hx) ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hθ) hC0

theorem isRegular_one (S : Set ℕ) : IsRegular S 1 :=
  ⟨1 + |density S|, fun x hx => by
    rw [Real.rpow_one]; exact abs_err_le S (by linarith)⟩

theorem theta_set_bddBelow (S : Set ℕ) : BddBelow {θ : ℝ | 0 ≤ θ ∧ IsRegular S θ} :=
  ⟨0, fun _ h => h.1⟩

theorem theta_set_one_mem (S : Set ℕ) : (1 : ℝ) ∈ {θ : ℝ | 0 ≤ θ ∧ IsRegular S θ} :=
  ⟨zero_le_one, isRegular_one S⟩

theorem theta_nonneg (S : Set ℕ) : 0 ≤ theta S :=
  le_csInf ⟨1, theta_set_one_mem S⟩ fun _ h => h.1

theorem theta_le_one (S : Set ℕ) : theta S ≤ 1 :=
  csInf_le (theta_set_bddBelow S) (theta_set_one_mem S)

/-- Every exponent above `θ(S)` is admissible. -/
theorem isRegular_of_theta_lt {S : Set ℕ} {θ : ℝ} (h : theta S < θ) : IsRegular S θ := by
  obtain ⟨θ₀, hθ₀, hlt⟩ := exists_lt_of_csInf_lt ⟨1, theta_set_one_mem S⟩ h
  exact hθ₀.2.mono hlt.le

/-- An admissible exponent bounds `θ(S)`. -/
theorem theta_le_of_isRegular {S : Set ℕ} {θ : ℝ} (h0 : 0 ≤ θ) (h : IsRegular S θ) : theta S ≤ θ :=
  csInf_le (theta_set_bddBelow S) ⟨h0, h⟩

theorem meanSq_le_of_pointwise {S : Set ℕ} {X M : ℝ} (hX : 1 ≤ X)
    (h : ∀ x ∈ Set.Icc X (2 * X), err S x ^ 2 ≤ M) : meanSq S X ≤ M := by
  unfold meanSq
  have hX0 : 0 < X := by linarith
  have hle : X ≤ 2 * X := by linarith
  have hint : ∫ x in X..2 * X, err S x ^ 2 ≤ ∫ _x in X..2 * X, M :=
    intervalIntegral.integral_mono_on hle (intervalIntegrable_err_sq S hX0.le hle)
      intervalIntegrable_const h
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have : X⁻¹ * ∫ x in X..2 * X, err S x ^ 2 ≤ X⁻¹ * ((2 * X - X) * M) :=
    mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hX0.le)
  calc X⁻¹ * ∫ x in X..2 * X, err S x ^ 2 ≤ X⁻¹ * ((2 * X - X) * M) := this
    _ = M := by field_simp; ring

theorem meanSq_nonneg (S : Set ℕ) {X : ℝ} (hX : 0 ≤ X) : 0 ≤ meanSq S X := by
  unfold meanSq
  apply mul_nonneg (inv_nonneg.mpr hX)
  apply intervalIntegral.integral_nonneg (by linarith)
  intro x _
  positivity

theorem IsMSRegular.nonneg_const {S : Set ℕ} {θ C : ℝ}
    (h : ∀ X : ℝ, 1 ≤ X → meanSq S X ≤ C * X ^ (2 * θ)) : 0 ≤ C := by
  have := h 1 le_rfl
  rw [Real.one_rpow, mul_one] at this
  exact le_trans (meanSq_nonneg S zero_le_one) this

theorem IsMSRegular.mono {S : Set ℕ} {θ θ' : ℝ} (h : IsMSRegular S θ) (hθ : θ ≤ θ') :
    IsMSRegular S θ' := by
  obtain ⟨C, hC⟩ := h
  have hC0 := IsMSRegular.nonneg_const hC
  refine ⟨C, fun X hX => le_trans (hC X hX) ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) hC0

/-- A sup-norm bound gives the same mean-square bound. -/
theorem IsRegular.isMSRegular {S : Set ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (h : IsRegular S θ) :
    IsMSRegular S θ := by
  obtain ⟨C, hC⟩ := h
  have hC0 := IsRegular.nonneg_const hC
  refine ⟨(C * 2 ^ θ) ^ 2, fun X hX => meanSq_le_of_pointwise hX fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans hX hx.1
  have hx0 : 0 ≤ x := by linarith
  have hX0 : 0 ≤ X := by linarith
  have h1 : |err S x| ≤ C * x ^ θ := hC x hx1
  have h2 : C * x ^ θ ≤ C * (2 * X) ^ θ :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0 hx.2 hθ) hC0
  have h3 : err S x ^ 2 ≤ (C * (2 * X) ^ θ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (le_trans h1 h2) 2
  have h4 : X ^ (2 * θ) = (X ^ θ) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hX0, Real.rpow_two]
  calc err S x ^ 2 ≤ (C * (2 * X) ^ θ) ^ 2 := h3
    _ = (C * 2 ^ θ) ^ 2 * X ^ (2 * θ) := by
      rw [h4, Real.mul_rpow (by norm_num) hX0]; ring

theorem isMSRegular_one (S : Set ℕ) : IsMSRegular S 1 :=
  (isRegular_one S).isMSRegular zero_le_one

theorem theta2_set_bddBelow (S : Set ℕ) : BddBelow {θ : ℝ | 0 ≤ θ ∧ IsMSRegular S θ} :=
  ⟨0, fun _ h => h.1⟩

theorem theta2_set_one_mem (S : Set ℕ) : (1 : ℝ) ∈ {θ : ℝ | 0 ≤ θ ∧ IsMSRegular S θ} :=
  ⟨zero_le_one, isMSRegular_one S⟩

theorem theta2_nonneg (S : Set ℕ) : 0 ≤ theta2 S :=
  le_csInf ⟨1, theta2_set_one_mem S⟩ fun _ h => h.1

/-- Every exponent above `θ₂(S)` is admissible in mean square. -/
theorem isMSRegular_of_theta2_lt {S : Set ℕ} {θ : ℝ} (h : theta2 S < θ) : IsMSRegular S θ := by
  obtain ⟨θ₀, hθ₀, hlt⟩ := exists_lt_of_csInf_lt ⟨1, theta2_set_one_mem S⟩ h
  exact hθ₀.2.mono hlt.le

theorem theta2_le_of_isMSRegular {S : Set ℕ} {θ : ℝ} (h0 : 0 ≤ θ) (h : IsMSRegular S θ) :
    theta2 S ≤ θ :=
  csInf_le (theta2_set_bddBelow S) ⟨h0, h⟩

/-- `θ₂(S) ≤ θ(S)`. -/
theorem theta2_le_theta (S : Set ℕ) : theta2 S ≤ theta S := by
  refine le_of_forall_gt_imp_ge_of_dense fun θ hθ => ?_
  have h0 : 0 ≤ θ := le_trans (theta_nonneg S) hθ.le
  exact theta2_le_of_isMSRegular h0 ((isRegular_of_theta_lt hθ).isMSRegular h0)

/-! ### Comparing power laws -/

/-- If `c X^a ≤ C X^b` for arbitrarily large `X`, with `c > 0`, then `a ≤ b`. -/
theorem le_of_frequently_rpow_le {a b c C : ℝ} (hc : 0 < c)
    (h : ∃ᶠ X in atTop, c * X ^ a ≤ C * X ^ b) : a ≤ b := by
  by_contra hab
  push Not at hab
  have hlim : Tendsto (fun X : ℝ => X ^ (a - b)) atTop atTop := tendsto_rpow_atTop (by linarith)
  have hev : ∀ᶠ X in atTop, C / c + 1 ≤ X ^ (a - b) ∧ 1 ≤ X := by
    filter_upwards [hlim.eventually_ge_atTop (C / c + 1), eventually_ge_atTop 1] with X h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨X, hX, h1, h2⟩ := (h.and_eventually hev).exists
  have hX0 : 0 < X := by linarith
  have hb : 0 < X ^ b := Real.rpow_pos_of_pos hX0 b
  have hsplit : X ^ a = X ^ (a - b) * X ^ b := by
    rw [← Real.rpow_add hX0]; ring_nf
  rw [hsplit] at hX
  have : c * (C / c + 1) * X ^ b ≤ c * X ^ (a - b) * X ^ b := by
    apply mul_le_mul_of_nonneg_right _ hb.le
    exact mul_le_mul_of_nonneg_left h1 hc.le
  have : (C + c) * X ^ b ≤ C * X ^ b := by
    calc (C + c) * X ^ b = c * (C / c + 1) * X ^ b := by field_simp
      _ ≤ c * X ^ (a - b) * X ^ b := this
      _ = c * (X ^ (a - b) * X ^ b) := by ring
      _ ≤ C * X ^ b := hX
  nlinarith

end

end DeletedPrimes
