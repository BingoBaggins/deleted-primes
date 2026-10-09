import DeletedPrimes.Legendre
import DeletedPrimes.Exponents
import DeletedPrimes.GoodScales

/-!
# Theorem 6 (every deletion) and Corollaries 7 and 8

The analytic part of §5 — Steps 1–7, the test against the first harmonics of the sawtooth functions of the test
moduli — enters as the hypothesis `Frame S`: for `k ≥ 1`, a level `κ` with the side conditions `κ < 1/2`,
`κ < 1 − α` and all error exponents `errExp k α κ τ ≤ −μ < 0` (Lemma 5.3), there are a tolerance `δ > 0` for the block
shares and a range `η < η₀` such that every configuration of `k` dense dyadic blocks
`T_i = S ∩ [2^{j_i}, 2^{j_i+1})` (increasing, `#T_i ≥ (2^{j_i})^{α−η}`, shares `log 2^{j_i} / log Y` within `δ` of
`1/k`, `Y = ∏ 2^{j_i}` large) has mean square `≥ c ∏ #T_i` at `X = Y^{1/κ}`. This is (5.10) of the paper.

Theorem 9 (the Mertens law, from Landau's and Karamata's theorems) enters as the hypothesis `Quantization S`, and the
first part of Corollary 8 (Landau's theorem at `s = 1`) as `LandauAtOne S`.

Proved here from these hypotheses and the rest of the library:
- Theorem 6(1): `meanSq_lower_prime`; the prime floor `α κ_1(α) ≤ 2θ₂` (`prime_floor`);
- Theorem 6(2): `composite_floor`, `α κ_k(α) ≤ 2θ₂` for every `k ≥ 1`;
- Theorem 6(3): `floor_theta2`, `floor_theta`, `(α/2) min(1/2, 1−α) ≤ θ₂(S) ≤ θ(S)`;
- Corollary 7: `counterexample_window_of_deletion`;
- Corollary 8: `dim_lt_one`, `dim_eq_zero_of_theta2`, `dim_eq_zero_of_theta`.
The choice of block scales (`good_scales`, `frequently_dense_block`), the exponent optimisation (`errExp_le_maxExp`,
`maxExp_neg_iff`), the side conditions and all limits are proved.
-/

open Real Filter Topology

namespace DeletedPrimes

noncomputable section

/-- **Steps 1–7 of §5**, as a hypothesis (the analytic frame of Theorem 6). -/
structure Frame (S : Set ℕ) : Prop where
  bound : ∀ k : ℕ, 1 ≤ k → ∀ κ μ : ℝ, 0 < κ → 0 < μ → κ < 1 / 2 → κ < 1 - dim S →
    (∀ τ ∈ Set.Icc 0 κ, errExp k (dim S) κ τ ≤ -μ) →
    ∃ δ : ℝ, 0 < δ ∧ ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ c : ℝ, 0 < c ∧ ∃ Y₀ : ℝ, ∀ j : Fin k → ℕ, StrictMono j →
        Y₀ ≤ ∏ i, (2 : ℝ) ^ j i →
        (∀ i, |Real.log ((2 : ℝ) ^ j i) / Real.log (∏ i', (2 : ℝ) ^ j i') - 1 / k| ≤ δ) →
        (∀ i, ((2 : ℝ) ^ j i) ^ (dim S - η) ≤ blockCount S (2 ^ j i)) →
        c * ∏ i, (blockCount S (2 ^ j i) : ℝ) ≤ meanSq S ((∏ i, (2 : ℝ) ^ j i) ^ (1 / κ))

/-- **Theorem 9** (Landau's and Karamata's theorems), as a hypothesis: if `θ₂(S) < α(S)`, the deleted primes obey
the Mertens law `∑_{p∈S, p≤x} log p / p^α ∼ m log x` with an integer `m ≥ 1`. -/
def Quantization (S : Set ℕ) : Prop :=
  theta2 S < dim S → ∃ m : ℕ, 1 ≤ m ∧ MertensLaw S (dim S) m

/-- **The first part of Corollary 8** (Landau's theorem at `s = 1`), as a hypothesis. -/
def LandauAtOne (S : Set ℕ) : Prop := theta2 S < 1 → dim S < 1

/-! ### Two elementary helpers -/

/-- If `κ(α − η) ≤ B` for every `η ∈ (0, η₀)`, then `κα ≤ B`. -/
theorem le_of_forall_small {κ α B η₀ : ℝ} (hκ : 0 < κ) (hη₀ : 0 < η₀)
    (h : ∀ η : ℝ, 0 < η → η < η₀ → κ * (α - η) ≤ B) : κ * α ≤ B := by
  by_contra hlt
  push Not at hlt
  set η := min (η₀ / 2) ((κ * α - B) / (2 * κ)) with hηdef
  have hη0 : 0 < η := lt_min (by linarith) (div_pos (by linarith) (by linarith))
  have hη1 : η < η₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hη2 : κ * η ≤ (κ * α - B) / 2 := by
    have : η ≤ (κ * α - B) / (2 * κ) := min_le_right _ _
    calc κ * η ≤ κ * ((κ * α - B) / (2 * κ)) := mul_le_mul_of_nonneg_left this hκ.le
      _ = (κ * α - B) / 2 := by field_simp
  have := h η hη0 hη1
  nlinarith

/-- The block shares: if `L/k ≤ ℓ_i ≤ (1+w) L/k` for all `i`, then `|ℓ_i / ∑ ℓ − 1/k| ≤ w/k`. -/
theorem share_bound {k : ℕ} (hk : 1 ≤ k) {L w : ℝ} (hL : 0 < L) (ℓ : Fin k → ℝ)
    (hℓ : ∀ i, L / k ≤ ℓ i ∧ ℓ i ≤ (1 + w) * L / k) (i : Fin k) :
    L ≤ ∑ i', ℓ i' ∧ |ℓ i / ∑ i', ℓ i' - 1 / k| ≤ w / k := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hsum : L ≤ ∑ i', ℓ i' := by
    calc L = ∑ _i' : Fin k, L / k := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
      _ ≤ ∑ i', ℓ i' := Finset.sum_le_sum fun i' _ => (hℓ i').1
  refine ⟨hsum, ?_⟩
  have hspos : 0 < ∑ i', ℓ i' := lt_of_lt_of_le hL hsum
  have hpair : ∀ i', |ℓ i - ℓ i'| ≤ w * L / k := by
    intro i'
    have h1 := hℓ i; have h2 := hℓ i'
    have e : (1 + w) * L / k - L / k = w * L / k := by ring
    rw [abs_le]; constructor <;> linarith
  have hdiff : |(k : ℝ) * ℓ i - ∑ i', ℓ i'| ≤ w * L := by
    have e : (k : ℝ) * ℓ i - ∑ i', ℓ i' = ∑ i', (ℓ i - ℓ i') := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [e]
    calc |∑ i', (ℓ i - ℓ i')| ≤ ∑ i', |ℓ i - ℓ i'| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i' : Fin k, w * L / k := Finset.sum_le_sum fun i' _ => hpair i'
      _ = w * L := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have e2 : ℓ i / ∑ i', ℓ i' - 1 / k = ((k : ℝ) * ℓ i - ∑ i', ℓ i') / (k * ∑ i', ℓ i') := by
    field_simp
  rw [e2, abs_div, abs_of_pos (mul_pos hkpos hspos), div_le_div_iff₀ (mul_pos hkpos hspos) hkpos]
  have hw : 0 ≤ w * L := le_trans (abs_nonneg _) hdiff
  calc |(k : ℝ) * ℓ i - ∑ i', ℓ i'| * k ≤ w * L * k := mul_le_mul_of_nonneg_right hdiff hkpos.le
    _ ≤ w * (k * ∑ i', ℓ i') := by
        have : w * L * k = (w * L) * k := rfl
        nlinarith [mul_le_mul_of_nonneg_left hsum (le_of_lt hkpos), hw]

/-! ### Theorem 6(1): the prime test -/

/-- **Theorem 6(1).** For every `κ < κ_1(α)` and `ε > 0` there are arbitrarily large `X` with
`X⁻¹∫_X^{2X} E² ≥ c X^{ακ−ε}`. -/
theorem meanSq_lower_prime {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) {κ ε : ℝ} (hκ0 : 0 < κ) (hκ : κ < kappaOne (dim S)) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ X : ℝ in atTop, c * X ^ (dim S * κ - ε) ≤ meanSq S X := by
  set α := dim S with hαdef
  have hκ1 : κ < kappaK 1 α := by rw [kappaK_one]; exact hκ
  set μ := -maxExp 1 α κ with hμdef
  have hμ : 0 < μ := by have := (maxExp_neg_iff le_rfl hα0 hα1).2 hκ1; linarith
  have herr : ∀ τ ∈ Set.Icc 0 κ, errExp 1 α κ τ ≤ -μ := fun τ hτ => by
    rw [hμdef, neg_neg]; exact errExp_le_maxExp le_rfl hα0 hα1 hκ0.le hτ.1 hτ.2
  have h12 : κ < 1 / 2 := lt_trans hκ1 (kappaK_lt_half le_rfl hα0 hα1)
  have h1a : κ < 1 - α := lt_trans hκ1 (kappaK_lt_one_sub le_rfl hα0 hα1)
  obtain ⟨δ, hδ, η₀, hη₀, hF⟩ := F.bound 1 le_rfl κ μ hκ0 hμ h12 h1a herr
  set η₁ := min (η₀ / 4) (min (α / 2) (ε / (2 * κ))) with hη₁def
  have hη₁0 : 0 < η₁ := lt_min (by linarith) (lt_min (by linarith) (div_pos hε (by linarith)))
  have hη₁a : η₁ ≤ η₀ / 4 := min_le_left _ _
  have hη₁b : η₁ ≤ α / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hη₁c : η₁ ≤ ε / (2 * κ) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hκη : 2 * κ * η₁ ≤ ε := by
    calc 2 * κ * η₁ ≤ 2 * κ * (ε / (2 * κ)) := mul_le_mul_of_nonneg_left hη₁c (by linarith)
      _ = ε := by field_simp
  obtain ⟨c, hc, Y₀, hY⟩ := hF (2 * η₁) (by linarith) (by linarith)
  refine ⟨c, hc, ?_⟩
  have hdense := frequently_dense_block (S := S) (σ := α - η₁) (η := η₁) (by linarith) (by linarith) hη₁0
  have hlarge : ∀ᶠ j : ℕ in atTop, Y₀ ≤ (2 : ℝ) ^ j ∧ 1 ≤ j := by
    have h2 : Tendsto (fun j : ℕ => (2 : ℝ) ^ j) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    filter_upwards [h2.eventually_ge_atTop Y₀, eventually_ge_atTop 1] with j h1 h2
    exact ⟨h1, h2⟩
  have hX : Tendsto (fun j : ℕ => ((2 : ℝ) ^ j) ^ (1 / κ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  refine hX.frequently ((hdense.and_eventually hlarge).mono fun j ⟨hd, hjY, hj1⟩ => ?_)
  set jf : Fin 1 → ℕ := fun _ => j with hjf
  have hmono : StrictMono jf := fun a b hab => absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl _)
  have hprod : ∏ i, (2 : ℝ) ^ jf i = 2 ^ j := by simp [hjf]
  have hlog : 0 < Real.log ((2 : ℝ) ^ j) := Real.log_pos (one_lt_pow₀ (by norm_num) (by omega))
  have hshare : ∀ i, |Real.log ((2 : ℝ) ^ jf i) / Real.log (∏ i', (2 : ℝ) ^ jf i') - 1 / ((1 : ℕ) : ℝ)| ≤ δ := by
    intro i
    rw [hprod]
    simp only [hjf, Nat.cast_one, div_one]
    rw [div_self hlog.ne', sub_self, abs_zero]; exact hδ.le
  have hdens : ∀ i, ((2 : ℝ) ^ jf i) ^ (α - 2 * η₁) ≤ blockCount S (2 ^ jf i) := by
    intro i
    have : α - 2 * η₁ = α - η₁ - η₁ := by ring
    simpa [hjf, this] using hd
  have key := hY jf hmono (by rw [hprod]; exact hjY) hshare hdens
  rw [hprod] at key
  simp only [hjf, Finset.univ_unique, Finset.prod_singleton] at key
  have hB : 1 ≤ ((2 : ℝ) ^ j) := one_le_pow₀ (by norm_num)
  have hXge : 1 ≤ ((2 : ℝ) ^ j) ^ (1 / κ) := Real.one_le_rpow hB (by positivity)
  have hdj : ((2 : ℝ) ^ j) ^ (α - 2 * η₁) ≤ blockCount S (2 ^ j) := by simpa [hjf] using hdens ⟨0, by omega⟩
  calc c * (((2 : ℝ) ^ j) ^ (1 / κ)) ^ (α * κ - ε)
      ≤ c * (((2 : ℝ) ^ j) ^ (1 / κ)) ^ (κ * (α - 2 * η₁)) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        exact Real.rpow_le_rpow_of_exponent_le hXge (by nlinarith)
    _ = c * ((2 : ℝ) ^ j) ^ (α - 2 * η₁) := by
        rw [← Real.rpow_mul (by positivity)]
        congr 2; field_simp
    _ ≤ c * (blockCount S (2 ^ j) : ℝ) := mul_le_mul_of_nonneg_left hdj hc.le
    _ ≤ meanSq S (((2 : ℝ) ^ j) ^ (1 / κ)) := key

/-- A mean-square lower bound along arbitrarily large `X` bounds `θ₂` from below. -/
theorem le_two_theta2_of_frequently {S : Set ℕ} {a c : ℝ} (hc : 0 < c)
    (h : ∃ᶠ X : ℝ in atTop, c * X ^ a ≤ meanSq S X) : a ≤ 2 * theta2 S := by
  have key : ∀ θ' : ℝ, theta2 S < θ' → a ≤ 2 * θ' := by
    intro θ' hθ'
    obtain ⟨C, hC⟩ := isMSRegular_of_theta2_lt hθ'
    apply le_of_frequently_rpow_le hc (C := C)
    refine (h.and_eventually (eventually_ge_atTop 1)).mono fun X ⟨h1, h2⟩ => ?_
    exact le_trans h1 (hC X h2)
  by_contra hlt
  push Not at hlt
  have := key ((theta2 S + a / 2) / 2) (by linarith)
  linarith

/-- The prime floor: `α κ_1(α) ≤ 2θ₂(S)`, hence `θ(S) ≥ θ₂(S) ≥ α(1−α)/(2(1+(1−α)²))`. -/
theorem prime_floor {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) : dim S * kappaOne (dim S) ≤ 2 * theta2 S := by
  set α := dim S
  have hk1 : 0 < kappaOne α := by rw [← kappaK_one]; exact kappaK_pos le_rfl hα0 hα1
  have hκ : ∀ κ : ℝ, 0 < κ → κ < kappaOne α → α * κ ≤ 2 * theta2 S := by
    intro κ hκ0 hκ
    have : ∀ ε : ℝ, 0 < ε → α * κ - ε ≤ 2 * theta2 S := by
      intro ε hε
      obtain ⟨c, hc, hfr⟩ := meanSq_lower_prime hα0 hα1 F hκ0 hκ hε
      exact le_two_theta2_of_frequently hc hfr
    by_contra hlt; push Not at hlt
    have := this ((α * κ - 2 * theta2 S) / 2) (by linarith); linarith
  by_contra hlt; push Not at hlt
  set κ := (2 * theta2 S / α + kappaOne α) / 2 with hκdef
  have hθ0 := theta2_nonneg S
  have hlt' : 2 * theta2 S / α < kappaOne α := by
    rw [div_lt_iff₀ hα0]; linarith
  have hκ0 : 0 < κ := by
    have : 0 ≤ 2 * theta2 S / α := div_nonneg (by linarith) hα0.le
    rw [hκdef]; linarith
  have hκ1 : κ < kappaOne α := by rw [hκdef]; linarith
  have h1 := hκ κ hκ0 hκ1
  have h2 : 2 * theta2 S < α * κ := by
    have : 2 * theta2 S / α < κ := by rw [hκdef]; linarith
    rw [div_lt_iff₀ hα0] at this; linarith
  linarith

/-! ### Theorem 6(2): product test moduli -/

/-- The scales for `k` product blocks: for every `η` below the frame's range, the mean square is
`≥ c X^{κ(α−η)}` along arbitrarily large `X`. -/
theorem meanSq_lower_composite {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) {m : ℝ} (hm : 0 < m) (hM : MertensLaw S (dim S) m) {k : ℕ} (hk : 1 ≤ k) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ : κ < kappaK k (dim S)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ c : ℝ, 0 < c ∧ ∃ᶠ X : ℝ in atTop, c * X ^ (κ * (dim S - η)) ≤ meanSq S X := by
  set α := dim S with hαdef
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  set μ := -maxExp k α κ with hμdef
  have hμ : 0 < μ := by have := (maxExp_neg_iff hk hα0 hα1).2 hκ; linarith
  have herr : ∀ τ ∈ Set.Icc 0 κ, errExp k α κ τ ≤ -μ := fun τ hτ => by
    rw [hμdef, neg_neg]; exact errExp_le_maxExp hk hα0 hα1 hκ0.le hτ.1 hτ.2
  have h12 : κ < 1 / 2 := lt_trans hκ (kappaK_lt_half hk hα0 hα1)
  have h1a : κ < 1 - α := lt_trans hκ (kappaK_lt_one_sub hk hα0 hα1)
  obtain ⟨δ, hδ, η₀, hη₀, hF⟩ := F.bound k hk κ μ hκ0 hμ h12 h1a herr
  refine ⟨η₀, hη₀, fun η hη hηlt => ?_⟩
  obtain ⟨c, hc, Y₀, hY⟩ := hF η hη hηlt
  refine ⟨c, hc, ?_⟩
  -- the block exponents `λ_i = (1 + iρ)/k`, separated by the factor `1 + δ'`
  set ρ := min 1 (k * δ / (2 * k + 1)) with hρdef
  have hρ0 : 0 < ρ := lt_min one_pos (div_pos (mul_pos hkpos hδ) (by linarith))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρ2 : ρ ≤ k * δ / (2 * k + 1) := min_le_right _ _
  set δ' := ρ / (2 * (1 + k * ρ)) with hδ'def
  have hD : 0 < 1 + k * ρ := by positivity
  have hδ'0 : 0 < δ' := by positivity
  have hδ'ρ : δ' * (1 + k * ρ) = ρ / 2 := by rw [hδ'def]; field_simp
  have hδ'le : δ' ≤ ρ := by
    have : δ' * 1 ≤ δ' * (1 + k * ρ) := mul_le_mul_of_nonneg_left (by nlinarith) hδ'0.le
    linarith
  set w := (1 + k * ρ) * (1 + δ') - 1 with hwdef
  have hw : w ≤ k * δ := by
    have h1 : w ≤ (2 * k + 1) * ρ := by
      have : (1 + k * ρ) * (1 + δ') ≤ (1 + k * ρ) * (1 + ρ) := mul_le_mul_of_nonneg_left (by linarith) hD.le
      have h2 : k * ρ * ρ ≤ k * ρ := mul_le_of_le_one_right (by positivity) hρ1
      rw [hwdef]; nlinarith
    have h3 : (2 * k + 1) * ρ ≤ k * δ := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * k + 1)] at hρ2; linarith
    linarith
  set lam : Fin k → ℝ := fun i => (1 + (i : ℝ) * ρ) / k with hlamdef
  have hlam0 : ∀ i, 0 < lam i := fun i => by rw [hlamdef]; positivity
  have hlamlo : ∀ i, 1 / k ≤ lam i := fun i => by
    have : (0 : ℝ) ≤ (i : ℝ) * ρ := by positivity
    rw [hlamdef]; apply div_le_div_of_nonneg_right _ hkpos.le; linarith
  have hlamhi : ∀ i, lam i * (1 + δ') ≤ (1 + w) / k := fun i => by
    have hi : (i : ℝ) ≤ k := by exact_mod_cast i.isLt.le
    rw [hlamdef, hwdef, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hkpos.le
    have : 1 + (i : ℝ) * ρ ≤ 1 + k * ρ := by nlinarith
    nlinarith
  have hsep : ∀ i i' : Fin k, i < i' → lam i * (1 + δ') < lam i' := by
    intro i i' hii'
    have hlt : (i : ℝ) + 1 ≤ i' := by exact_mod_cast (show (i : ℕ) + 1 ≤ i' from hii')
    have hi : (i : ℝ) ≤ k := by exact_mod_cast i.isLt.le
    rw [hlamdef, div_mul_eq_mul_div]
    apply div_lt_div_of_pos_right _ hkpos
    have h1 : (1 + (i : ℝ) * ρ) * δ' ≤ (1 + k * ρ) * δ' :=
      mul_le_mul_of_nonneg_right (by nlinarith) hδ'0.le
    nlinarith
  have hgs := good_scales hα0 hm hM hδ'0 hη lam hlam0 hsep
  rw [Filter.frequently_atTop]
  intro B
  have hev : ∀ᶠ X₀ : ℝ in atTop, (∃ j : Fin k → ℕ, StrictMono j ∧ ∀ i,
      X₀ ^ lam i ≤ 2 ^ j i ∧ (2 : ℝ) ^ j i ≤ X₀ ^ (lam i * (1 + δ')) ∧
      ((2 : ℝ) ^ j i) ^ (α - η) ≤ blockCount S (2 ^ j i)) ∧ 1 < X₀ ∧ Y₀ ≤ X₀ ∧ B ≤ X₀ ^ (1 / κ) := by
    filter_upwards [hgs, eventually_gt_atTop 1, eventually_ge_atTop Y₀,
      (tendsto_rpow_atTop (show 0 < 1 / κ by positivity)).eventually_ge_atTop B] with X₀ h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨X₀, ⟨j, hj, hjb⟩, hX₀1, hX₀Y, hX₀B⟩ := hev.exists
  have hX₀0 : 0 < X₀ := by linarith
  set L := Real.log X₀ with hLdef
  have hL : 0 < L := Real.log_pos hX₀1
  set ℓ : Fin k → ℝ := fun i => Real.log ((2 : ℝ) ^ j i) with hℓdef
  have hℓ : ∀ i, L / k ≤ ℓ i ∧ ℓ i ≤ (1 + w) * L / k := by
    intro i
    obtain ⟨hlo, hhi, -⟩ := hjb i
    have hpos : (0 : ℝ) < 2 ^ j i := by positivity
    have e1 : Real.log (X₀ ^ lam i) = lam i * L := Real.log_rpow hX₀0 _
    have e2 : Real.log (X₀ ^ (lam i * (1 + δ'))) = lam i * (1 + δ') * L := Real.log_rpow hX₀0 _
    have l1 : lam i * L ≤ ℓ i := by
      rw [← e1]; exact Real.log_le_log (by positivity) hlo
    have l2 : ℓ i ≤ lam i * (1 + δ') * L := by
      rw [← e2]; exact Real.log_le_log hpos hhi
    constructor
    · calc L / k = 1 / k * L := by ring
        _ ≤ lam i * L := mul_le_mul_of_nonneg_right (hlamlo i) hL.le
        _ ≤ ℓ i := l1
    · calc ℓ i ≤ lam i * (1 + δ') * L := l2
        _ ≤ (1 + w) / k * L := mul_le_mul_of_nonneg_right (hlamhi i) hL.le
        _ = (1 + w) * L / k := by ring
  have hlogY : Real.log (∏ i, (2 : ℝ) ^ j i) = ∑ i, ℓ i :=
    Real.log_prod (fun i _ => by positivity)
  have hYpos : 0 < ∏ i, (2 : ℝ) ^ j i := Finset.prod_pos fun i _ => by positivity
  have hshare : ∀ i, |Real.log ((2 : ℝ) ^ j i) / Real.log (∏ i', (2 : ℝ) ^ j i') - 1 / k| ≤ δ := by
    intro i
    rw [hlogY]
    have := (share_bound hk hL ℓ hℓ i).2
    have h2 : w / k ≤ δ := by rw [div_le_iff₀ hkpos]; linarith
    exact le_trans this h2
  have hYX₀ : X₀ ≤ ∏ i, (2 : ℝ) ^ j i := by
    have h1 : L ≤ Real.log (∏ i, (2 : ℝ) ^ j i) := by
      rw [hlogY]; exact (share_bound hk hL ℓ hℓ ⟨0, by omega⟩).1
    exact (Real.log_le_log_iff hX₀0 hYpos).mp h1
  have hdens : ∀ i, ((2 : ℝ) ^ j i) ^ (α - η) ≤ blockCount S (2 ^ j i) := fun i => (hjb i).2.2
  have key := hY j hj (le_trans hX₀Y hYX₀) hshare hdens
  set Y := ∏ i, (2 : ℝ) ^ j i with hYdef
  refine ⟨Y ^ (1 / κ), le_trans hX₀B (Real.rpow_le_rpow hX₀0.le hYX₀ (by positivity)), ?_⟩
  have hprod : Y ^ (α - η) ≤ ∏ i, (blockCount S (2 ^ j i) : ℝ) := by
    rw [hYdef, ← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
    gcongr with i _
    exact hdens i
  calc c * (Y ^ (1 / κ)) ^ (κ * (α - η)) = c * Y ^ (α - η) := by
        rw [← Real.rpow_mul hYpos.le]; congr 2; field_simp
    _ ≤ c * ∏ i, (blockCount S (2 ^ j i) : ℝ) := mul_le_mul_of_nonneg_left hprod hc.le
    _ ≤ meanSq S (Y ^ (1 / κ)) := key

/-- **Theorem 6(2).** `α κ_k(α) ≤ 2θ₂(S)` for every `k ≥ 1`. -/
theorem composite_floor {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) (Q : Quantization S) {k : ℕ} (hk : 1 ≤ k) :
    dim S * kappaK k (dim S) ≤ 2 * theta2 S := by
  set α := dim S with hαdef
  have hθ0 := theta2_nonneg S
  have hkap := kappaK_lt_half hk hα0 hα1
  by_cases hθα : α ≤ theta2 S
  · nlinarith [kappaK_pos hk hα0 hα1]
  push Not at hθα
  obtain ⟨m, hm1, hM⟩ := Q hθα
  have hm : (0 : ℝ) < m := by exact_mod_cast hm1
  have hκ : ∀ κ : ℝ, 0 < κ → κ < kappaK k α → κ * α ≤ 2 * theta2 S := by
    intro κ hκ0 hκ
    obtain ⟨η₀, hη₀, h⟩ := meanSq_lower_composite hα0 hα1 F hm hM hk hκ0 hκ
    apply le_of_forall_small hκ0 hη₀
    intro η hη hηlt
    obtain ⟨c, hc, hfr⟩ := h η hη hηlt
    exact le_two_theta2_of_frequently hc hfr
  by_contra hlt; push Not at hlt
  set κ := (2 * theta2 S / α + kappaK k α) / 2 with hκdef
  have hlt' : 2 * theta2 S / α < kappaK k α := by rw [div_lt_iff₀ hα0]; linarith
  have hκ0 : 0 < κ := by
    have : 0 ≤ 2 * theta2 S / α := div_nonneg (by linarith) hα0.le
    rw [hκdef]; linarith
  have hκ1 : κ < kappaK k α := by rw [hκdef]; linarith
  have h1 := hκ κ hκ0 hκ1
  have h2 : 2 * theta2 S < κ * α := by
    have : 2 * theta2 S / α < κ := by rw [hκdef]; linarith
    rw [div_lt_iff₀ hα0] at this; linarith
  linarith

/-! ### Theorem 6(3) and Corollaries 7 and 8 -/

/-- **Theorem 6(3)**, mean square: `θ₂(S) ≥ (α/2) min(1/2, 1−α)`. -/
theorem floor_theta2 {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) (Q : Quantization S) : dim S / 2 * min (1 / 2) (1 - dim S) ≤ theta2 S :=
  floor_of_forall_k hα1 fun _ hk => composite_floor hα0 hα1 F Q hk

/-- **Theorem 6(3)**: `θ(S) ≥ θ₂(S) ≥ (α/2) min(1/2, 1−α)`. -/
theorem floor_theta {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) (Q : Quantization S) : dim S / 2 * min (1 / 2) (1 - dim S) ≤ theta S :=
  (floor_theta2 hα0 hα1 F Q).trans (theta2_le_theta S)

/-- **Corollary 8**, first part, in the form used: `θ₂(S) < 1` forces `α(S) < 1`. -/
theorem dim_lt_one {S : Set ℕ} (L : LandauAtOne S) (h : theta2 S < 1) : dim S < 1 := L h

/-- **Corollary 7** (the counterexample window). -/
theorem counterexample_window_of_deletion {S : Set ℕ} (F : Frame S)
    (Q : Quantization S) (L : LandauAtOne S) {θ : ℝ} (hθ8 : θ < 1 / 8) (hθ2 : theta2 S ≤ θ)
    (hθα : θ < dim S / 2) :
    (2 * θ < dim S ∧ dim S ≤ 4 * θ) ∨ 1 - (1 - Real.sqrt (1 - 8 * θ)) / 2 ≤ dim S := by
  have hθ0 : 0 ≤ θ := le_trans (theta2_nonneg S) hθ2
  have hα0 : 0 < dim S := by linarith
  have hα1 : dim S < 1 := L (by linarith)
  exact counterexample_window hα0 hα1 hθ8 hθα ((floor_theta2 hα0 hα1 F Q).trans hθ2)

/-- **Corollary 8**: `θ₂(S) = 0` forces `α(S) = 0`. -/
theorem dim_eq_zero_of_theta2 {S : Set ℕ} (F : Frame S) (Q : Quantization S)
    (L : LandauAtOne S) (h : theta2 S = 0) : dim S = 0 := by
  have hα1 : dim S < 1 := L (by rw [h]; norm_num)
  rcases (dim_nonneg S).lt_or_eq with hα0 | hα0
  · exfalso
    have hfl := floor_theta2 hα0 hα1 F Q
    rw [h] at hfl
    have : 0 < dim S / 2 * min (1 / 2) (1 - dim S) :=
      mul_pos (by linarith) (lt_min (by norm_num) (by linarith))
    linarith
  · exact hα0.symm

/-- **Corollary 8**: `N_S(x) = a_S x + O(x^ε)` for every `ε > 0` (that is, `θ(S) = 0`) forces `α(S) = 0`. -/
theorem dim_eq_zero_of_theta {S : Set ℕ} (F : Frame S) (Q : Quantization S)
    (L : LandauAtOne S) (h : theta S = 0) : dim S = 0 := by
  have h2 : theta2 S = 0 := le_antisymm (h ▸ theta2_le_theta S) (theta2_nonneg S)
  exact dim_eq_zero_of_theta2 F Q L h2

end

end DeletedPrimes
