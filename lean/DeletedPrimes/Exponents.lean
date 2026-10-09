import Mathlib

/-!
# The exponent arithmetic of Theorem 6 (the composite-modulus floor)

With `k` blocks of equal weight, level `κ = log Y / log X` and `t = X^τ`, the third error bullet of Step 5 has
normalised exponent `errExp k α κ τ = (α−1) + κ + τ(1−α) + h(τ) − ακ`, where `h(τ)` is the exponent of the per-unit hit
count given by Lemma 5.2 (composite window rigidity):
`h(τ) = min_{0≤i≤k} [ακ i/k + max(κ − τ − κ i/k, 0)]`.

Proved here, for `0 < α < 1` and `k ≥ 1`:
- the maximum over `τ ∈ [0, κ]` is attained at `τ* = κ − ακ/k` (`α ≤ 1/2`) or `τ* = κ(1−α)/k` (`α ≥ 1/2`), with
  value `(α−1) + κ(2 − 2α + α²/k)`, resp. `(α−1) + κ(1 + (1−α)²/k)` (`errExp_le_maxExp`, `errExp_argmax`);
- every exponent is negative iff `κ < κ_k(α)` (`errExp_neg_iff`);
- `κ_k(α) < min(1/2, 1−α)` (`kappaK_lt_half`, `kappaK_lt_one_sub`), the side conditions of Steps 2, 5, 6;
- the boundary term on `(κ, κ+ε]` is negative (`boundary_neg`);
- unequal block weights cost at most `(1+α)κδ` (`hitExp_perturb`);
- `k = 1` is the prime test: `κ_1(α) = κ(α) = (1−α)/(1+(1−α)²)` (`kappaK_one`, `errExp_one`);
- `κ_k(α)` increases to `min(1/2, 1−α)` (`kappaK_mono`, `tendsto_kappaK`), whence the floor
  `(α/2) min(1/2, 1−α)` (`floor_of_forall_k`);
- Corollary 7, the counterexample window (`counterexample_window`).
-/

open Real Filter Topology

namespace DeletedPrimes

noncomputable section

/-- `κ(α) = (1−α)/(1+(1−α)²)`, the level of the prime test. -/
def kappaOne (α : ℝ) : ℝ := (1 - α) / (1 + (1 - α) ^ 2)

/-- `κ_k(α)`, the level reached with test moduli from `k` blocks. -/
def kappaK (k : ℕ) (α : ℝ) : ℝ :=
  if α ≤ 1 / 2 then (1 - α) / (2 * (1 - α) + α ^ 2 / k) else (1 - α) / (1 + (1 - α) ^ 2 / k)

/-- The exponent of the per-unit hit count, `h(τ) = min_{0≤i≤k} [ακ i/k + max(κ − τ − κ i/k, 0)]`. -/
def hitExp (k : ℕ) (α κ τ : ℝ) : ℝ :=
  (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
    fun i => α * κ * i / k + max (κ - τ - κ * i / k) 0

/-- The normalised exponent of the third error bullet of Step 5 at `t = X^τ`. -/
def errExp (k : ℕ) (α κ τ : ℝ) : ℝ := (α - 1) + κ + τ * (1 - α) + hitExp k α κ τ - α * κ

/-- The maximum of `errExp k α κ` over `τ ∈ [0, κ]`. -/
def maxExp (k : ℕ) (α κ : ℝ) : ℝ :=
  if α ≤ 1 / 2 then (α - 1) + κ * (2 - 2 * α + α ^ 2 / k) else (α - 1) + κ * (1 + (1 - α) ^ 2 / k)

/-- The point where the maximum is attained. -/
def argmaxExp (k : ℕ) (α κ : ℝ) : ℝ := if α ≤ 1 / 2 then κ - α * κ / k else κ * (1 - α) / k

/-! ### Helper lemmas on `hitExp` -/

/-- `hitExp` is at most each of its terms. -/
lemma hitExp_le_term {k : ℕ} {α κ τ : ℝ} {i : ℕ} (hi : i ≤ k) :
    hitExp k α κ τ ≤ α * κ * i / k + max (κ - τ - κ * i / k) 0 :=
  Finset.inf'_le (fun i : ℕ => α * κ * i / k + max (κ - τ - κ * i / k) 0)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-- A lower bound for every term is a lower bound for `hitExp`. -/
lemma le_hitExp {k : ℕ} {α κ τ c : ℝ}
    (h : ∀ i ≤ k, c ≤ α * κ * i / k + max (κ - τ - κ * i / k) 0) : c ≤ hitExp k α κ τ :=
  Finset.le_inf' _ _ fun i hi => h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

/-- The terms of `hitExp` written with the unit `u = κ/k`. -/
lemma term_u {k : ℕ} (hk : 1 ≤ k) {α κ u τ : ℝ} (hκu : κ = k * u) (i : ℕ) :
    α * κ * i / k + max (κ - τ - κ * i / k) 0 = α * i * u + max (κ - τ - i * u) 0 := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have e1 : α * κ * i / k = α * i * u := by rw [div_eq_iff hk0, hκu]; ring
  have e2 : κ * i / k = i * u := by rw [div_eq_iff hk0, hκu]; ring
  rw [e1, e2]

lemma hitExp_le_pos {k : ℕ} (hk : 1 ≤ k) {α κ u τ : ℝ} (hκu : κ = k * u) {i : ℕ} (hi : i ≤ k)
    (ha : 0 ≤ κ - τ - i * u) : hitExp k α κ τ ≤ α * i * u + (κ - τ - i * u) := by
  have h := hitExp_le_term (α := α) (κ := κ) (τ := τ) hi
  rw [term_u hk hκu, max_eq_left ha] at h
  exact h

lemma hitExp_le_neg {k : ℕ} (hk : 1 ≤ k) {α κ u τ : ℝ} (hκu : κ = k * u) {i : ℕ} (hi : i ≤ k)
    (ha : κ - τ - i * u ≤ 0) : hitExp k α κ τ ≤ α * i * u := by
  have h := hitExp_le_term (α := α) (κ := κ) (τ := τ) hi
  rw [term_u hk hκu, max_eq_right ha, add_zero] at h
  exact h

lemma le_hitExp_u {k : ℕ} (hk : 1 ≤ k) {α κ u τ c : ℝ} (hκu : κ = k * u)
    (h : ∀ i ≤ k, c ≤ α * i * u + max (κ - τ - i * u) 0) : c ≤ hitExp k α κ τ :=
  le_hitExp fun i hi => by rw [term_u hk hκu]; exact h i hi

/-- Division of `j ∈ [0, k u]` by the unit `u`, with the remainder compared to `α u`. -/
lemma decomp {u j α : ℝ} {k : ℕ} (hα : 0 < α) (hu : 0 ≤ u) (hj0 : 0 ≤ j) (hjk : j ≤ k * u) :
    ∃ n : ℕ, n ≤ k ∧ (n : ℝ) * u ≤ j ∧
      (j - n * u ≤ α * u ∨ (α * u < j - n * u ∧ j < ((n : ℝ) + 1) * u ∧ n + 1 ≤ k)) := by
  rcases hu.eq_or_lt with hu0 | hupos
  · subst hu0
    refine ⟨0, Nat.zero_le _, ?_, Or.inl ?_⟩
    · simpa using hj0
    · simp only [mul_zero] at hjk ⊢; linarith
  · obtain ⟨n, h1, h2⟩ : ∃ n : ℕ, (n : ℝ) ≤ j / u ∧ j / u < n + 1 :=
      ⟨⌊j / u⌋₊, Nat.floor_le (div_nonneg hj0 hupos.le), Nat.lt_floor_add_one _⟩
    have h1' : (n : ℝ) * u ≤ j := (le_div_iff₀ hupos).1 h1
    have h2' : j < (n + 1) * u := (div_lt_iff₀ hupos).1 h2
    have hnk : n ≤ k := by
      have : (n : ℝ) ≤ k := le_of_mul_le_mul_right (h1'.trans hjk) hupos
      exact_mod_cast this
    refine ⟨n, hnk, h1', ?_⟩
    by_cases hr : j - n * u ≤ α * u
    · exact Or.inl hr
    · push Not at hr
      refine Or.inr ⟨hr, h2', ?_⟩
      have hne : n ≠ k := by
        intro h
        rw [h] at hr
        have := mul_pos hα hupos
        linarith
      omega

lemma maxExp_u {k : ℕ} (hk : 1 ≤ k) (α u : ℝ) :
    maxExp k α (k * u) = if α ≤ 1 / 2 then (α - 1) + 2 * (k * u) - 2 * α * (k * u) + α ^ 2 * u
      else (α - 1) + k * u + (1 - α) ^ 2 * u := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold maxExp
  split_ifs
  · have e : (k : ℝ) * u * (α ^ 2 / k) = α ^ 2 * u := by
      rw [mul_div_assoc', div_eq_iff hk0]; ring
    linear_combination e
  · have e : (k : ℝ) * u * ((1 - α) ^ 2 / k) = (1 - α) ^ 2 * u := by
      rw [mul_div_assoc', div_eq_iff hk0]; ring
    linear_combination e

lemma argmaxExp_u {k : ℕ} (hk : 1 ≤ k) (α u : ℝ) :
    argmaxExp k α (k * u) = if α ≤ 1 / 2 then k * u - α * u else (1 - α) * u := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold argmaxExp
  have e1 : α * (k * u) / k = α * u := by rw [div_eq_iff hk0]; ring
  have e2 : k * u * (1 - α) / k = (1 - α) * u := by rw [div_eq_iff hk0]; ring
  rw [e1, e2]

theorem kappaK_one (α : ℝ) : kappaK 1 α = kappaOne α := by
  unfold kappaK kappaOne
  have h1 : (2 * (1 - α) + α ^ 2 / ((1 : ℕ) : ℝ)) = 1 + (1 - α) ^ 2 := by push_cast; ring
  have h2 : (1 + (1 - α) ^ 2 / ((1 : ℕ) : ℝ)) = 1 + (1 - α) ^ 2 := by push_cast; ring
  split_ifs <;> simp only [h1, h2]

theorem errExp_one {α κ τ : ℝ} (hτ0 : 0 ≤ τ) (hτκ : τ ≤ κ) :
    errExp 1 α κ τ = (α - 1) + κ + τ * (1 - α) + min (α * κ) (κ - τ) - α * κ := by
  have hκu : κ = ((1 : ℕ) : ℝ) * κ := by simp
  have hH : hitExp 1 α κ τ = min (α * κ) (κ - τ) := by
    apply le_antisymm
    · apply le_min
      · have h := hitExp_le_neg (α := α) (τ := τ) le_rfl hκu (i := 1) le_rfl
          (by push_cast; linarith)
        push_cast at h
        linarith
      · have h := hitExp_le_pos (α := α) (τ := τ) le_rfl hκu (i := 0) (Nat.zero_le _)
          (by push_cast; linarith)
        push_cast at h
        linarith
    · apply le_hitExp_u le_rfl hκu
      intro i hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · have := le_max_left (κ - τ - ((0 : ℕ) : ℝ) * κ) 0
        have := min_le_right (α * κ) (κ - τ)
        push_cast at *
        linarith
      · have := le_max_right (κ - τ - ((1 : ℕ) : ℝ) * κ) 0
        have := min_le_left (α * κ) (κ - τ)
        push_cast at *
        linarith
  unfold errExp
  rw [hH]

theorem kappaK_pos {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) : 0 < kappaK k α := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  unfold kappaK
  split_ifs
  · exact div_pos (by linarith) (by have : 0 ≤ α ^ 2 / k := by positivity
                                    linarith)
  · exact div_pos (by linarith) (by have : 0 ≤ (1 - α) ^ 2 / k := by positivity
                                    linarith)

theorem kappaK_lt_half {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    kappaK k α < 1 / 2 := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  unfold kappaK
  split_ifs with hα
  · have hA : 0 < α ^ 2 / k := by positivity
    rw [div_lt_iff₀ (by linarith)]
    linarith
  · push Not at hα
    have hA : 0 ≤ (1 - α) ^ 2 / k := by positivity
    rw [div_lt_iff₀ (by linarith)]
    linarith

theorem kappaK_lt_one_sub {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    kappaK k α < 1 - α := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  unfold kappaK
  split_ifs with hα
  · have hA : 0 < α ^ 2 / k := by positivity
    exact div_lt_self (by linarith) (by linarith)
  · have hA : 0 < (1 - α) ^ 2 / k := by
      have : 0 < 1 - α := by linarith
      positivity
    exact div_lt_self (by linarith) (by linarith)

theorem argmaxExp_mem {k : ℕ} (hk : 1 ≤ k) {α κ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hκ : 0 ≤ κ) :
    argmaxExp k α κ ∈ Set.Icc 0 κ := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold argmaxExp
  split_ifs
  · constructor
    · have : α * κ / k ≤ κ := by
        rw [div_le_iff₀ hkpos]; nlinarith
      linarith
    · have : 0 ≤ α * κ / k := by positivity
      linarith
  · constructor
    · exact div_nonneg (mul_nonneg hκ (by linarith)) hkpos.le
    · rw [div_le_iff₀ hkpos]; nlinarith

theorem errExp_le_maxExp {k : ℕ} (hk : 1 ≤ k) {α κ τ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hκ : 0 ≤ κ)
    (hτ0 : 0 ≤ τ) (hτκ : τ ≤ κ) : errExp k α κ τ ≤ maxExp k α κ := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  obtain ⟨u, rfl⟩ : ∃ u : ℝ, κ = k * u := ⟨κ / k, by field_simp⟩
  have hu0 : 0 ≤ u := by nlinarith
  rw [maxExp_u hk]
  unfold errExp
  obtain ⟨n, hnk, hnu, hcase⟩ :=
    decomp h0 hu0 (sub_nonneg.2 hτκ) (by linarith : (k : ℝ) * u - τ ≤ k * u)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnk' : (n : ℝ) ≤ k := by exact_mod_cast hnk
  split_ifs with hα
  · rcases hcase with hA | ⟨hB1, hB2, hB3⟩
    · have hH := hitExp_le_pos hk (α := α) (τ := τ) rfl hnk (by linarith)
      have e1 : α * (k * u - τ - n * u) ≤ α * (α * u) := mul_le_mul_of_nonneg_left hA h0.le
      have e2 : 0 ≤ (1 - 2 * α) * n * u := mul_nonneg (mul_nonneg (by linarith) hn0) hu0
      linarith
    · have hH := hitExp_le_neg hk (α := α) (τ := τ) rfl (i := n + 1) hB3 (by push_cast; linarith)
      push_cast at hH
      have e1 : (1 - α) * (α * u) ≤ (1 - α) * (k * u - τ - n * u) :=
        mul_le_mul_of_nonneg_left hB1.le (by linarith)
      have e2 : 0 ≤ (1 - 2 * α) * n * u := mul_nonneg (mul_nonneg (by linarith) hn0) hu0
      linarith
  · push Not at hα
    rcases hcase with hA | ⟨hB1, hB2, hB3⟩
    · rcases Nat.lt_or_ge n k with hlt | hge
      · have hH := hitExp_le_pos hk (α := α) (τ := τ) rfl hnk (by linarith)
        have hn1 : (n : ℝ) + 1 ≤ k := by exact_mod_cast hlt
        have e1 : α * (k * u - τ - n * u) ≤ α * (α * u) := mul_le_mul_of_nonneg_left hA h0.le
        have e2 : 0 ≤ (2 * α - 1) * (k - n - 1) * u :=
          mul_nonneg (mul_nonneg (by linarith) (by linarith)) hu0
        linarith
      · have hnk2 : n = k := le_antisymm hnk hge
        subst hnk2
        have hτ' : τ = 0 := by linarith
        subst hτ'
        have hH := hitExp_le_pos hk (α := α) (τ := 0) rfl hnk (by linarith)
        have e : 0 ≤ (1 - α) ^ 2 * u := mul_nonneg (sq_nonneg _) hu0
        linarith
    · have hH := hitExp_le_neg hk (α := α) (τ := τ) rfl (i := n + 1) hB3 (by push_cast; linarith)
      push_cast at hH
      have hn1 : (n : ℝ) + 1 ≤ k := by exact_mod_cast hB3
      have e1 : (1 - α) * (α * u) ≤ (1 - α) * (k * u - τ - n * u) :=
        mul_le_mul_of_nonneg_left hB1.le (by linarith)
      have e2 : 0 ≤ (2 * α - 1) * (k - n - 1) * u :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) hu0
      linarith

theorem errExp_argmax {k : ℕ} (hk : 1 ≤ k) {α κ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hκ : 0 ≤ κ) :
    errExp k α κ (argmaxExp k α κ) = maxExp k α κ := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  obtain ⟨u, rfl⟩ : ∃ u : ℝ, κ = k * u := ⟨κ / k, by field_simp⟩
  have hu0 : 0 ≤ u := by nlinarith
  have hαu : 0 ≤ α * u := mul_nonneg h0.le hu0
  rw [maxExp_u hk, argmaxExp_u hk]
  unfold errExp
  split_ifs with hα
  · have hH : hitExp k α (k * u) (k * u - α * u) = α * u := by
      apply le_antisymm
      · have h := hitExp_le_pos hk (α := α) (τ := k * u - α * u) rfl (Nat.zero_le k)
          (by push_cast; linarith)
        push_cast at h
        linarith
      · apply le_hitExp_u hk rfl
        intro i hi
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · have := le_max_left ((k : ℝ) * u - (k * u - α * u) - ((0 : ℕ) : ℝ) * u) 0
          simp only [Nat.cast_zero] at this ⊢
          linarith
        · have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hpos
          have := le_max_right ((k : ℝ) * u - (k * u - α * u) - (i : ℝ) * u) 0
          have : 0 ≤ α * u * ((i : ℝ) - 1) := mul_nonneg hαu (by linarith)
          linarith
    rw [hH]; ring
  · push Not at hα
    have hH : hitExp k α (k * u) ((1 - α) * u) = α * k * u := by
      apply le_antisymm
      · have h1u : 0 ≤ (1 - α) * u := mul_nonneg (by linarith) hu0
        exact hitExp_le_neg hk (α := α) (τ := (1 - α) * u) rfl le_rfl (by linarith)
      · apply le_hitExp_u hk rfl
        intro i hi
        rcases Nat.lt_or_ge i k with hlt | hge
        · have hi1 : (i : ℝ) + 1 ≤ k := by exact_mod_cast hlt
          have := le_max_left ((k : ℝ) * u - (1 - α) * u - (i : ℝ) * u) 0
          have : 0 ≤ (1 - α) * ((k : ℝ) - 1 - i) * u :=
            mul_nonneg (mul_nonneg (by linarith) (by linarith)) hu0
          linarith
        · have hik : i = k := le_antisymm hi hge
          subst hik
          have := le_max_right ((i : ℝ) * u - (1 - α) * u - (i : ℝ) * u) 0
          linarith
    rw [hH]; ring

theorem maxExp_neg_iff {k : ℕ} (hk : 1 ≤ k) {α κ : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    maxExp k α κ < 0 ↔ κ < kappaK k α := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  unfold maxExp kappaK
  split_ifs with hα
  · have hA : 0 ≤ α ^ 2 / k := by positivity
    rw [lt_div_iff₀ (by linarith)]
    constructor <;> intro h <;> linarith
  · have hA : 0 ≤ (1 - α) ^ 2 / k := by positivity
    rw [lt_div_iff₀ (by linarith)]
    constructor <;> intro h <;> linarith

/-- Every error exponent on `[0, κ]` is negative iff `κ < κ_k(α)`. -/
theorem errExp_neg_iff {k : ℕ} (hk : 1 ≤ k) {α κ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hκ : 0 ≤ κ) :
    (∀ τ ∈ Set.Icc 0 κ, errExp k α κ τ < 0) ↔ κ < kappaK k α := by
  constructor
  · intro h
    have := h _ (argmaxExp_mem hk h0 h1 hκ)
    rw [errExp_argmax hk h0 h1 hκ] at this
    exact (maxExp_neg_iff hk h0 h1).1 this
  · intro h τ hτ
    exact lt_of_le_of_lt (errExp_le_maxExp hk h0 h1 hκ hτ.1 hτ.2) ((maxExp_neg_iff hk h0 h1).2 h)

/-- The term `+1` of Lemma 5.2, on `τ ∈ (κ, κ+ε]`: its exponent `(1−α)(2κ−1)` is negative for `κ < 1/2`. -/
theorem boundary_neg {α κ : ℝ} (h1 : α < 1) (hκ : κ < 1 / 2) : (1 - α) * (2 * κ - 1) < 0 :=
  mul_neg_of_pos_of_neg (by linarith) (by linarith)

/-- Unequal block weights `s_i` (the exponent share of `i` blocks) with `|s_i − i/k| ≤ δ` change the hit exponent by
at most `(1+α)κδ`. -/
theorem hitExp_perturb {k : ℕ} {α κ τ δ : ℝ} (h0 : 0 ≤ α) (hκ : 0 ≤ κ) (s : ℕ → ℝ)
    (hs : ∀ i ≤ k, |s i - i / k| ≤ δ) :
    (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
        (fun i => α * κ * s i + max (κ - τ - κ * s i) 0)
      ≤ hitExp k α κ τ + (1 + α) * κ * δ := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' (Finset.nonempty_range_add_one (n := k))
    (fun i : ℕ => α * κ * i / k + max (κ - τ - κ * i / k) 0)
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hH : hitExp k α κ τ = α * κ * j / k + max (κ - τ - κ * j / k) 0 := hjeq
  rw [hH]
  refine le_trans (Finset.inf'_le _ hj) ?_
  obtain ⟨hl, hr⟩ := abs_le.1 (hs j hjk)
  rw [show α * κ * (j : ℝ) / k = α * κ * ((j : ℝ) / k) by ring,
    show κ * (j : ℝ) / k = κ * ((j : ℝ) / k) by ring]
  generalize (j : ℝ) / k = q at hl hr ⊢
  have hδ : 0 ≤ δ := by linarith
  have m1 : max (κ - τ - κ * s j) 0 ≤ max (κ - τ - κ * q) 0 + κ * δ := by
    apply max_le
    · have := le_max_left (κ - τ - κ * q) 0
      have : κ * (q - s j) ≤ κ * δ := mul_le_mul_of_nonneg_left (by linarith) hκ
      linarith
    · have := le_max_right (κ - τ - κ * q) 0
      have : 0 ≤ κ * δ := mul_nonneg hκ hδ
      linarith
  have m2 : α * κ * s j ≤ α * κ * q + α * κ * δ := by
    have := mul_le_mul_of_nonneg_left (show s j - q ≤ δ by linarith) (mul_nonneg h0 hκ)
    linarith
  linarith

theorem kappaK_mono {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {k k' : ℕ} (hk : 1 ≤ k) (hkk' : k ≤ k') :
    kappaK k α ≤ kappaK k' α := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hkk : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
  have hk'pos : (0 : ℝ) < k' := lt_of_lt_of_le hkpos hkk
  unfold kappaK
  split_ifs
  · have hA : α ^ 2 / k' ≤ α ^ 2 / k := div_le_div_of_nonneg_left (sq_nonneg α) hkpos hkk
    have hA' : 0 ≤ α ^ 2 / k' := by positivity
    exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  · have hA : (1 - α) ^ 2 / k' ≤ (1 - α) ^ 2 / k :=
      div_le_div_of_nonneg_left (sq_nonneg _) hkpos hkk
    have hA' : 0 ≤ (1 - α) ^ 2 / k' := by positivity
    exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)

theorem tendsto_kappaK {α : ℝ} (h1 : α < 1) :
    Tendsto (fun k : ℕ => kappaK k α) atTop (𝓝 (min (1 / 2) (1 - α))) := by
  by_cases hα : α ≤ 1 / 2
  · have heq : (fun k : ℕ => kappaK k α) = fun k : ℕ => (1 - α) / (2 * (1 - α) + α ^ 2 / k) := by
      funext k; simp only [kappaK, hα, ↓reduceIte]
    have hlim : min (1 / 2) (1 - α) = (1 - α) / (2 * (1 - α) + 0) := by
      rw [min_eq_left (by linarith), add_zero, eq_div_iff (by linarith)]; ring
    rw [heq, hlim]
    exact tendsto_const_nhds.div (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _))
      (by linarith)
  · have heq : (fun k : ℕ => kappaK k α) = fun k : ℕ => (1 - α) / (1 + (1 - α) ^ 2 / k) := by
      funext k; simp only [kappaK, hα, ↓reduceIte]
    push Not at hα
    have hlim : min (1 / 2) (1 - α) = (1 - α) / (1 + 0) := by
      rw [min_eq_right (by linarith), add_zero, div_one]
    rw [heq, hlim]
    exact tendsto_const_nhds.div (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _))
      (by norm_num)

/-- If `ακ_k(α) ≤ 2θ` for every `k ≥ 1`, then `(α/2) min(1/2, 1−α) ≤ θ`. -/
theorem floor_of_forall_k {α θ : ℝ} (h1 : α < 1)
    (h : ∀ k : ℕ, 1 ≤ k → α * kappaK k α ≤ 2 * θ) : α / 2 * min (1 / 2) (1 - α) ≤ θ := by
  have hlim := (tendsto_kappaK h1).const_mul α
  have : α * min (1 / 2) (1 - α) ≤ 2 * θ :=
    le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, fun k hk => h k hk⟩)
  linarith

theorem kappaOne_closed (α : ℝ) : α * kappaOne α / 2 = α * (1 - α) / (2 * (1 + (1 - α) ^ 2)) := by
  unfold kappaOne
  have : (0 : ℝ) < 1 + (1 - α) ^ 2 := by positivity
  field_simp

/-- Auxiliary version of `window_root` (stated before its use in `counterexample_window`). -/
lemma window_root_aux {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ8 : θ < 1 / 8) :
    (1 - Real.sqrt (1 - 8 * θ)) / 2 * (1 - (1 - Real.sqrt (1 - 8 * θ)) / 2) = 2 * θ ∧
      0 ≤ (1 - Real.sqrt (1 - 8 * θ)) / 2 ∧ (1 - Real.sqrt (1 - 8 * θ)) / 2 < 1 / 2 := by
  have h8 : 0 < 1 - 8 * θ := by linarith
  have hs : Real.sqrt (1 - 8 * θ) ^ 2 = 1 - 8 * θ := Real.sq_sqrt h8.le
  have hs_pos : 0 < Real.sqrt (1 - 8 * θ) := Real.sqrt_pos.2 h8
  have hs_le : Real.sqrt (1 - 8 * θ) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-1 / 4 : ℝ) * hs
  · linarith
  · linarith

/-- Corollary 7 (counterexample window): for `θ < 1/8`, a deletion with `θ < α/2` that obeys the floor has
`α ∈ (2θ, 4θ] ∪ [1 − u(θ), 1)`, `u(θ) = (1 − √(1−8θ))/2`. -/
theorem counterexample_window {α θ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hθ8 : θ < 1 / 8)
    (hθα : θ < α / 2) (hfloor : α / 2 * min (1 / 2) (1 - α) ≤ θ) :
    (2 * θ < α ∧ α ≤ 4 * θ) ∨ 1 - (1 - Real.sqrt (1 - 8 * θ)) / 2 ≤ α := by
  by_cases hα : α ≤ 1 / 2
  · left
    rw [min_eq_left (by linarith)] at hfloor
    constructor <;> linarith
  · right
    push Not at hα
    rw [min_eq_right (by linarith)] at hfloor
    have hθ0 : 0 ≤ θ := by nlinarith [mul_pos h0 (sub_pos.2 h1)]
    obtain ⟨hu1, hu2, hu3⟩ := window_root_aux hθ0 hθ8
    generalize (1 - Real.sqrt (1 - 8 * θ)) / 2 = u at hu1 hu2 hu3 ⊢
    by_contra hc
    push Not at hc
    nlinarith [mul_pos (sub_pos.2 hc) (show 0 < α + (1 - u) - 1 by linarith)]

/-- `u(θ) = (1 − √(1−8θ))/2` is the root in `[0, 1/2)` of `u(1−u) = 2θ`, for `0 ≤ θ < 1/8`. -/
theorem window_root {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ8 : θ < 1 / 8) :
    let u := (1 - Real.sqrt (1 - 8 * θ)) / 2
    u * (1 - u) = 2 * θ ∧ 0 ≤ u ∧ u < 1 / 2 :=
  window_root_aux hθ0 hθ8

end

end DeletedPrimes
