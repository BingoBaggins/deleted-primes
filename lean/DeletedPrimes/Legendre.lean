import DeletedPrimes.Basic

/-!
# Legendre's identity and Rankin's bound (§5.1)

For a set `S` of primes:
- `1_{𝒩_S} = 1 ∗ μ_S` (`sum_divisors_muS`) and its summed form `N_S(x) = ∑_{d≤x} μ_S(d)⌊x/d⌋` (`count_eq_sum`);
- the multiplicativity of `μ_S` used in Step 5 of §5 (`muS_mul_of_coprime`, `muS_mul_of_not_coprime`);
- the squarefree `S`-units have `∑ d^{−σ} < ∞` whenever `∑_{p∈S} p^{−σ} < ∞`
  (`summable_units_of_summable`), in particular for every `σ > α(S)` (`summable_units`);
- `a_S = ∏_{p∈S}(1 − 1/p)` (`density_eq_tprod`);
- Rankin's bounds (5.2) (`rankin_count`, `rankin_tail`);
- Legendre's identity (5.1) (`legendre`);
- `θ(S) ≤ α(S)` (`theta_le_dim`).
-/

open Real Filter Topology

namespace DeletedPrimes

noncomputable section

open Classical

variable {S : Set ℕ}

/-- `K(σ) = ∑_{d ∈ 𝒟_S} d^{−σ}`. -/
def unitSum (S : Set ℕ) (σ : ℝ) : ℝ := ∑' d : ℕ, |(muS S d : ℝ)| * (d : ℝ) ^ (-σ)

/-- The partial sum `M_S(x) = ∑_{d ≤ x} μ_S(d)`. -/
def mertensS (S : Set ℕ) (x : ℝ) : ℝ := ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ)

/-! ### Elementary properties of `μ_S` -/

theorem muS_zero (S : Set ℕ) : muS S 0 = 0 := by
  simp [muS]

theorem muS_one (S : Set ℕ) : muS S 1 = 1 := by
  simp [muS]

theorem muS_prime {p : ℕ} (hp : p.Prime) : muS S p = if p ∈ S then -1 else 0 := by
  simp [muS, hp.primeFactors, ArithmeticFunction.moebius_apply_prime hp]

theorem muS_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) : muS S (p ^ k) = 0 := by
  unfold muS
  rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
  simp [show k ≠ 1 by omega]

theorem muS_ne_zero_iff {d : ℕ} :
    muS S d ≠ 0 ↔ Squarefree d ∧ ∀ p ∈ d.primeFactors, p ∈ S := by
  unfold muS
  split_ifs with h
  · rw [ArithmeticFunction.moebius_ne_zero_iff_squarefree]; tauto
  · simp only [ne_eq, not_true_eq_false, false_iff]; tauto

theorem abs_muS_real (d : ℕ) : |(muS S d : ℝ)| = if muS S d = 0 then 0 else 1 := by
  split_ifs with h
  · simp [h]
  · have hsq := (muS_ne_zero_iff.mp h).1
    have : muS S d = ArithmeticFunction.moebius d := by
      unfold muS; rw [ite_eq_left (muS_ne_zero_iff.mp h).2]
    rw [this, ← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsq, Int.cast_one]

theorem muS_mul_of_coprime_aux {q d : ℕ} (h : Nat.Coprime q d) :
    muS S (q * d) = muS S q * muS S d := by
  unfold muS
  rw [Nat.Coprime.primeFactors_mul h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]
  by_cases hq : ∀ p ∈ q.primeFactors, p ∈ S <;> by_cases hd : ∀ p ∈ d.primeFactors, p ∈ S
  · rw [ite_eq_left (fun p hp => (Finset.mem_union.mp hp).elim (hq p) (hd p)), ite_eq_left hq,
      ite_eq_left hd]
  · rw [ite_eq_right (fun h' => hd fun p hp => h' p (Finset.mem_union_right _ hp)), ite_eq_right hd,
      mul_zero]
  · rw [ite_eq_right (fun h' => hq fun p hp => h' p (Finset.mem_union_left _ hp)), ite_eq_right hq,
      zero_mul]
  · rw [ite_eq_right (fun h' => hq fun p hp => h' p (Finset.mem_union_left _ hp)), ite_eq_right hq,
      zero_mul]

/-! ### `μ_S ∗ 1 = 1_{𝒩_S}` as arithmetic functions -/

/-- `μ_S` as an arithmetic function. -/
def muSFun (S : Set ℕ) : ArithmeticFunction ℤ := ⟨muS S, muS_zero S⟩

theorem muSFun_apply (n : ℕ) : muSFun S n = muS S n := rfl

theorem isMultiplicative_muSFun : (muSFun S).IsMultiplicative :=
  ⟨muS_one S, fun h => muS_mul_of_coprime_aux h⟩

/-- The indicator of the `S`-free integers `n ≥ 1`, as an arithmetic function. -/
def sfreeFun (S : Set ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≠ 0 ∧ SFree S n then 1 else 0, by simp⟩

theorem sfreeFun_apply (n : ℕ) : sfreeFun S n = if n ≠ 0 ∧ SFree S n then 1 else 0 := rfl

theorem sFree_mul_iff (hS : ∀ p ∈ S, p.Prime) {m n : ℕ} :
    SFree S (m * n) ↔ SFree S m ∧ SFree S n := by
  constructor
  · intro h
    exact ⟨fun p hp hdvd => h p hp (dvd_mul_of_dvd_left hdvd n),
      fun p hp hdvd => h p hp (dvd_mul_of_dvd_right hdvd m)⟩
  · rintro ⟨hm, hn⟩ p hp hdvd
    rcases (hS p hp).dvd_mul.mp hdvd with h' | h'
    · exact hm p hp h'
    · exact hn p hp h'

theorem isMultiplicative_sfreeFun (hS : ∀ p ∈ S, p.Prime) : (sfreeFun S).IsMultiplicative := by
  refine ⟨?_, fun {m n} _ => ?_⟩
  · rw [sfreeFun_apply, ite_eq_left]
    exact ⟨one_ne_zero, fun p hp hdvd => (hS p hp).one_lt.ne' (Nat.dvd_one.mp hdvd)⟩
  · simp only [sfreeFun_apply, sFree_mul_iff hS, mul_ne_zero_iff]
    by_cases hm : m ≠ 0 ∧ SFree S m <;> by_cases hn : n ≠ 0 ∧ SFree S n
    · rw [ite_eq_left hm, ite_eq_left hn, ite_eq_left ⟨⟨hm.1, hn.1⟩, hm.2, hn.2⟩, mul_one]
    · rw [ite_eq_left hm, ite_eq_right hn, ite_eq_right (fun h' => hn ⟨h'.1.2, h'.2.2⟩), mul_zero]
    · rw [ite_eq_right hm, ite_eq_right (fun h' => hm ⟨h'.1.1, h'.2.1⟩), zero_mul]
    · rw [ite_eq_right hm, ite_eq_right (fun h' => hm ⟨h'.1.1, h'.2.1⟩), zero_mul]

theorem sum_range_muS_prime_pow {p : ℕ} (hp : p.Prime) :
    ∀ k : ℕ, ∑ j ∈ Finset.range (k + 2), muS S (p ^ j) = 1 + muS S p
  | 0 => by simp [Finset.sum_range_succ, muS_one]
  | k + 1 => by
    rw [Finset.sum_range_succ, sum_range_muS_prime_pow hp k, muS_prime_pow hp (by omega), add_zero]

theorem muSFun_mul_zeta (hS : ∀ p ∈ S, p.Prime) :
    muSFun S * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) = sfreeFun S := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_muSFun.mul ArithmeticFunction.isMultiplicative_zeta.natCast) _
    (isMultiplicative_sfreeFun hS)]
  intro p i hp
  rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, sfreeFun_apply]
  simp only [muSFun_apply]
  rcases i with _ | k
  · simp [muS_one]
    exact fun q hq hdvd => (hS q hq).one_lt.ne' (Nat.dvd_one.mp hdvd)
  · rw [sum_range_muS_prime_pow hp k, muS_prime hp]
    have hne : p ^ (k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
    by_cases hpS : p ∈ S
    · rw [ite_eq_left hpS, ite_eq_right]
      · norm_num
      · rintro ⟨_, h⟩
        exact h p hpS (dvd_pow_self p (Nat.succ_ne_zero k))
    · rw [ite_eq_right hpS, ite_eq_left]
      · norm_num
      · refine ⟨hne, fun q hq hdvd => ?_⟩
        have := (Nat.prime_dvd_prime_iff_eq (hS q hq) hp).mp ((hS q hq).dvd_of_dvd_pow hdvd)
        exact hpS (this ▸ hq)

/-- `1_{𝒩_S}(n) = ∑_{d ∣ n} μ_S(d)` for `n ≥ 1`. -/
theorem sum_divisors_muS (hS : ∀ p ∈ S, p.Prime) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, muS S d = if SFree S n then 1 else 0 := by
  have := congrArg (fun f => f n) (muSFun_mul_zeta hS)
  simp only [ArithmeticFunction.coe_mul_zeta_apply, muSFun_apply, sfreeFun_apply] at this
  rw [this]
  simp [hn.ne']

/-- Legendre's identity, finite form: `N_S(x) = ∑_{d ≤ x} μ_S(d) ⌊x/d⌋`. -/
theorem count_eq_sum (hS : ∀ p ∈ S, p.Prime) (x : ℝ) :
    (count S x : ℝ) = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) * (⌊x / d⌋₊ : ℝ) := by
  have key := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (muSFun S) ⌊x⌋₊
  rw [muSFun_mul_zeta hS] at key
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := rfl
  simp only [Nat.floor_div_natCast]
  unfold count
  rw [Finset.card_filter, hIcc]
  have key' := congrArg (fun z : ℤ => (z : ℝ)) key
  simp only [sfreeFun_apply, muSFun_apply, Int.cast_sum, Int.cast_mul, Int.cast_natCast] at key'
  push_cast
  rw [← key']
  refine Finset.sum_congr rfl fun n hn => ?_
  have : n ≠ 0 := by simp at hn; omega
  simp [this]

/-- Step 5 of §5: `μ_S(qd') = μ_S(q) μ_S(d')` for coprime `q, d'`. -/
theorem muS_mul_of_coprime {q d : ℕ} (h : Nat.Coprime q d) : muS S (q * d) = muS S q * muS S d :=
  muS_mul_of_coprime_aux h

/-- Step 5 of §5: `qd' ∉ 𝒟_S` when `q ∈ 𝒟_S` and `d'` is not coprime to `q`. -/
theorem muS_mul_of_not_coprime {q d : ℕ} (h : ¬ Nat.Coprime q d) : muS S (q * d) = 0 := by
  unfold muS
  have : ArithmeticFunction.moebius (q * d) = 0 := by
    by_contra hne
    exact h (Nat.coprime_of_squarefree_mul (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hne))
  simp [this]

/-! ### Convergence of `∑_{d ∈ 𝒟_S} d^{−σ}` -/

/-- Partial sums of `∑_{d ∈ 𝒟_S} d^{−σ}` are bounded by the partial Euler product `∏ (1 + p^{−σ})`. -/
theorem sum_range_units_le (σ : ℝ) (N : ℕ) :
    ∑ d ∈ Finset.range N, |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) ≤
      ∏ p ∈ (Finset.range N).filter (· ∈ S), (1 + (p : ℝ) ^ (-σ)) := by
  set P := (Finset.range N).filter (· ∈ S)
  set A := (Finset.range N).filter (fun d => muS S d ≠ 0)
  have h1 : ∑ d ∈ Finset.range N, |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) = ∑ d ∈ A, (d : ℝ) ^ (-σ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [abs_muS_real]
    split_ifs <;> simp_all
  have h2 : ∑ d ∈ A, (d : ℝ) ^ (-σ) = ∑ d ∈ A, ∏ p ∈ d.primeFactors, (p : ℝ) ^ (-σ) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hsq := (muS_ne_zero_iff.mp (Finset.mem_filter.mp hd).2).1
    rw [Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _), ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hsq]
  have hinj : Set.InjOn Nat.primeFactors (A : Set ℕ) := by
    intro a ha b hb hab
    have ha' := (muS_ne_zero_iff.mp (Finset.mem_filter.mp ha).2).1
    have hb' := (muS_ne_zero_iff.mp (Finset.mem_filter.mp hb).2).1
    rw [← Nat.prod_primeFactors_of_squarefree ha', ← Nat.prod_primeFactors_of_squarefree hb', hab]
  have h3 : ∑ d ∈ A, ∏ p ∈ d.primeFactors, (p : ℝ) ^ (-σ) =
      ∑ T ∈ A.image Nat.primeFactors, ∏ p ∈ T, (p : ℝ) ^ (-σ) :=
    (Finset.sum_image (f := fun T : Finset ℕ => ∏ p ∈ T, (p : ℝ) ^ (-σ)) hinj).symm
  have hsub : A.image Nat.primeFactors ⊆ P.powerset := by
    intro T hT
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hdN, hd0⟩ := Finset.mem_filter.mp hd
    have hS' := (muS_ne_zero_iff.mp hd0).2
    rw [Finset.mem_powerset]
    intro p hp
    have hdpos : d ≠ 0 := by
      intro h; apply hd0; rw [h]; simp [muS]
    have hpd : p ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hdpos) (Nat.dvd_of_mem_primeFactors hp)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (lt_of_le_of_lt hpd (Finset.mem_range.mp hdN)), hS' p hp⟩
  rw [h1, h2, h3, Finset.prod_one_add]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun T _ _ =>
    Finset.prod_nonneg fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- The squarefree `S`-units have `∑_{d ∈ 𝒟_S} d^{−σ} < ∞` when `∑_{p ∈ S} p^{−σ} < ∞`. -/
theorem summable_units_of_summable {σ : ℝ}
    (h : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-σ))) :
    Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) := by
  have hnn : ∀ n : ℕ, 0 ≤ S.indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) n := fun n =>
    Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n
  refine summable_of_sum_range_le
    (c := Real.exp (∑' n, S.indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) n))
    (fun d => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)) fun N => ?_
  refine le_trans (sum_range_units_le σ N) ?_
  have hP : ∑ p ∈ (Finset.range N).filter (· ∈ S), (p : ℝ) ^ (-σ) =
      ∑ n ∈ Finset.range N, S.indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Set.indicator_apply]
  calc ∏ p ∈ (Finset.range N).filter (· ∈ S), (1 + (p : ℝ) ^ (-σ))
      ≤ ∏ p ∈ (Finset.range N).filter (· ∈ S), Real.exp ((p : ℝ) ^ (-σ)) := by
        refine Finset.prod_le_prod₀ (fun p _ => ?_) (fun p _ => ?_)
        · have := Real.rpow_nonneg (Nat.cast_nonneg p) (-σ); linarith
        · rw [add_comm]; exact Real.add_one_le_exp _
    _ = Real.exp (∑ p ∈ (Finset.range N).filter (· ∈ S), (p : ℝ) ^ (-σ)) :=
        (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' n, S.indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) n) := by
        rw [Real.exp_le_exp, hP]
        exact h.sum_le_tsum _ fun n _ => hnn n

theorem dim_set_two_mem (S : Set ℕ) :
    (2 : ℝ) ∈ {σ : ℝ | 0 ≤ σ ∧ Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-σ))} :=
  ⟨by norm_num, (Real.summable_nat_rpow.mpr (by norm_num)).indicator S⟩

theorem dim_nonneg (S : Set ℕ) : 0 ≤ dim S :=
  le_csInf ⟨2, dim_set_two_mem S⟩ fun _ h => h.1

/-- For every `σ > α(S)` the squarefree `S`-units have `∑_{d ∈ 𝒟_S} d^{−σ} < ∞`. -/
theorem summable_units {σ : ℝ} (hσ : dim S < σ) :
    Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) := by
  obtain ⟨σ₀, ⟨hσ₀0, hσ₀⟩, hlt⟩ := exists_lt_of_csInf_lt ⟨2, dim_set_two_mem S⟩ hσ
  have hσ0 : 0 < σ := lt_of_le_of_lt hσ₀0 hlt
  refine summable_units_of_summable (hσ₀.of_nonneg_of_le (fun n =>
    Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n) fun n => ?_)
  by_cases hn : n ∈ S
  · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [Nat.cast_zero, Real.zero_rpow (by linarith)]
      exact Real.rpow_nonneg le_rfl _
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpos) (by linarith)
  · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn]

/-- `∑_d |μ_S(d)/d| < ∞` when `∑_{p ∈ S} 1/p < ∞`. -/
theorem summable_abs_muS_div
    (h1 : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-1 : ℝ))) :
    Summable fun d : ℕ => |(muS S d : ℝ) / d| := by
  have := summable_units_of_summable h1
  refine this.congr fun d => ?_
  rw [Real.rpow_neg_one, abs_div, Nat.abs_cast, div_eq_mul_inv]

/-- `∑_d μ_S(d)/d` converges absolutely when `∑_{p ∈ S} 1/p < ∞`. -/
theorem summable_muS_div
    (h1 : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-1 : ℝ))) :
    Summable fun d : ℕ => (muS S d : ℝ) / d :=
  Summable.of_norm (summable_abs_muS_div h1)

/-- `a_S = ∏_{p ∈ S}(1 − 1/p)`, as a product over all primes. -/
theorem density_eq_tprod
    (h1 : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-1 : ℝ))) :
    density S = ∏' p : Nat.Primes, (if (p : ℕ) ∈ S then 1 - 1 / (p : ℝ) else 1) := by
  have hf₁ : (muS S 1 : ℝ) / ((1 : ℕ) : ℝ) = 1 := by simp [muS_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      (muS S (m * n) : ℝ) / ((m * n : ℕ) : ℝ) =
        (muS S m : ℝ) / (m : ℝ) * ((muS S n : ℝ) / (n : ℝ)) := by
    intro m n h
    rw [muS_mul_of_coprime h, Int.cast_mul, Nat.cast_mul, mul_div_mul_comm]
  have hsum : Summable fun n : ℕ => ‖(muS S n : ℝ) / (n : ℝ)‖ := summable_abs_muS_div h1
  have hf₀ : (muS S 0 : ℝ) / ((0 : ℕ) : ℝ) = 0 := by simp
  unfold density
  rw [← EulerProduct.eulerProduct_tprod (f := fun n : ℕ => (muS S n : ℝ) / (n : ℝ)) hf₁ hmul hsum
    hf₀]
  refine tprod_congr fun p => ?_
  have hp := p.prop
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, muS_one, muS_prime hp]
    split_ifs <;> ring
  · intro e he
    simp only [Finset.mem_range, not_lt] at he
    simp [muS_prime_pow hp he]

/-! ### Rankin's bounds -/

/-- Rankin's bound (5.2) for the count: `#{d ≤ Z : d ∈ 𝒟_S} ≤ K(σ) Z^σ` for `σ ≥ 0` and `Z ≥ 1`. -/
theorem rankin_count {σ : ℝ} (hsum : Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ))
    (hσ : 0 ≤ σ) {Z : ℝ} (hZ : 1 ≤ Z) :
    ∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, |(muS S d : ℝ)| ≤ unitSum S σ * Z ^ σ := by
  have hZ0 : 0 < Z := by linarith
  calc ∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, |(muS S d : ℝ)|
      ≤ ∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) * Z ^ σ := by
        refine Finset.sum_le_sum fun d hd => ?_
        obtain ⟨hd1, hdZ⟩ := Finset.mem_Icc.mp hd
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
        have hdZ' : (d : ℝ) ≤ Z := le_trans (by exact_mod_cast hdZ) (Nat.floor_le hZ0.le)
        have : 1 ≤ (d : ℝ) ^ (-σ) * Z ^ σ := by
          rw [Real.rpow_neg hd0.le, ← div_eq_inv_mul, le_div_iff₀ (Real.rpow_pos_of_pos hd0 _),
            one_mul]
          exact Real.rpow_le_rpow hd0.le hdZ' hσ
        rw [mul_assoc]
        exact le_mul_of_one_le_right (abs_nonneg _) this
    _ = (∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, |(muS S d : ℝ)| * (d : ℝ) ^ (-σ)) * Z ^ σ := by
        rw [Finset.sum_mul]
    _ ≤ unitSum S σ * Z ^ σ := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hZ0.le _)
        exact hsum.sum_le_tsum _ fun d _ =>
          mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)

/-- Rankin's bound (5.2) for the tail: `∑_{d > Z, d ∈ 𝒟_S} 1/d ≤ K(σ) Z^{σ−1}` for `σ ≤ 1` and `Z ≥ 1`. -/
theorem rankin_tail {σ : ℝ} (hsum : Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ))
    (hσ1 : σ ≤ 1) {Z : ℝ} (hZ : 1 ≤ Z) :
    ∑' d : ℕ, (if Z < d then |(muS S d : ℝ)| / d else 0) ≤ unitSum S σ * Z ^ (σ - 1) := by
  have hZ0 : 0 < Z := by linarith
  have hle : ∀ d : ℕ, (if Z < d then |(muS S d : ℝ)| / d else 0) ≤
      Z ^ (σ - 1) * (|(muS S d : ℝ)| * (d : ℝ) ^ (-σ)) := by
    intro d
    split_ifs with h
    · have hd0 : (0 : ℝ) < d := lt_trans hZ0 h
      have h2 : (d : ℝ) ^ (σ - 1) ≤ Z ^ (σ - 1) :=
        Real.rpow_le_rpow_of_nonpos hZ0 h.le (by linarith)
      have h3 : |(muS S d : ℝ)| / d = |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) * (d : ℝ) ^ (σ - 1) := by
        rw [mul_assoc, ← Real.rpow_add hd0, show -σ + (σ - 1) = -1 by ring, Real.rpow_neg_one,
          div_eq_mul_inv]
      rw [h3, mul_comm (Z ^ (σ - 1))]
      exact mul_le_mul_of_nonneg_left h2
        (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hd0.le _))
    · exact mul_nonneg (Real.rpow_nonneg hZ0.le _)
        (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
  have hnn : ∀ d : ℕ, 0 ≤ (if Z < d then |(muS S d : ℝ)| / d else 0) := by
    intro d; split_ifs
    · exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg d)
    · exact le_rfl
  have hsum' := hsum.mul_left (Z ^ (σ - 1))
  calc ∑' d : ℕ, (if Z < d then |(muS S d : ℝ)| / d else 0)
      ≤ ∑' d : ℕ, Z ^ (σ - 1) * (|(muS S d : ℝ)| * (d : ℝ) ^ (-σ)) :=
        Summable.tsum_le_tsum hle (hsum'.of_nonneg_of_le hnn hle) hsum'
    _ = unitSum S σ * Z ^ (σ - 1) := by
        rw [tsum_mul_left, unitSum, mul_comm]

/-! ### Legendre's identity -/

theorem natFloor_eq_sub_fract {u : ℝ} (hu : 0 ≤ u) : (⌊u⌋₊ : ℝ) = u - Int.fract u := by
  rw [Int.self_sub_fract, ← Int.natCast_floor_eq_floor hu, Int.cast_natCast]

theorem abs_saw_le (u : ℝ) : |saw u| ≤ 1 / 2 := by
  unfold saw
  have h0 := Int.fract_nonneg u
  have h1 := Int.fract_lt_one u
  rw [abs_le]; constructor <;> linarith

/-- Splitting `∑_d μ_S(d)/d` at `x`. -/
theorem tsum_muS_div_split (hsum : Summable fun d : ℕ => (muS S d : ℝ) / d) (x : ℝ) :
    ∑' d : ℕ, (muS S d : ℝ) / d = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) / d
      + ∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0) := by
  have hfin : ∀ d ∉ Finset.Icc 1 ⌊x⌋₊, (if x < d then 0 else (muS S d : ℝ) / d) = 0 := by
    intro d hd
    split_ifs with h
    · rfl
    · rcases Nat.eq_zero_or_pos d with rfl | hpos
      · simp
      · exfalso; apply hd
        refine Finset.mem_Icc.mpr ⟨hpos, ?_⟩
        push Not at h
        exact Nat.le_floor h
  have hB : Summable fun d : ℕ => (if x < d then 0 else (muS S d : ℝ) / d) :=
    (hasSum_sum_of_ne_finset_zero hfin).summable
  have hA : Summable fun d : ℕ => (if x < d then (muS S d : ℝ) / d else 0) := by
    refine Summable.of_norm_bounded hsum.abs fun d => ?_
    split_ifs
    · exact le_rfl
    · simp
  have hBsum : ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (if x < d then 0 else (muS S d : ℝ) / d) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) / d := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdx : (d : ℝ) ≤ x := by
      have h1 : d ≤ ⌊x⌋₊ := (Finset.mem_Icc.mp hd).2
      have hx0 : 0 ≤ x := by
        by_contra hneg
        push Not at hneg
        have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        have := (Finset.mem_Icc.mp hd).1
        omega
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le hx0)
    rw [ite_eq_right (not_lt.mpr hdx)]
  calc ∑' d : ℕ, (muS S d : ℝ) / d
      = ∑' d : ℕ, ((if x < d then (muS S d : ℝ) / d else 0)
          + (if x < d then 0 else (muS S d : ℝ) / d)) :=
        tsum_congr fun d => by split_ifs <;> simp
    _ = _ := by rw [Summable.tsum_add hA hB, tsum_eq_sum hfin, hBsum, add_comm]

/-- Legendre's identity (5.1):
`E(x) = −∑_{d≤x} μ_S(d) b(x/d) − M_S(x)/2 − x ∑_{d>x} μ_S(d)/d`. -/
theorem legendre (hS : ∀ p ∈ S, p.Prime) (hsum : Summable fun d : ℕ => (muS S d : ℝ) / d)
    {x : ℝ} (hx : 1 ≤ x) :
    err S x = -(∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) * saw (x / d)) - mertensS S x / 2
      - x * ∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0) := by
  have hx0 : 0 ≤ x := by linarith
  have hcount : (count S x : ℝ) = x * ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) / d
      - ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) * saw (x / d) - mertensS S x / 2 := by
    rw [count_eq_sum hS x, mertensS, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [natFloor_eq_sub_fract (div_nonneg hx0 (Nat.cast_nonneg d))]
    unfold saw
    ring
  unfold err density
  rw [hcount, tsum_muS_div_split hsum x]
  ring

/-- The trivial bound of §5.1: `|E(x)| ≤ 2K(σ) x^σ` for `x ≥ 1`, whenever `0 ≤ σ ≤ 1` and `K(σ) < ∞`. -/
theorem abs_err_le_rankin (hS : ∀ p ∈ S, p.Prime) {σ : ℝ}
    (hsum : Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ)) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (h1 : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-1 : ℝ))) {x : ℝ} (hx : 1 ≤ x) :
    |err S x| ≤ 2 * unitSum S σ * x ^ σ := by
  have hx0 : 0 < x := by linarith
  rw [legendre hS (summable_muS_div h1) hx]
  have hK := rankin_count hsum hσ0 hx
  have hA : |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) * saw (x / d)| ≤
      1 / 2 * (unitSum S σ * x ^ σ) := by
    calc |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) * saw (x / d)|
        ≤ ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, |(muS S d : ℝ) * saw (x / d)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, |(muS S d : ℝ)| * (1 / 2) := by
          refine Finset.sum_le_sum fun d _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_saw_le _) (abs_nonneg _)
      _ = 1 / 2 * ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, |(muS S d : ℝ)| := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ 1 / 2 * (unitSum S σ * x ^ σ) := mul_le_mul_of_nonneg_left hK (by norm_num)
  have hM : |mertensS S x| ≤ unitSum S σ * x ^ σ :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) hK
  have hT : |∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0)| ≤ unitSum S σ * x ^ (σ - 1) := by
    have hle : ∀ d : ℕ, ‖(if x < d then (muS S d : ℝ) / d else 0)‖ ≤ |(muS S d : ℝ) / d| := by
      intro d; split_ifs
      · exact le_rfl
      · simp
    have hs : Summable fun d : ℕ => ‖(if x < d then (muS S d : ℝ) / d else 0)‖ :=
      (summable_abs_muS_div h1).of_nonneg_of_le (fun _ => norm_nonneg _) hle
    calc |∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0)|
        = ‖∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0)‖ := rfl
      _ ≤ ∑' d : ℕ, ‖(if x < d then (muS S d : ℝ) / d else 0)‖ := norm_tsum_le_tsum_norm hs
      _ = ∑' d : ℕ, (if x < d then |(muS S d : ℝ)| / d else 0) := by
          refine tsum_congr fun d => ?_
          split_ifs
          · rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
          · simp
      _ ≤ unitSum S σ * x ^ (σ - 1) := rankin_tail hsum hσ1 hx
  have hxT : |x * ∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0)| ≤ unitSum S σ * x ^ σ := by
    rw [abs_mul, abs_of_pos hx0]
    calc x * |∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0)|
        ≤ x * (unitSum S σ * x ^ (σ - 1)) := mul_le_mul_of_nonneg_left hT hx0.le
      _ = unitSum S σ * x ^ σ := by
          rw [Real.rpow_sub_one hx0.ne']
          field_simp
  have e1 := abs_le.mp hA
  have e2 := abs_le.mp hM
  have e3 := abs_le.mp hxT
  rw [abs_le]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

/-- `θ(S) ≤ α(S)` for every set of primes with `∑_{p ∈ S} 1/p < ∞`. -/
theorem theta_le_dim (hS : ∀ p ∈ S, p.Prime)
    (h1 : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-1 : ℝ))) :
    theta S ≤ dim S := by
  refine le_of_forall_gt_imp_ge_of_dense fun σ hσ => ?_
  by_cases hσ1 : 1 ≤ σ
  · exact le_trans (theta_le_one S) hσ1
  · push Not at hσ1
    have hσ0 : 0 ≤ σ := le_trans (dim_nonneg S) hσ.le
    have hsum := summable_units hσ
    exact theta_le_of_isRegular hσ0
      ⟨2 * unitSum S σ, fun x hx => abs_err_le_rankin hS hsum hσ0 hσ1.le h1 hx⟩

end

end DeletedPrimes
