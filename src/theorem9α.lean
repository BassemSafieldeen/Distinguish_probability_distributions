import analysis.special_functions.pow
import analysis.special_functions.complex.log

import approach_one_symbol
import theorem4

open real set fintype

open_locale big_operators

noncomputable theory

variables {ι : Type} [fintype ι] [decidable_eq ι]
(q₁ q₂ : ι → ℝ) [rnd_var_1 q₁] [rnd_var_1 q₂]
(r T : ℝ) [hT : T = err_exp_1 q₁ q₂ r - r]

lemma indicator_le_of_indicator_eq_1 (q₁ q₂ : ι → ℝ) (r T : ℝ) {k} {s} :
(Φ q₁ q₂ T k) = 1 → (Φ q₁ q₂ T k) ≤ (M q₁ q₂ k r s) :=
begin
  intro eq_1,
  rw [eq_1, M],
  apply one_le_rpow,
  have k_mem_U : k ∈ U q₁ q₂ T,
    by exact (indicator_eq_one_iff_mem ℝ).mp eq_1,
  have mem_ineq : (q₁ k) ≥ (q₂ k) * exp T, {
    sorry,
  },
  have hT : T = err_exp_1 q₁ q₂ r - r, { sorry },
  rw hT at mem_ineq,
  sorry,
  have s_nonneg : s ≥ 0, sorry,
  have one_add_s_nonneg : 1+s ≥ 0, linarith,
  exact div_nonneg s_nonneg one_add_s_nonneg,
end

lemma indicator_zero_of_not_one {k} :
¬ (Φ q₁ q₂ T k = 1) → (Φ q₁ q₂ T k = 0) :=
begin
  intro H, rw [Φ, indicator] at *,
  by_contradiction H1, finish,
end

lemma indicator_le (r T : ℝ) {s : ℝ} :
∀ k, (Φ q₁ q₂ T k) ≤ (M q₁ q₂ k r s) :=
begin
  intro k, by_cases (Φ q₁ q₂ T k) = 1,
  apply indicator_le_of_indicator_eq_1, exact h,
  rw indicator_zero_of_not_one,
  rw M,
  apply rpow_nonneg_of_nonneg,
  apply mul_nonneg, apply div_nonneg;
  apply rnd_var_1.probs_nonneg,
  simp only [le_of_lt, exp_pos],
  exact h,
end

lemma indicator_mul_q₂_le (r T : ℝ) {s : ℝ} :
∀ k, (q₂ k) * (Φ q₁ q₂ T k) ≤ (q₂ k) * (M q₁ q₂ k r s) :=
λ k, mul_le_mul_of_nonneg_left (indicator_le q₁ q₂ r T k) (rnd_var_1.probs_nonneg k)

lemma sum_indicator_le (r T : ℝ) {s : ℝ} :
∑ k, (q₂ k) * (Φ q₁ q₂ T k) ≤ ∑ k, (q₂ k) * (M q₁ q₂ k r s) :=
sum_mono (indicator_mul_q₂_le q₁ q₂ r T)

theorem prob_α_le (r T : ℝ) :
∀ s, α q₁ q₂ T ≤ ∑ k, (q₂ k) * (M q₁ q₂ k r s) :=
λ s, by simp only [α, sum_indicator_le q₁ q₂ r T]

theorem a_le_c {b : ℝ → ℝ} {a c : ℝ} :
(∀ s, a ≤ b s) → (∃ s, c = b s) → (a ≤ c) :=
by finish

/-- Thm. 9 in Blahut1974: r-close to q₁ → farther from q₂ → smaller error α -/
theorem prob_α_error_le :
α q₁ q₂ T ≤ exp(-err_exp_1 q₁ q₂ r) :=
a_le_c (prob_α_le q₁ q₂ r T) (exp_err_exp_of_s q₁ q₂ r T)