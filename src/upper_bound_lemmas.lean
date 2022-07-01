import approach

open real

open_locale big_operators

noncomputable theory

variables {ι : Type} [fintype ι]
[fintype (ℕ → ι)] [decidable_eq ι]
(q₁ q₂ : ι → ℝ) [rnd_var_1 q₁] [rnd_var_1 q₂]
(qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) [rnd_var qₙ₁] [rnd_var qₙ₂]
(r T Tₙ : ℝ) [r > 0]
[T = (err_exp_1 q₁ q₁ r) - r] [Tₙ = (err_exp qₙ₁ qₙ₁ r) - r] -- consider this partition

/-- Thm. 9 in Blahut1974: larger r → smaller β -/
theorem prob_of_β_error_le : β q₁ q₂ T ≤ exp(-r) := sorry

/-- Thm. 9 in Blahut1974: r-close to q₁ → farther from q₂ → smaller error α -/
theorem prob_of_α_error_le : α q₁ q₂ T ≤ exp(-err_exp_1 q₁ q₂ r) := sorry

variables (n : ℕ) [iid n qₙ₁ q₁] [iid n qₙ₂ q₂]

/-- Corollary 1 in Blahut1974 -/
theorem prob_of_α_error_le_of_iid :
αₙ qₙ₁ qₙ₂ Tₙ ≤ exp(-n * err_exp_1 q₁ q₂ r/n) := sorry
-- by simp only [prob_of_α_error_le, err_exp_of_iid]

/-- Corollary 1 in Blahut1974 -/
theorem prob_of_β_error_le_of_iid :
βₙ qₙ₁ qₙ₂ Tₙ ≤ exp(-n*r) := sorry