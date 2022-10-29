import approach_n_symbols

open real

open_locale big_operators

noncomputable theory

variables {ι : Type} [fintype ι]
[fintype (ℕ → ι)] [decidable_eq ι]
(q₁ q₂ : ι → ℝ) [rnd_var_1 q₁] [rnd_var_1 q₂]
(qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) [rnd_var qₙ₁] [rnd_var qₙ₂]
(n : ℕ)
[iid n qₙ₁ q₁] [iid n qₙ₂ q₂]
(r T Tₙ : ℝ)
[Tₙ = (err_exp qₙ₁ qₙ₁ r) - r] -- consider this partition

theorem prob_αₙ_le (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) [rnd_var qₙ₁] [rnd_var qₙ₂] (r Tₙ : ℝ) :
αₙ qₙ₁ qₙ₂ Tₙ ≤ exp(-err_exp qₙ₁ qₙ₂ r) := sorry -- proof like theorem9α