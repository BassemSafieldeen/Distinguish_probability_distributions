import approach_n_symbols

open real 

open_locale big_operators

noncomputable theory

variables {ι : Type} [fintype ι] [decidable_eq ι] [fintype (ℕ → ι)]
(qₙ qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) [rnd_var qₙ₁] [rnd_var qₙ₂] [rnd_var qₙ]
(r Tₙ : ℝ) [r > 0] [Tₙ = (err_exp qₙ₁ qₙ₂ r) - r] -- consider this partition

variables (δ ε : ℝ) [δ > 0] [ε > 0]
[achieves_err_exp qₙ qₙ₁ qₙ₂ r δ]

variables (σₙ₁ σₙ₂ : ℝ)
[σₙ₁ = ∑ kₙ, (qₙ kₙ) * log(qₙ kₙ / qₙ₁ kₙ)^2 - (∑ kₙ, (qₙ kₙ) * log(qₙ kₙ / qₙ₁ kₙ))^2]
[σₙ₂ = ∑ kₙ, (qₙ kₙ) * log(qₙ kₙ / qₙ₂ kₙ)^2 - (∑ kₙ, (qₙ kₙ) * log(qₙ kₙ / qₙ₂ kₙ))^2]

variables (q₁ q₂ : ι → ℝ) [rnd_var_1 q₁] [rnd_var_1 q₂]

/-- Corollary 2 in Blahut1974 -/
theorem prob_of_α_error_ge_of_iid {n : ℕ} [iid n qₙ₁ q₁] [iid n qₙ₂ q₂] : 
∀ ε > 0, ∀ γ > 0,
βₙ qₙ₁ qₙ₂ Tₙ ≤ γ * exp(-n*(r + ε))
→ αₙ qₙ₁ qₙ₂ Tₙ ≥ exp(-n*(err_exp_1 q₁ q₂ r/n + ε)) * (1 - (σₙ₁ + σₙ₂)/(n*ε^2) - γ) :=
begin
  intros ε Hε γ Hγ Hβₙ,
  sorry,
end