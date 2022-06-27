import basic

open_locale big_operators

open real

noncomputable theory

variables {ι : Type}
[fintype ι] [decidable_eq ι]
(q q₁ q₂ : ι → ℝ) [rnd_var q] [rnd_var q₁] [rnd_var q₂]
(n : ℕ)
(r δ ε : ℝ) [r > 0] [δ > 0] [ε > 0]
[achieves_err_exp q₁ q₂ ε q δ]
(T : ℝ) [T = (err_exp q₁ q₂ r) - r] -- consider this partition

variables (σ₁ σ₂ : ℝ) 
[σ₁ = ∑ k, (q k) * log(q k / q₁ k)^2 - (∑ k, (q k) * log(q k / q₁ k))^2]
[σ₂ = ∑ k, (q k) * log(q k / q₂ k)^2 - (∑ k, (q k) * log(q k / q₂ k))^2]

theorem prob_of_α_error_ge (r > 0) : 
∀ ε > 0, ∀ γ > 0,
β q₁ q₂ (err_exp q₁ q₂ r) ≤ γ * exp(-n*(r + ε))
→ α q₁ q₂ T ≥ exp(-n*((err_exp q₁ q₂ r) + ε)) * (1 - (σ₁^2 + σ₂^2)/(n*ε^2) - γ) :=
begin
  intros β β_pos γ Hγ β_le,
  -- apply prob_in_U₂_ge_of_prob_in_U₁_le
  sorry,
end

theorem log_prob_of_α_error_ge (r > 0) : 
∀ ε > 0, ∀ γ > 0,
β q₁ q₂ (err_exp q₁ q₂ r) ≤ γ * exp(-n*(r + ε))
→ 1/n • log(α q₁ q₂ T) ≥ -(err_exp q₁ q₂ r + ε) + log(1 - (σ₁^2 + σ₂^2)/(n*ε^2) - γ) / n :=
begin
  -- take the log on both sides
  sorry,
end