import approach_n_symbols
import theorem9α

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
αₙ qₙ₁ qₙ₂ Tₙ ≤ exp(-err_exp qₙ₁ qₙ₂ r) := sorry -- proof similar to theorem9α

/-- Corollary 1 in Blahut1974 -/
theorem prob_αₙ_le_of_iid :
αₙ qₙ₁ qₙ₂ Tₙ ≤ exp(-(n * err_exp_1 q₁ q₂ (r/n))) :=
begin
  rw ← err_exp_of_iid qₙ₁ qₙ₂ q₁ q₂,
  exact prob_αₙ_le qₙ₁ qₙ₂ r Tₙ,
  exact _inst_8, exact _inst_9,
end

/-- Corollary 1 in Blahut1974 -/
theorem prob_βₙ_le_of_iid :
βₙ qₙ₁ qₙ₂ Tₙ ≤ exp(-n*r) := sorry