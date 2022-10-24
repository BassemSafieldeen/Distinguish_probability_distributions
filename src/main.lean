import corollary1
import corollary2

import order.liminf_limsup

open real filter

noncomputable theory

variables {ι : Type} {n : ℕ}
[fintype ι] [fintype (ℕ → ι)] [decidable_eq ι]
(qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) [rnd_var qₙ₁] [rnd_var qₙ₂]
(q₁ q₂ : ι → ℝ) [rnd_var_1 q₁] [rnd_var_1 q₂]
(r T : ℝ) [r > 0] [T = (err_exp qₙ₁ qₙ₂ r) - r] -- consider this partition

theorem lim_log_prob_of_α_error_of_iid [iid n qₙ₁ q₁] [iid n qₙ₂ q₂] :
lim at_top (λn:ℕ, 1/n • log(αₙ qₙ₁ qₙ₂ T)) = - discrimination_1 q₁ q₂ :=
begin
  sorry,
end

-- how about rw in terms of existential quantifiers