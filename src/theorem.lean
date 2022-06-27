import basic

import order.liminf_limsup

open real filter

noncomputable theory

variables {ι : Type}
[fintype ι] [decidable_eq ι]
(q q₁ q₂ : ι → ℝ) [rnd_var q] [rnd_var q₁] [rnd_var q₂]
(n : ℕ)
(r δ ε : ℝ) [r > 0] [δ > 0] [ε > 0]
[achieves_err_exp q₁ q₂ ε q δ]
(T : ℝ) [T = (err_exp q₁ q₂ r) - r] -- consider this partition

theorem lim_log_prob_of_α_error :
lim at_top (λ n:ℕ, 1/n • log(α q₁ q₂ T)) = -err_exp q₁ q₂ r :=
begin
  -- the proof goes here
  sorry,
end