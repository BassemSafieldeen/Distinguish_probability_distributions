import basic

open_locale big_operators

open real

noncomputable theory

variables {ι : Type}
[fintype ι] [decidable_eq ι]
{q₁ q₂ : ι → ℝ} [rnd_var q₁] [rnd_var q₂]
(r : ℝ) [r > 0] 
(T : ℝ) [T = (err_exp q₁ q₂ r) - r] -- consider this partition

/-- larger r → smaller β -/
theorem prob_of_β_error_le :
β q₁ q₂ T ≤ exp(-r) :=
begin
  /- Let s parametrize the point (r, err_exp r) -/
  let s : ℝ := _,

  calc β q₁ q₂ T = ∑ᶠ k ∉ (U q₁ q₂ T), q₁ k : by sorry
     ... ≤ ∑ᶠ k, (q₁ k) * ((q₂ k) / (q₁ k))^(1/(1+s)) * exp(T/(1+s)) : by sorry
     ... = exp(-r) : by sorry,

  sorry,
end

/-- smaller error α if q's r-close to q₁ are farther from q₂ -/
theorem prob_of_α_error_le :
α q₁ q₂ T ≤ exp(-err_exp q₁ q₂ r) :=
begin
  /- Let s parametrize the point (r, err_exp r) -/
  let s : ℝ := _,

  calc α q₁ q₂ T = ∑ᶠ k ∈ (U q₁ q₂ T), q₂ k : by sorry
     ... ≤ ∑ᶠ k, (q₂ k) * ((q₁ k) / (q₂ k))^(s/(1+s)) * exp(-T*s/(1+s)) : by sorry
     ... = exp(-err_exp q₁ q₂ r) : by sorry,

  sorry,
end

theorem log_prob_of_α_error_le :
log(α q₁ q₂ T) ≤ -err_exp q₁ q₂ r :=
begin
  -- take the log on both sides
  sorry,
end