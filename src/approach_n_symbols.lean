import algebra.indicator_function

import rnd_var_n_symbols

open real set

open_locale big_operators

noncomputable theory

variables {ι : Type} {n : ℕ} [fintype ι]
[fintype (ℕ → ι)] [decidable_eq ι]

/-- if output is one of these then guess q₁ -/
def Uₙ (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) (T : ℝ) :=
{ kₙ | (qₙ₁ kₙ) ≥ (qₙ₂ kₙ) * exp T }

/-- Uₙ indicator function: if kₙ ∈ Uₙ then 1 else 0 -/
def Φ (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) (T : ℝ) (kₙ : ℕ → ι) : ℝ :=
indicator (Uₙ qₙ₁ qₙ₂ T) 1 kₙ

/--  Prob. of error: guess qₙ₁ when actually qₙ₂ -/
def αₙ (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) (T : ℝ) : ℝ :=
∑ kₙ, (qₙ₂ kₙ) * (Φ qₙ₁ qₙ₂ T kₙ)

/-- Uₙᶜ indicator function: if kₙ ∉ Uₙ then 1 else 0 -/
def Φc (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) (T : ℝ) (kₙ : ℕ → ι) : ℝ :=
indicator (Uₙᶜ qₙ₁ qₙ₂ T) (λ kₙ, 1) kₙ

/-- Prob. of error: guess qₙ₂ when actually qₙ₁ -/
def βₙ (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) (T : ℝ) : ℝ :=
∑ kₙ, (qₙ₁ kₙ) * (Φc qₙ₁ qₙ₂ T kₙ)