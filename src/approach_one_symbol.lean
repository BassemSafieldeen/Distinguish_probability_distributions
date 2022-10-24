import algebra.indicator_function

import rnd_var_one_symbol

open real set

open_locale big_operators

noncomputable theory

variables {ι : Type} {n : ℕ} [fintype ι] [decidable_eq ι]

def U (q₁ q₂ : ι → ℝ) (T : ℝ) :=
{ k | (q₁ k) ≥ (q₂ k) * exp T }

/-- U indicator function: if k ∈ U then 1 else 0 -/
def Φ (q₁ q₂ : ι → ℝ) (T : ℝ) (k : ι) : ℝ :=
indicator (U q₁ q₂ T) 1 k

def α (q₁ q₂ : ι → ℝ) (T : ℝ) : ℝ :=
∑ k, (q₂ k) * (Φ q₁ q₂ T k)

/-- Uᶜ indicator function: if k ∉ U then 1 else 0 -/
def Φc (q₁ q₂ : ι → ℝ) (T : ℝ) (k : ι) : ℝ :=
indicator (Uᶜ q₁ q₂ T) (λ k, 1) k

def β (q₁ q₂ : ι → ℝ) (T : ℝ) : ℝ :=
∑ k, (q₁ k) * (Φc q₁ q₂ T k)