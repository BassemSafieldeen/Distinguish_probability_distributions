import util
import rnd_var_one_symbol

open real set

open_locale big_operators

noncomputable theory

variables {ι : Type} [fintype ι] [decidable_eq ι]

def U (q₁ q₂ : ι → ℝ) (T : ℝ) :=
{ k | (q₁ k) ≥ (q₂ k) * exp T }

def α (q₁ q₂ : ι → ℝ) (T : ℝ) : ℝ :=
∑ k, (q₂ k) * (Φ (U q₁ q₂ T) k)

def β (q₁ q₂ : ι → ℝ) (T : ℝ) : ℝ :=
∑ k, (q₁ k) * (Φ (U q₁ q₂ T)ᶜ k)