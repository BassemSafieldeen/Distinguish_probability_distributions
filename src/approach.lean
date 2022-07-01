import basic

open real

open_locale big_operators

noncomputable theory

variables {ι : Type} {n : ℕ} [fintype ι]
[fintype (ℕ → ι)] [decidable_eq ι]

/-- if output is one of these then guess q₁ -/
def Uₙ (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) (T : ℝ) :=
{ kₙ | (qₙ₁ kₙ) ≥ (qₙ₂ kₙ) * exp T }

/--  Prob. of error: guess q₁ when actually q₂ -/
def αₙ (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) (T : ℝ) : ℝ :=
∑ᶠ kₙ ∈ (Uₙ qₙ₁ qₙ₂ T), (qₙ₂ kₙ)

/-- Prob. of error: guess q₂ when actually q₁ -/
def βₙ (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) (T : ℝ) : ℝ :=
∑ᶠ kₙ ∉ (Uₙ qₙ₁ qₙ₂ T), (qₙ₁ kₙ)

def U (q₁ q₂ : ι → ℝ) (T : ℝ) :=
{ k | (q₁ k) ≥ (q₂ k) * exp T }

def α (q₁ q₂ : ι → ℝ) (T : ℝ) : ℝ :=
∑ᶠ k ∈ (U q₁ q₂ T), (q₂ k)

def β (q₁ q₂ : ι → ℝ) (T : ℝ) : ℝ :=
∑ᶠ k ∉ (U q₁ q₂ T), (q₁ k)