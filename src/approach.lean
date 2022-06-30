import basic

open real

open_locale big_operators

noncomputable theory

variables {ι : Type} {n : ℕ} [fintype ι]
[fintype (ℕ → ι)] [decidable_eq ι]

/-- if output is one of these then guess q₁ -/
def U (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) (T : ℝ) :=
{ kₙ | (qₙ₁ kₙ) ≥ (qₙ₂ kₙ) * exp T }

/--  Prob. of error: guess q₁ when actually q₂ -/
def α (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) (T : ℝ) : ℝ :=
∑ᶠ kₙ ∈ (U qₙ₁ qₙ₂ T), (qₙ₂ kₙ)

/-- Prob. of error: guess q₂ when actually q₁ -/
def β (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) (T : ℝ) : ℝ :=
∑ᶠ kₙ ∉ (U qₙ₁ qₙ₂ T), (qₙ₁ kₙ)

def U_1 (q₁ q₂ : ι → ℝ) (T : ℝ) :=
{ k | (q₁ k) ≥ (q₂ k) * exp T }

/--  Prob. of error: guess q₁ when actually q₂ -/
def α_1 (q₁ q₂ : ι → ℝ) (T : ℝ) : ℝ :=
∑ᶠ k ∈ (U_1 q₁ q₂ T), (q₂ k)

/-- Prob. of error: guess q₂ when actually q₁ -/
def β_1 (q₁ q₂ : ι → ℝ) (T : ℝ) : ℝ :=
∑ᶠ k ∉ (U_1 q₁ q₂ T), (q₁ k)