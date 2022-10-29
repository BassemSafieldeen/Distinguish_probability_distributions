import util
import approach_one_symbol

open real set

open_locale big_operators

noncomputable theory

variables {ι : Type} [fintype ι] [decidable_eq ι]

/-- U with q k divided on both sides and q₂ bounded further from below
{ k | (exp -ε) < q₂ k / q k * exp(err_exp_1 q₁ q₂ r) ≤ q₁ k / q k * (exp r) } -/
def U₁ (q q₁ q₂ : ι → ℝ) [rnd_var_1 q] [rnd_var_1 q₁] [rnd_var_1 q₂] (r ε : ℝ) :=
{ k | q₁ k / q k ≥ q₂ k / q k * exp(err_exp_1 q₁ q₂ r - r) ∧ q₂ k > q k * exp(-(err_exp_1 q₁ q₂ r + ε)) }

/-- Uᶜ but q₁ bounded further from below
{ k | (exp -ε) < q₁ k / q k * (exp r) < q₂ k / q k * exp(err_exp_1 q₁ q₂ r) } -/
def U₂ (q q₁ q₂ : ι → ℝ) [rnd_var_1 q] [rnd_var_1 q₁] [rnd_var_1 q₂] (r ε : ℝ) :=
{ k | q₁ k / q k < q₂ k / q k * exp(err_exp_1 q₁ q₂ r - r) ∧ q₁ k > q k * exp(-(ε + r)) }

def UA (q q₁ q₂ : ι → ℝ) [rnd_var_1 q] [rnd_var_1 q₁] [rnd_var_1 q₂] (r ε : ℝ) :=
{ k | q₁ k > q k * exp(-(err_exp_1 q₁ q₂ r + ε)) }

def UB (q q₁ q₂ : ι → ℝ) [rnd_var_1 q] [rnd_var_1 q₁] [rnd_var_1 q₂] (r ε : ℝ) :=
{ k | q₂ k > q k * exp(-(r + ε)) }

def UT (q q₁ q₂ : ι → ℝ) [rnd_var_1 q] [rnd_var_1 q₁] [rnd_var_1 q₂] (r ε : ℝ) :=
{ k | abs(log( q k / q₁ k * exp(-r) )) ≥ ε }

variables
{q q₁ q₂ : ι → ℝ} [rnd_var_1 q] [rnd_var_1 q₁] [rnd_var_1 q₂]
{r T ε : ℝ} [T = r - err_exp_1 q₁ q₂ r]
[Hr : r = ∑ k, q k * log(q k / q₁ k)] -- let q achieve err_exp_1(r)

lemma U₁_subset_U :
  (U₁ q q₁ q₂ r ε) ⊆ (U q₁ q₂ T) :=
begin
  rw U₁,
  have h1 : { k | q₁ k / q k ≥ q₂ k / q k * exp(err_exp_1 q₁ q₂ r - r) ∧ q₂ k > q k * exp(-(err_exp_1 q₁ q₂ r + ε)) }
     = { k | q₁ k / q k ≥ q₂ k / q k * exp(err_exp_1 q₁ q₂ r - r) } ∩ { k | q₂ k > q k * exp(-(err_exp_1 q₁ q₂ r + ε)) }, { tauto },
  have h2 : { k | q₁ k / q k ≥ q₂ k / q k * exp(err_exp_1 q₁ q₂ r - r) } = (U q₁ q₂ T), { sorry },
  rw h1, rw h2,
  apply inter_subset_left (U q₁ q₂ T),
end

lemma U₂_subset_Uc :
  (U₂ q q₁ q₂ r ε) ⊆ (U q₁ q₂ T)ᶜ :=
begin
  rw U₂,
  have h1 : { k | q₁ k / q k < q₂ k / q k * exp(err_exp_1 q₁ q₂ r - r) ∧ q₁ k > q k * exp(-(ε + r)) }
     = { k | q₁ k / q k < q₂ k / q k * exp(err_exp_1 q₁ q₂ r - r) } ∩ { k | q₁ k > q k * exp(-(ε + r)) }, { tauto },
  have h2 : { k | q₁ k / q k < q₂ k / q k * exp(err_exp_1 q₁ q₂ r - r) } = (U q₁ q₂ T)ᶜ, { sorry },
  rw h1, rw h2,
  apply inter_subset_left (U q₁ q₂ T)ᶜ,
end

lemma α_ge_U₁ :
  α q₁ q₂ T > exp(-(err_exp_1 q₁ q₂ r + ε)) * ∑ k, q k * (Φ (U₁ q q₁ q₂ r ε) k) :=
begin
  calc α q₁ q₂ T = ∑ k, (q₂ k) * (Φ (U q₁ q₂ T) k) : by rw α
             ... ≥ ∑ k, (q₂ k) * (Φ (U₁ q q₁ q₂ r ε) k) : sorry -- U₁_subset_U
             ... > ∑ k, q k * exp(-(err_exp_1 q₁ q₂ r + ε)) * (Φ (U₁ q q₁ q₂ r ε) k) : sorry -- rw U₁'s prop
             ... = exp(-(err_exp_1 q₁ q₂ r + ε)) * ∑ k, q k * (Φ (U₁ q q₁ q₂ r ε) k) : by sorry, -- by rw finset.mul_sum,
end

lemma β_ge_U₂ :
  β q₁ q₂ T > exp(-(r + ε)) * ∑ k, q k * (Φ (U₂ q q₁ q₂ r ε) k) :=
begin
  calc β q₁ q₂ T = ∑ k, (q₁ k) * (Φ (U q₁ q₂ T)ᶜ k) : by rw β
             ... ≥ ∑ k, (q₁ k) * (Φ (U₂ q q₁ q₂ r ε) k) : sorry -- U₂_subset_Uc
             ... > ∑ k, q k * exp(-(ε + r)) * (Φ (U₂ q q₁ q₂ r ε) k) : sorry -- rw U₂'s prop
             ... = exp(-(r + ε)) * ∑ k, q k * (Φ (U₂ q q₁ q₂ r ε) k) : sorry, -- finset.mul_sum
end

lemma U₁_union_U₂_eq_UA_inter_UB :
  (U₁ q q₁ q₂ r ε) ∪ (U₂ q q₁ q₂ r ε) = (UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε) :=
begin
  -- if k in UA ∩ UB then
  -- q₁ k > q k * exp(-(err_exp_1 q₁ q₂ r + ε)) and q₂ k > q k * exp(-(r + ε))

  -- if k in U₁ ∪ U₂
  -- U₁ = { k | q₁ k / q k ≥ q₂ k / q k * exp(err_exp_1 q₁ q₂ r - r) ∧ q₂ k > q k * exp(-(err_exp_1 q₁ q₂ r + ε)) }
  -- U₂ = { k | q₁ k / q k < q₂ k / q k * exp(err_exp_1 q₁ q₂ r - r) ∧ q₁ k > q k * exp(-(ε + r)) }
  sorry,
end

lemma sum_inter_ge :
  ∑ k, q k * (Φ ((UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε)) k) 
          ≥ 1 - ∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) - ∑ k, q k * (Φ (UB q q₁ q₂ r ε)ᶜ k) :=
begin
  calc ∑ k, q k * (Φ ((UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε)) k) 
                  = 1 - ∑ k, q k * (Φ ((UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε))ᶜ k) : by rw in_self_or_in_compl
              ... = 1 - ∑ k, q k * (Φ ((UA q q₁ q₂ r ε)ᶜ ∪ (UB q q₁ q₂ r ε)ᶜ) k) : by rw compl_inter
              ... ≥ 1 - (∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) + ∑ k, q k * (Φ (UB q q₁ q₂ r ε)ᶜ k)) : by apply sub_le_sub_left add_ge_sum_union
              ... ≥ 1 - ∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) - ∑ k, q k * (Φ (UB q q₁ q₂ r ε)ᶜ k) : by linarith,
end

lemma UT_rw :
  UT q q₁ q₂ r ε = { k | abs(log(q k / q₁ k) - ∑ k, q k * log(q k / q₁ k)) ≥ ε } :=
begin
  -- rw ← Hr,
  -- rw UT,
  -- rw log_mul
  sorry,
end

lemma UBc_rw :
  (UB q q₁ q₂ r ε)ᶜ = { k | abs(log(q k / q₂ k) - ∑ k, q k * log(q k / q₂ k)) ≥ ε } :=
begin
  calc (UB q q₁ q₂ r ε)ᶜ = { k | q₂ k > q k * exp(-(r + ε)) }ᶜ : by rw UB
                     ... = { k | q₂ k ≤ q k * exp(-(r + ε)) } : by rw gt_compl_le
                     ... = { k | 1 ≤ q k / q₂ k * exp(-(r + ε)) } : sorry -- linarith
                     ... = { k | exp(ε) ≤ q k / q₂ k * exp(-r) } : sorry -- linarith
                     ... = { k | log(q k / q₂ k) - r ≥ ε } : sorry -- log_le_log
                     ... = { k | log(q k / q₂ k) - ∑ k, q k * log(q k / q₂ k) ≥ ε } : sorry -- Hr
                     ... = { k | abs(log(q k / q₂ k) - ∑ k, q k * log(q k / q₂ k)) ≥ ε } : sorry, -- abs_of_pos
end

lemma UAc_subset_UT :
  (UA q q₁ q₂ r ε)ᶜ ⊂ (UT q q₁ q₂ r ε) :=
begin
  -- if k ∈ UAᶜ then q₁ k ≤ q k * exp(-(err_exp_1 q₁ q₂ r + ε))

  -- if k ∈ UT then abs(log( q k / q₁ k * exp(-r) )) ≥ ε
  -- or log( q k / q₁ k * exp(-r) ) ≥ ε ∧ log( q k / q₁ k * exp(-r) ) ≤ -ε
  -- or q k / q₁ k * exp(-r) ≥ exp(ε) ∧ q k / q₁ k * exp(-r) ≤ exp(-ε)
  -- or q k / q₁ k ≥ exp(r+ε) ∧ q k / q₁ k ≤ exp(r-ε)
  -- or q k ≥ q₁ k * exp(r+ε) ∧ q k ≤ q₁ k * exp(r-ε)

  -- so it's q k ≥ q₁ k * exp(r+ε) ∧ ...
  -- or q₁ k ≤ q k * exp(-(r+ε)) ∧ ...
  -- .. how are err_exp_1 q₁ q₂ r and r related? are they related by Hr
  sorry,
end

lemma sum_UAc_le_sum_UT :
  ∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) ≤ ∑ k, q k * (Φ (UT q q₁ q₂ r ε) k) :=
sum_lt_of_subset (UAc_subset_UT)

variables {σ₁ σ₂ : ℝ}

lemma sum_UT_le_var (Hσ₁ : σ₁ = Var q (λk, log(q k / q₁ k))) :
  ∑ k, q k * (Φ (UT q q₁ q₂ r ε) k) ≤ σ₁/(ε^2) := 
by {rw [UT_rw, Hσ₁], exact Chebyshevs_ineq}

lemma sum_UAc_le_var (Hσ₁ : σ₁ = Var q (λk, log(q k / q₁ k))) :
  ∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) ≤ σ₁/(ε^2) :=
le_trans sum_UAc_le_sum_UT (sum_UT_le_var Hσ₁)

lemma sum_UBc_le_var (Hσ₂ : σ₂ = Var q (λk, log(q k / q₂ k))) :
  ∑ k, q k * (Φ (UB q q₁ q₂ r ε)ᶜ k) ≤ σ₂/(ε^2) :=
by {rw [UBc_rw, Hσ₂], exact Chebyshevs_ineq}

lemma sum_UA_inter_UB_ge (Hσ₁ : σ₁ = Var q (λk, log(q k / q₁ k))) (Hσ₂ : σ₂ = Var q (λk, log(q k / q₂ k))) :
  ∑ k, q k * (Φ ((UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε)) k) ≥ 1 - (σ₁ + σ₂)/ε^2 :=
begin
  calc ∑ k, q k * (Φ ((UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε)) k)
          ≥ 1 - ∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) - ∑ k, q k * (Φ (UB q q₁ q₂ r ε)ᶜ k) : sum_inter_ge
      ... ≥ 1 - ∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) - σ₂/(ε^2) : by apply sub_le_sub_left (sum_UBc_le_var Hσ₂)
      ... ≥ 1 - σ₂/(ε^2) - ∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) : by linarith
      ... ≥ 1 - σ₂/(ε^2) - σ₁/(ε^2) : by apply sub_le_sub_left (sum_UAc_le_var Hσ₁)
      ... ≥ 1 - (σ₁/(ε^2) + σ₂/(ε^2)) : by linarith
      ... = 1 - (σ₁ + σ₂)/ε^2 : by simp only [add_div],
end

lemma sum_U2_ge_of_sum_U1_le {γ} (Hσ₁ : σ₁ = Var q (λk, log(q k / q₁ k))) (Hσ₂ : σ₂ = Var q (λk, log(q k / q₂ k))) :
  ∑ k, q k * (Φ (U₁ q q₁ q₂ r ε) k) ≤ γ
      → ∑ k, q k * (Φ (U₂ q q₁ q₂ r ε) k) + γ ≥ 1 - (σ₁ + σ₂)/ε^2 :=
begin
  intro H,
  calc ∑ k, q k * (Φ (U₂ q q₁ q₂ r ε) k) + γ
            ≥ ∑ k, q k * (Φ (U₂ q q₁ q₂ r ε) k) + ∑ k, q k * (Φ (U₁ q q₁ q₂ r ε) k) : by apply add_le_add_left H
        ... ≥ ∑ k, q k * (Φ ((U₂ q q₁ q₂ r ε) ∪ (U₁ q q₁ q₂ r ε)) k) : add_ge_sum_union
        ... = ∑ k, q k * (Φ ((UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε)) k) : by rw [union_comm, U₁_union_U₂_eq_UA_inter_UB]
        ... ≥ 1 - (σ₁ + σ₂)/ε^2 : sum_UA_inter_UB_ge Hσ₁ Hσ₂,
end

/-- Thm. 10 in Blahut1974 -/
theorem prob_of_α_error_ge {ε > 0} {γ > 0} : 
  β q₁ q₂ T ≤ γ * exp(-(r + ε))
  → α q₁ q₂ T ≥ exp(-(err_exp_1 q₁ q₂ r + ε)) * (1 - (σ₁ + σ₂)/(ε^2) - γ) :=
begin
  intros Hβ,
  sorry,
end