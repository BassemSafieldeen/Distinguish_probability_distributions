import util
import approach_one_symbol

open real set rnd_var_1

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
{ k | exp(-ε) < q₁ k / q k * exp(r) }

def UB (q q₁ q₂ : ι → ℝ) [rnd_var_1 q] [rnd_var_1 q₁] [rnd_var_1 q₂] (r ε : ℝ) :=
{ k | exp(-ε) < q₂ k / q k * exp(err_exp_1 q₁ q₂ r) }

def UTA (q q₁ q₂ : ι → ℝ) [rnd_var_1 q] [rnd_var_1 q₁] [rnd_var_1 q₂] (r ε : ℝ) :=
{ k | abs(log( q k / q₁ k * exp(-r) )) ≥ ε }

def UTB (q q₁ q₂ : ι → ℝ) [rnd_var_1 q] [rnd_var_1 q₁] [rnd_var_1 q₂] (r ε : ℝ) :=
{ k | abs(log( q k / q₂ k * exp(-err_exp_1 q₁ q₂ r) )) ≥ ε }

variables
{q q₁ q₂ : ι → ℝ} [rnd_var_1 q] [rnd_var_1 q₁] [rnd_var_1 q₂]
{r T ε : ℝ} (HT : T = err_exp_1 q₁ q₂ r - r)
(Hr : r = ∑ k, q k * log(q k / q₁ k)) -- let q achieve err_exp_1(r)
(Hε : ε > 0)
(Herr_exp : err_exp_1 q₁ q₂ r = ∑ k, q k * log(q k / q₂ k))

@[simp] lemma exp_ne_zero : exp(r) ≠ 0 := ne_of_gt (exp_pos r)
@[simp] lemma q_pos       : ∀ k, 0 < q k := λk, probs_pos k
@[simp] lemma q₁_pos      : ∀ k, 0 < q₁ k := λk, probs_pos k
@[simp] lemma q₂_pos      : ∀ k, 0 < q₂ k := λk, probs_pos k

@[simp]
lemma q_div_q₁_ne_zero {k} :
  q k / q₁ k ≠ 0 :=
by {apply ne_of_gt, rw [(lt_div_iff _), zero_mul]; simp}

lemma in_U₂ :
  (∑ k, q k * (Φ (U₂ q q₁ q₂ r ε) k)) * exp(-(r + ε)) ≤ ∑ k, q₁ k * (Φ (U₂ q q₁ q₂ r ε) k) :=
begin
  rw finset.sum_mul,
  apply finset.sum_le_sum,
  intros k hk,
  rw [Φ, indicator],
  by_cases (k ∈ U₂ q q₁ q₂ r ε), simp only [h], simp,
  rw U₂ at h, norm_num at h,
  apply le_of_lt, rw add_comm, exact h.2,
  simp only [h], simp,
end

lemma in_U₁ :
(∑ k, q k * (Φ (U₁ q q₁ q₂ r ε) k))
                                   ≤ (∑ k, (q₂ k) * (Φ (U₁ q q₁ q₂ r ε) k)) * exp(err_exp_1 q₁ q₂ r + ε) :=
begin
  rw finset.sum_mul,
  apply finset.sum_le_sum,
  intros k hk,
  rw [Φ, indicator],
  by_cases (k ∈ U₁ q q₁ q₂ r ε), simp only [h], simp,
  rw U₁ at h, norm_num at h,
  apply le_of_lt,
  rw ← mul_lt_mul_right (exp_pos (-err_exp_1 q₁ q₂ r - ε)),
  rw mul_assoc, rw ← exp_add _ _, ring_nf, rw exp_zero, rw one_mul,
  rw ← tactic.ring.add_neg_eq_sub, rw add_comm, rw mul_comm, exact h.2,
  simp only [h], simp,
end

include HT

lemma U₁_subset_U :
  (U₁ q q₁ q₂ r ε) ⊆ (U q₁ q₂ T) :=
begin
  rw [U, U₁], intros k Hk, norm_num,
  have qk_pos : ∀ k, 0 < q k, by exact (probs_pos),
  rw ← div_le_div_right (qk_pos k),
  rw [mul_comm, ← mul_div, mul_comm, HT], exact Hk.1,
end

lemma U₂_subset_Uc :
  (U₂ q q₁ q₂ r ε) ⊆ (U q₁ q₂ T)ᶜ :=
begin
  rw [U, U₂], intros k Hk, norm_num,
  have qk_pos : ∀ k, 0 < q k, by exact (probs_pos),
  rw ← div_lt_div_right (qk_pos k),
  rw [mul_comm, ← mul_div, mul_comm, HT], exact Hk.1,
end

omit HT

lemma U₁_union_U₂_eq_UA_inter_UB :
  (U₁ q q₁ q₂ r ε) ∪ (U₂ q q₁ q₂ r ε) = (UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε) :=
begin
  rw [union_def, inter_def], ext k,

  let a : Prop := exp (-ε) < q₁ k / q k * exp r,
  let b : Prop := exp (-ε) < q₂ k / q k * exp (err_exp_1 q₁ q₂ r),
  let c : Prop :=  q₂ k / q k * exp(err_exp_1 q₁ q₂ r) ≤ q₁ k / q k * exp(r),

  have a_def : a ↔ exp (-ε) < q₁ k / q k * exp r, refl,
  have b_def : b ↔ exp (-ε) < q₂ k / q k * exp (err_exp_1 q₁ q₂ r), refl,
  have c_def : c ↔ q₂ k / q k * exp(err_exp_1 q₁ q₂ r) ≤ q₁ k / q k * exp(r), refl,

  have a_rw     : a ↔ q k * exp (-r + -ε) < q₁ k, {
    rw ← mul_lt_mul_right (exp_pos(r)),
    rw [mul_assoc, ← exp_add, add_comm, ← add_assoc, add_neg_self, zero_add],
    have q_inv_pos : 0 < (q k)⁻¹, by exact inv_pos.mpr (q_pos k),
    rw [← mul_lt_mul_right q_inv_pos, mul_assoc, mul_comm],
    rw [← div_eq_mul_inv, div_mul, div_self, div_one],
    rw [mul_assoc, mul_comm (exp (r)) (q k)⁻¹],
    rw [← mul_assoc, ← div_eq_mul_inv],
    exact ne_of_gt (q_pos k),
  },
  have b_rw     : b ↔ q k * exp (-ε + -err_exp_1 q₁ q₂ r) < q₂ k, {
    rw ← mul_lt_mul_right (exp_pos(err_exp_1 q₁ q₂ r)),
    rw [mul_assoc, ← exp_add, add_assoc, neg_add_self, add_zero],
    have q_inv_pos : 0 < (q k)⁻¹, by exact inv_pos.mpr (q_pos k),
    rw [← mul_lt_mul_right q_inv_pos, mul_assoc, mul_comm],
    rw [← div_eq_mul_inv, div_mul, div_self, div_one],
    rw [mul_assoc, mul_comm (exp (err_exp_1 q₁ q₂ r)) (q k)⁻¹],
    rw [← mul_assoc, ← div_eq_mul_inv],
    exact ne_of_gt (q_pos k),
  },
  have c_rw     : c ↔ q₂ k / q k * exp (err_exp_1 q₁ q₂ r - r) ≤ q₁ k / q k, {
    rw ← mul_le_mul_right (exp_pos(r)),
    rw [mul_assoc, ← exp_add], simp,
  },
  have not_c_rw : ¬ c ↔ q₁ k / q k < q₂ k / q k * exp (err_exp_1 q₁ q₂ r - r), by rw [c_rw, not_le],

  have a_and_b_rw : (c ∧ b ∧ a) ∨ (¬ c ∧ b ∧ a) ↔ (a ∧ b), by {split, tauto, tauto},

  have c_and_b_rw     :   c ∧ b ↔ c ∧ b ∧ a, {
    rw [a_def, b_def, c_def],
    split, intro H,
    split, exact H.1, split, exact H.2,
    calc exp(-ε) < q₂ k / q k * exp (err_exp_1 q₁ q₂ r) : H.2
             ... ≤ q₁ k / q k * exp r : H.1,
    intro H, exact ⟨H.1, H.2.1⟩,
  },
  have not_c_and_b_rw : ¬ c ∧ a ↔ ¬ c ∧ b ∧ a, {
    rw [a_def, b_def, c_def, not_le],
    split,
    intro H, split, exact H.1, split,
    calc exp (-ε) < q₁ k / q k * exp r : H.2
              ... < q₂ k / q k * exp (err_exp_1 q₁ q₂ r) : H.1,
    exact H.2,
    intro H, exact ⟨H.1, H.2.2⟩,
  },
  split,
  {
    intro H, rw [U₁, U₂] at H, rw [UA, UB],
    norm_num, norm_num at H,
    rwa [← a_and_b_rw, ← c_and_b_rw, ← not_c_and_b_rw, not_c_rw, c_rw, a_rw, b_rw],
  },
  {
    intro H, rw [UA, UB] at H, rw [U₁, U₂],
    norm_num, norm_num at H,
    rw [← b_rw, ← a_rw, ← c_rw, ← not_c_rw, c_and_b_rw, not_c_and_b_rw],
    exact a_and_b_rw.mpr H,
  },
end

lemma sum_inter_ge :
  ∑ k, q k * (Φ ((UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε)) k) 
          ≥ 1 - ∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) - ∑ k, q k * (Φ (UB q q₁ q₂ r ε)ᶜ k) :=
begin
  calc ∑ k, q k * (Φ ((UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε)) k) 
                  = 1 - ∑ k, q k * (Φ ((UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε))ᶜ k) : by rw in_self_or_in_compl
              ... = 1 - ∑ k, q k * (Φ ((UA q q₁ q₂ r ε)ᶜ ∪ (UB q q₁ q₂ r ε)ᶜ) k) : by rw compl_inter
              ... ≥ 1 - (∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) + ∑ k, q k * (Φ (UB q q₁ q₂ r ε)ᶜ k)) : by {apply sub_le_sub_left, exact add_ge_sum_union q_pos}
              ... ≥ 1 - ∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) - ∑ k, q k * (Φ (UB q q₁ q₂ r ε)ᶜ k) : by linarith,
end

lemma log_lt_of_lt_div_mul {k} :
  exp (-ε) < q₁ k / q k * exp r → log(q k / q₁ k * exp(-r)) < ε :=
begin
  intro H,
  rw [← exp_lt_exp, exp_log],
  rw [← mul_lt_mul_left (exp_pos _), ← (exp_add _ _)],
  rw [neg_add_self, exp_zero, ← mul_assoc],
  rw ← mul_lt_mul_right (exp_pos _),
  rw [mul_assoc, ← (exp_add _ _)],
  rw [neg_add_self, exp_zero, mul_one, one_mul, mul_div],
  rw div_lt_iff (q₁_pos k),
  have qk_pos : 0 < q k, by exact probs_pos k,
  rw [← div_lt_div_right (qk_pos), ← mul_div],
  rwa [div_self, mul_one, ← mul_div, mul_comm],
  exact ne_of_gt qk_pos, assumption,
  rw [zero_lt_mul_right, lt_div_iff, zero_mul],
  simp, simp, apply exp_pos,
end

lemma lt_div_mul_of_log_lt {k} :
  log(q k / q₁ k * exp(-r)) < ε → exp (-ε) < q₁ k / q k * exp r :=
begin
  intro H,
  rw ← mul_lt_mul_left (exp_pos $ ε),
  rw [← (exp_add _ _), add_neg_self, exp_zero],
  rw [← mul_assoc, ← mul_lt_mul_right (exp_pos $ -r)],
  rw [mul_assoc, ← (exp_add _ _), add_neg_self, exp_zero, mul_one, one_mul],
  rw mul_div,
  have qk_pos : 0 < q k, by exact probs_pos k,
  rw [lt_div_iff (qk_pos), ← div_lt_iff _],
  rw [← mul_div, mul_comm, ← log_lt_log_iff],
  rwa log_exp,
  rw zero_lt_mul_right (exp_pos $ -r),
  rw [lt_div_iff, zero_mul],
  simp, simp, apply exp_pos, simp,
end

lemma UA_rw :
  UA q q₁ q₂ r ε = { k | log(q k / q₁ k * exp(-r)) < ε } :=
by {ext, exact ⟨log_lt_of_lt_div_mul, lt_div_mul_of_log_lt⟩}

include Hr

lemma UTA_rw :
  UTA q q₁ q₂ r ε = { k | abs(log(q k / q₁ k) - ∑ k, q k * log(q k / q₁ k)) ≥ ε } :=
begin
  rw UTA, ext k, split,
  intro H, norm_num at *, rwa [log_mul, log_exp, Hr] at H, simp, simp,
  intro H, norm_num at *, rwa [log_mul, log_exp, Hr], simp, simp,
end

omit Hr
include Herr_exp

lemma UTB_rw :
  UTB q q₁ q₂ r ε = { k | abs(log(q k / q₂ k) - ∑ k, q k * log(q k / q₂ k)) ≥ ε } :=
begin
  rw UTB, ext k, split,
  intro H, norm_num at H, rwa [Herr_exp, log_mul, log_exp] at H, simp, simp,
  intro H, norm_num, rwa [Herr_exp, log_mul, log_exp], simp, simp,
end

omit Herr_exp

lemma UB_rw :
  UB q q₁ q₂ r ε = { k | log(q k / q₂ k * exp(-err_exp_1 q₁ q₂ r)) < ε } :=
by {ext, exact ⟨log_lt_of_lt_div_mul, lt_div_mul_of_log_lt⟩}

lemma UAc_subset_UTA :
  (UA q q₁ q₂ r ε)ᶜ ⊆ (UTA q q₁ q₂ r ε) :=
by {rw [UTA, UA_rw, gt_compl_le], apply subset_abs}

lemma sum_UAc_le_sum_UTA :
  ∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) ≤ ∑ k, q k * (Φ (UTA q q₁ q₂ r ε) k) :=
sum_le_of_subset q_pos (UAc_subset_UTA)

variables {σ₁ σ₂ : ℝ}
(Hσ₁ : σ₁ = Var q (λk, log(q k / q₁ k)))
(Hσ₂ : σ₂ = Var q (λk, log(q k / q₂ k)))

include Hσ₁ Hr Hε

lemma sum_UTA_le_var :
  ∑ k, q k * (Φ (UTA q q₁ q₂ r ε) k) ≤ σ₁/(ε^2) := 
by {rw [UTA_rw Hr, Hσ₁], apply Chebyshevs_ineq, assumption}

lemma sum_UAc_le_var :
  ∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) ≤ σ₁/(ε^2) :=
le_trans sum_UAc_le_sum_UTA (sum_UTA_le_var Hr Hε Hσ₁)

omit Hr Hε Hσ₁

lemma UBc_subset_UTB :
  (UB q q₁ q₂ r ε)ᶜ ⊆ (UTB q q₁ q₂ r ε) :=
by {rw [UTB, UB_rw, gt_compl_le], apply subset_abs}

lemma sum_UBc_le_sum_UTB :
  ∑ k, q k * (Φ (UB q q₁ q₂ r ε)ᶜ k) ≤ ∑ k, q k * (Φ (UTB q q₁ q₂ r ε) k) :=
sum_le_of_subset q_pos (UBc_subset_UTB)

include Hσ₂ Herr_exp Hε

lemma sum_UTB_le_var :
  ∑ k, q k * (Φ (UTB q q₁ q₂ r ε) k) ≤ σ₂/(ε^2) := 
by {rw [UTB_rw, Hσ₂], apply Chebyshevs_ineq, assumption, exact Herr_exp}

lemma sum_UBc_le_var  :
  ∑ k, q k * (Φ (UB q q₁ q₂ r ε)ᶜ k) ≤ σ₂/(ε^2) :=
le_trans sum_UBc_le_sum_UTB (sum_UTB_le_var Hε Herr_exp Hσ₂)

include Hσ₁ Hr

lemma sum_UA_inter_UB_ge :
  ∑ k, q k * (Φ ((UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε)) k) ≥ 1 - (σ₁ + σ₂)/ε^2 :=
begin
  calc ∑ k, q k * (Φ ((UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε)) k)
          ≥ 1 - ∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) - ∑ k, q k * (Φ (UB q q₁ q₂ r ε)ᶜ k) : sum_inter_ge
      ... ≥ 1 - ∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) - σ₂/(ε^2) : by apply sub_le_sub_left (sum_UBc_le_var Hε Herr_exp Hσ₂)
      ... ≥ 1 - σ₂/(ε^2) - ∑ k, q k * (Φ (UA q q₁ q₂ r ε)ᶜ k) : by linarith
      ... ≥ 1 - σ₂/(ε^2) - σ₁/(ε^2) : by apply sub_le_sub_left (sum_UAc_le_var Hr Hε Hσ₁)
      ... ≥ 1 - (σ₁/(ε^2) + σ₂/(ε^2)) : by linarith
      ... = 1 - (σ₁ + σ₂)/ε^2 : by simp only [add_div],
end

lemma sum_U2_ge_of_sum_U1_le {γ} :
  ∑ k, q k * (Φ (U₁ q q₁ q₂ r ε) k) ≤ γ
      → ∑ k, q k * (Φ (U₂ q q₁ q₂ r ε) k) + γ ≥ 1 - (σ₁ + σ₂)/ε^2 :=
begin
  intro H,
  calc ∑ k, q k * (Φ (U₂ q q₁ q₂ r ε) k) + γ
            ≥ ∑ k, q k * (Φ (U₂ q q₁ q₂ r ε) k) + ∑ k, q k * (Φ (U₁ q q₁ q₂ r ε) k) : by apply add_le_add_left H
        ... ≥ ∑ k, q k * (Φ ((U₂ q q₁ q₂ r ε) ∪ (U₁ q q₁ q₂ r ε)) k) : add_ge_sum_union q_pos
        ... = ∑ k, q k * (Φ ((UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε)) k) : by rw [union_comm, U₁_union_U₂_eq_UA_inter_UB]
        ... ≥ 1 - (σ₁ + σ₂)/ε^2 : sum_UA_inter_UB_ge Hr Hε Herr_exp Hσ₁ Hσ₂,
end

include HT

/-- Thm. 10 in Blahut1974 -/
theorem prob_of_α_error_ge {γ > 0} : 
  β q₁ q₂ T ≤ γ * exp(-(r + ε))
  → α q₁ q₂ T ≥ exp(-(err_exp_1 q₁ q₂ r + ε)) * (1 - (σ₁ + σ₂)/(ε^2) - γ) :=
begin
  intros Hβ,
  have Hγ : (∑ k, q k * (Φ (U₂ q q₁ q₂ r ε) k)) * exp(-(r + ε)) ≤ γ * exp(-(r + ε)), {
    calc (∑ k, q k * (Φ (U₂ q q₁ q₂ r ε) k)) * exp(-(r + ε)) 
                ≤ ∑ k, q₁ k * (Φ (U₂ q q₁ q₂ r ε) k) : in_U₂
            ... ≤ ∑ k, q₁ k * (Φ (U q₁ q₂ T)ᶜ k) : sum_le_of_subset q₁_pos (U₂_subset_Uc HT)
            ... = β q₁ q₂ T : by rw β
            ... ≤ γ * exp(-(r + ε)) : by assumption,
  },
  have γ_gt : ∑ k, q k * (Φ (U₂ q q₁ q₂ r ε) k) ≤ γ, {
    exact (mul_le_mul_right (exp_pos (-(r + ε)))).mp Hγ,
  },
  have : α q₁ q₂ T * exp(err_exp_1 q₁ q₂ r + ε) + γ ≥ 1 - (σ₁ + σ₂)/ε^2, {
    calc α q₁ q₂ T * exp(err_exp_1 q₁ q₂ r + ε) + γ
               = (∑ k, q₂ k * (Φ (U q₁ q₂ T) k)) * exp(err_exp_1 q₁ q₂ r + ε) + γ : by rw α
           ... ≥ (∑ k, q₂ k * (Φ (U₁ q q₁ q₂ r ε) k)) * exp(err_exp_1 q₁ q₂ r + ε) + γ : mul_add_ge_of_ge (exp_pos _) (sum_le_of_subset q₂_pos (U₁_subset_U HT))
           ... ≥ ∑ k, q k * (Φ (U₁ q q₁ q₂ r ε) k) + γ : by apply add_le_add_right in_U₁
           ... ≥ ∑ k, q k * (Φ (U₁ q q₁ q₂ r ε) k) + ∑ k, q k * (Φ (U₂ q q₁ q₂ r ε) k) : by apply add_le_add_left γ_gt
           ... ≥ ∑ k, q k * (Φ ((U₁ q q₁ q₂ r ε) ∪ (U₂ q q₁ q₂ r ε)) k) : add_ge_sum_union q_pos
           ... = ∑ k, q k * (Φ ((UA q q₁ q₂ r ε) ∩ (UB q q₁ q₂ r ε)) k) : by rw U₁_union_U₂_eq_UA_inter_UB
           ... ≥ 1 - (σ₁ + σ₂)/(ε^2) : by {apply sum_UA_inter_UB_ge; assumption},
  },
  have : α q₁ q₂ T * exp(err_exp_1 q₁ q₂ r + ε) ≥ 1 - (σ₁ + σ₂)/ε^2 - γ, {
    apply sub_le_iff_le_add.mpr this,
  },
  apply (mul_le_mul_right (exp_pos((err_exp_1 q₁ q₂ r + ε)))).mp _,
  rw [mul_comm, ← mul_assoc, ← exp_add _ _, neg_add, ← add_assoc],
  rw [add_assoc, add_assoc, add_comm, add_comm (-err_exp_1 q₁ q₂ r) (-ε), ← add_assoc],
  rw [add_neg_self, zero_add, add_comm, add_neg_self, exp_zero, one_mul], exact this,
end