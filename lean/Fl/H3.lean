import Fl.H2

/-! Formal lane, hypothesis H3 (round 2/3, specification 1).
Window k-1 sets leverage L = (1-eta)*(-1/xp), xp = worst day of window k-1 (negative).
Premise P3: every x_t of window k is at least xp*(1+kappa); eta > kappa*(1-eta).
Q3a: every factor 1 + L*x_t >= eta - kappa*(1-eta) > 0.
Q3b: W(L)/W(0) <= (1 + L*x_ts)*exp(L*S_other) for any day ts, and, if x_ts <= xp and
eta*exp(L*S_other) < 1, W(L)/W(0) <= eta*exp(L*S_other) < 1. x_t = (m_t - c_t)/(1 + c_t). -/

namespace FL

/-- leverage chosen from the previous window's worst day xp -/
noncomputable def Lk (η xp : ℝ) : ℝ := (1 - η) * (-1 / xp)

lemma Lk_pos {η xp : ℝ} (hη1 : η < 1) (hneg : xp < 0) : 0 < Lk η xp := by
  unfold Lk
  exact mul_pos (by linarith) (div_pos_of_neg_of_neg (by norm_num) hneg)

lemma Lk_mul {η xp : ℝ} (hneg : xp < 0) : Lk η xp * xp = -(1 - η) := by
  unfold Lk
  have : xp ≠ 0 := hneg.ne
  field_simp

lemma ratio_eq {T : ℕ} (m c : Fin T → ℝ) (hc : ∀ t, 0 < 1 + c t) (L : ℝ) :
    W m c L / W m c 0 = ∏ t, (1 + L * ((m t - c t) / (1 + c t))) := by
  rw [W_eq m c hc L, W_eq m c hc 0]
  have : (∏ t, (1 + (0:ℝ) * ((m t - c t) / (1 + c t)))) = 1 := by simp
  rw [this, mul_one, mul_div_cancel_left₀ _ (Finset.prod_pos (fun t _ => hc t)).ne']

theorem h3a {T : ℕ} (x : Fin T → ℝ) (xp η κ : ℝ)
    (hη1 : η < 1) (hneg : xp < 0)
    (hP3 : ∀ t, xp * (1 + κ) ≤ x t) :
    ∀ t, η - κ * (1 - η) ≤ 1 + Lk η xp * x t := by
  intro t
  have hL := Lk_pos hη1 hneg
  have hLx := Lk_mul (η := η) hneg
  have := mul_le_mul_of_nonneg_left (hP3 t) hL.le
  have e : Lk η xp * (xp * (1 + κ)) = -(1 - η) * (1 + κ) := by rw [← mul_assoc, hLx]
  nlinarith [e, this]

theorem h3b {T : ℕ} (mc cc : Fin T → ℝ) (x : Fin T → ℝ) (xp η κ : ℝ) (ts : Fin T)
    (hη1 : η < 1) (hηκ : κ * (1 - η) < η)
    (hcc : ∀ t, 0 < 1 + cc t) (hx : ∀ t, x t = (mc t - cc t) / (1 + cc t))
    (hneg : xp < 0) (hP3 : ∀ t, xp * (1 + κ) ≤ x t) :
    W mc cc (Lk η xp) / W mc cc 0
      ≤ (1 + Lk η xp * x ts) * Real.exp (Lk η xp * ((∑ t, x t) - x ts)) := by
  have hpos : ∀ t, 0 < 1 + Lk η xp * x t := by
    intro t
    have := h3a x xp η κ hη1 hneg hP3 t
    linarith
  have hr : W mc cc (Lk η xp) / W mc cc 0 = ∏ t, (1 + Lk η xp * x t) := by
    rw [ratio_eq mc cc hcc]
    exact Finset.prod_congr rfl (fun t _ => by rw [hx t])
  rw [hr, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ts)]
  have hrest : ∏ t ∈ Finset.univ.erase ts, (1 + Lk η xp * x t)
      ≤ Real.exp (Lk η xp * ((∑ t, x t) - x ts)) := by
    calc ∏ t ∈ Finset.univ.erase ts, (1 + Lk η xp * x t)
        ≤ ∏ t ∈ Finset.univ.erase ts, Real.exp (Lk η xp * x t) := by
          have hle : ∀ t ∈ Finset.univ.erase ts,
              (1 + Lk η xp * x t) ≤ Real.exp (Lk η xp * x t) := fun t _ => by
            have := Real.add_one_le_exp (Lk η xp * x t)
            linarith
          have h0 : ∀ t ∈ Finset.univ.erase ts, 0 ≤ (1 + Lk η xp * x t) :=
            fun t _ => (hpos t).le
          first
            | exact Finset.prod_le_prod₀ h0 hle
            | exact Finset.prod_le_prod h0 hle
            | exact Finset.prod_le_prod' hle
      _ = Real.exp (Lk η xp * ((∑ t, x t) - x ts)) := by
          rw [← Real.exp_sum, ← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ ts)]
  exact mul_le_mul_of_nonneg_left hrest (hpos ts).le

theorem h3c {T : ℕ} (mc cc : Fin T → ℝ) (x : Fin T → ℝ) (xp η κ : ℝ) (ts : Fin T)
    (hη1 : η < 1) (hηκ : κ * (1 - η) < η)
    (hcc : ∀ t, 0 < 1 + cc t) (hx : ∀ t, x t = (mc t - cc t) / (1 + cc t))
    (hneg : xp < 0) (hP3 : ∀ t, xp * (1 + κ) ≤ x t)
    (hle : x ts ≤ xp)
    (hsmall : η * Real.exp (Lk η xp * ((∑ t, x t) - x ts)) < 1) :
    W mc cc (Lk η xp) / W mc cc 0 ≤ η * Real.exp (Lk η xp * ((∑ t, x t) - x ts)) ∧
    W mc cc (Lk η xp) / W mc cc 0 < 1 := by
  have hb := h3b mc cc x xp η κ ts hη1 hηκ hcc hx hneg hP3
  have hL := Lk_pos hη1 hneg
  have hLx := Lk_mul (η := η) hneg
  have h1 : 1 + Lk η xp * x ts ≤ η := by
    have := mul_le_mul_of_nonneg_left hle hL.le
    linarith
  have h2 : (1 + Lk η xp * x ts) * Real.exp (Lk η xp * ((∑ t, x t) - x ts))
      ≤ η * Real.exp (Lk η xp * ((∑ t, x t) - x ts)) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  exact ⟨le_trans hb h2, lt_of_le_of_lt (le_trans hb h2) hsmall⟩

/-- non-vacuity: round-2 instance T=3, kappa=eta=1/4, m_prev=(.04,.02,-.10), m_curr=(.05,.05,-.11),
c = 0 satisfies every hypothesis of h3a and h3b -/
example : ∃ (mc cc x : Fin 3 → ℝ) (xp η κ : ℝ) (ts : Fin 3),
    η < 1 ∧ κ * (1 - η) < η ∧ (∀ t, 0 < 1 + cc t) ∧
    (∀ t, x t = (mc t - cc t) / (1 + cc t)) ∧ xp < 0 ∧ (∀ t, xp * (1 + κ) ≤ x t) ∧
    x ts ≤ xp ∧ Lk η xp = 15/2 ∧
    W mc cc (Lk η xp) / W mc cc 0 = 33085937500 / 100000000000 := by
  refine ⟨![5/100, 5/100, -11/100], ![0, 0, 0], ![5/100, 5/100, -11/100], -1/10, 1/4, 1/4, 2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · intro t; fin_cases t <;> simp
  · intro t; fin_cases t <;> simp
  · norm_num
  · intro t; fin_cases t <;> simp <;> norm_num
  · simp; norm_num
  · simp [Lk]; norm_num
  · have hL : Lk (1/4) (-1/10) = 15/2 := by simp [Lk]; norm_num
    rw [hL]
    simp [W, R, Fin.prod_univ_three]
    norm_num

#print axioms h3a
#print axioms h3b
#print axioms h3c

end FL
