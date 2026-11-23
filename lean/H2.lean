import Fl.H1

/-! Formal lane, hypothesis H2 (round 2/3, specification 1).
Claim Q2: with x_t = (m_t - c_t)/(1 + c_t), caps 0 < delta < M, L > 1, L*M < 1, and at most q*T days
with |x_t| > delta (premise P2), the drag D = L log W(1) + (1-L) log W(0) - log W(L) satisfies
D >= C(delta) * RV - (C(delta) - C(M)) * q * T * M^2, C(u) = L(L-1)/(2(1+Lu)(1+u)).
Lean proves "if the hypotheses then Q2"; P2 itself is tested on data elsewhere. -/

namespace FL

noncomputable def Cc (L u : ℝ) : ℝ := L * (L - 1) / (2 * (1 + L * u) * (1 + u))

lemma one_add_R {L m c : ℝ} (hc : 0 < 1 + c) :
    1 + R L m c = (1 + c) * (1 + L * ((m - c) / (1 + c))) := by
  have h : (1 + c) * ((m - c) / (1 + c)) = m - c := by field_simp
  unfold R
  linear_combination (-L) * h

lemma W_eq {T : ℕ} (m c : Fin T → ℝ) (hc : ∀ t, 0 < 1 + c t) (z : ℝ) :
    W m c z = (∏ t, (1 + c t)) * ∏ t, (1 + z * ((m t - c t) / (1 + c t))) := by
  unfold W
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun t _ => one_add_R (hc t))

lemma logW_eq {T : ℕ} (m c : Fin T → ℝ) (hc : ∀ t, 0 < 1 + c t) (z : ℝ)
    (hz : ∀ t, 0 < 1 + z * ((m t - c t) / (1 + c t))) :
    Real.log (W m c z) = ∑ t, Real.log (1 + c t) + ∑ t, Real.log (1 + z * ((m t - c t) / (1 + c t))) := by
  rw [W_eq m c hc z, Real.log_mul (Finset.prod_pos (fun t _ => hc t)).ne'
    (Finset.prod_pos (fun t _ => hz t)).ne',
    Real.log_prod (fun t _ => (hc t).ne'), Real.log_prod (fun t _ => (hz t).ne')]

lemma Cc_anti (L δ M : ℝ) (hL : 1 < L) (hδ : 0 < δ) (hδM : δ < M) : Cc L M ≤ Cc L δ := by
  unfold Cc
  have hK : 0 ≤ L * (L - 1) := by nlinarith
  have hM : 0 < M := lt_trans hδ hδM
  have hd : 0 < 2 * (1 + L * δ) * (1 + δ) := by positivity
  apply div_le_div_of_nonneg_left hK hd
  have : (1 + L * δ) * (1 + δ) ≤ (1 + L * M) * (1 + M) := by
    nlinarith [mul_pos (sub_pos.2 hδM) (by linarith : (0:ℝ) < L + 1),
      mul_pos (sub_pos.2 hδM) (mul_pos (by linarith : (0:ℝ) < L) (by linarith : 0 < M + δ))]
  have hp : 0 < (1 + L * δ) * (1 + δ) := by positivity
  nlinarith

/-- per-day inequality: the drag of one day is at least C(u) x^2 when |x| <= u -/
lemma day_aux (L u : ℝ) (hL : 1 < L) (hu : 0 < u) (hLu : L * u < 1) :
    ∀ x ∈ Set.Icc (-u) u, Cc L u * x ^ 2 ≤ L * Real.log (1 + x) - Real.log (1 + L * x) := by
  have hu1 : u < 1 := by nlinarith
  have hK0 : 0 ≤ L * (L - 1) := by nlinarith
  have hp1 : ∀ y ∈ Set.Icc (-u) u, 0 < 1 + y := by
    intro y hy; have := hy.1; linarith
  have hp2 : ∀ y ∈ Set.Icc (-u) u, 0 < 1 + L * y := by
    intro y hy; have := hy.1; nlinarith
  set h : ℝ → ℝ := fun y => L * Real.log (1 + y) - Real.log (1 + L * y) - Cc L u * y ^ 2 with hh
  have hd : ∀ y ∈ Set.Icc (-u) u, HasDerivAt h
      (L * (1 / (1 + y)) - L / (1 + L * y) - Cc L u * (2 * y)) y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 y := (hasDerivAt_id y).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => 1 + L * y) L y := by
      simpa using ((hasDerivAt_id y).const_mul L).const_add 1
    have l1 := h1.log (hp1 y hy).ne'
    have l2 := h2.log (hp2 y hy).ne'
    have q : HasDerivAt (fun y : ℝ => Cc L u * y ^ 2) (Cc L u * (2 * y)) y := by
      simpa using ((hasDerivAt_pow 2 y).const_mul (Cc L u))
    exact ((l1.const_mul L).sub l2).sub q
  have hsign : ∀ y ∈ Set.Icc (-u) u,
      L * (1 / (1 + y)) - L / (1 + L * y) - Cc L u * (2 * y)
        = y * (L * (L - 1) / ((1 + y) * (1 + L * y)) - L * (L - 1) / ((1 + L * u) * (1 + u))) := by
    intro y hy
    have a1 := (hp1 y hy).ne'
    have a2 := (hp2 y hy).ne'
    have a3 : (1 + L * u) ≠ 0 := by nlinarith
    have a4 : (1 + u) ≠ 0 := by linarith
    unfold Cc
    field_simp
    ring
  have hk : ∀ y ∈ Set.Icc (-u) u,
      0 ≤ L * (L - 1) / ((1 + y) * (1 + L * y)) - L * (L - 1) / ((1 + L * u) * (1 + u)) := by
    intro y hy
    apply sub_nonneg.2
    have hDpos : 0 < (1 + y) * (1 + L * y) := mul_pos (hp1 y hy) (hp2 y hy)
    apply div_le_div_of_nonneg_left hK0 hDpos
    have hy1 := hy.1
    have hy2 := hy.2
    nlinarith [mul_nonneg (sub_nonneg.2 hy2) (by nlinarith : 0 ≤ (1 + L) + L * (u + y))]
  have h0 : h 0 = 0 := by simp [hh]
  have hmono : MonotoneOn h (Set.Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
    · intro y hy
      exact (hd y ⟨by linarith [hy.1], hy.2⟩).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro y hy
      exact (hd y ⟨by linarith [hy.1], hy.2.le⟩).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro y hy
      have hy' : y ∈ Set.Icc (-u) u := ⟨by linarith [hy.1], hy.2.le⟩
      rw [(hd y hy').deriv, hsign y hy']
      exact mul_nonneg hy.1.le (hk y hy')
  have hanti : AntitoneOn h (Set.Icc (-u) 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (-u) 0)
    · intro y hy
      exact (hd y ⟨hy.1, by linarith [hy.2]⟩).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro y hy
      exact (hd y ⟨hy.1.le, by linarith [hy.2]⟩).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro y hy
      have hy' : y ∈ Set.Icc (-u) u := ⟨hy.1.le, by linarith [hy.2]⟩
      rw [(hd y hy').deriv, hsign y hy']
      exact mul_nonpos_of_nonpos_of_nonneg hy.2.le (hk y hy')
  intro x hx
  have key : 0 ≤ h x := by
    rcases le_total 0 x with hx0 | hx0
    · have := hmono ⟨le_refl 0, hu.le⟩ ⟨hx0, hx.2⟩ hx0
      linarith
    · have := hanti ⟨hx.1, hx0⟩ ⟨by linarith, le_refl 0⟩ hx0
      linarith
  simp only [hh] at key
  linarith

theorem h2 {T : ℕ} (_hT : 1 ≤ T) (m c : Fin T → ℝ) (L δ M q : ℝ)
    (hL : 1 < L) (hδ : 0 < δ) (hδM : δ < M) (hLM : L * M < 1) (_hq0 : 0 ≤ q) (_hq1 : q ≤ 1)
    (hc : ∀ t, 0 < 1 + c t)
    (hM : ∀ t, |(m t - c t) / (1 + c t)| ≤ M)
    (hP2 : ((Finset.univ.filter (fun t => δ < |(m t - c t) / (1 + c t)|)).card : ℝ) ≤ q * T) :
    Cc L δ * (∑ t, ((m t - c t) / (1 + c t)) ^ 2) - (Cc L δ - Cc L M) * q * T * M ^ 2
      ≤ L * Real.log (W m c 1) + (1 - L) * Real.log (W m c 0) - Real.log (W m c L) := by
  have hM0 : 0 < M := lt_trans hδ hδM
  have hM1 : M < 1 := by nlinarith
  have hLδ : L * δ < 1 := by nlinarith
  set x : Fin T → ℝ := fun t => (m t - c t) / (1 + c t) with hx
  have hxM : ∀ t, -M ≤ x t ∧ x t ≤ M := fun t => abs_le.1 (hM t)
  have hz0 : ∀ t, 0 < 1 + (0:ℝ) * x t := by intro t; simp
  have hz1 : ∀ t, 0 < 1 + (1:ℝ) * x t := by intro t; have := (hxM t).1; linarith
  have hzL : ∀ t, 0 < 1 + L * x t := by intro t; have := (hxM t).1; nlinarith
  rw [logW_eq m c hc 1 hz1, logW_eq m c hc 0 hz0, logW_eq m c hc L hzL]
  have hsum0 : ∑ t, Real.log (1 + (0:ℝ) * x t) = 0 := by simp
  rw [hsum0]
  have hdrag : L * (∑ t, Real.log (1 + c t) + ∑ t, Real.log (1 + (1:ℝ) * x t))
        + (1 - L) * (∑ t, Real.log (1 + c t) + 0)
        - (∑ t, Real.log (1 + c t) + ∑ t, Real.log (1 + L * x t))
      = ∑ t, (L * Real.log (1 + x t) - Real.log (1 + L * x t)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [one_mul]
    ring
  rw [hdrag]
  have hCa := Cc_anti L δ M hL hδ hδM
  have hterm : ∀ t, Cc L δ * x t ^ 2 - (if δ < |x t| then (Cc L δ - Cc L M) * M ^ 2 else 0)
      ≤ L * Real.log (1 + x t) - Real.log (1 + L * x t) := by
    intro t
    by_cases hb : δ < |x t|
    · rw [if_pos hb]
      have h1 := day_aux L M hL hM0 hLM (x t) ⟨(hxM t).1, (hxM t).2⟩
      have hx2 : x t ^ 2 ≤ M ^ 2 := by
        have := hM t
        nlinarith [abs_nonneg (x t), sq_abs (x t)]
      nlinarith [mul_le_mul_of_nonneg_left hx2 (sub_nonneg.2 hCa)]
    · rw [if_neg hb]
      push_neg at hb
      have h1 := day_aux L δ hL hδ hLδ (x t) ⟨(abs_le.1 hb).1, (abs_le.1 hb).2⟩
      linarith
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hterm t)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul] at hsum
  have hcard : (Finset.univ.filter (fun t => δ < |x t|)).card = (Finset.univ.filter
      (fun t => δ < |(m t - c t) / (1 + c t)|)).card := rfl
  rw [hcard] at hsum
  have hnn : 0 ≤ (Cc L δ - Cc L M) * M ^ 2 := mul_nonneg (sub_nonneg.2 hCa) (sq_nonneg M)
  have := mul_le_mul_of_nonneg_left hP2 hnn
  nlinarith

#print axioms h2

end FL
