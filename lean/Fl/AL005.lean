import Fl.AL001

/-! Formal lane: AL-005 (signed cubic lower bound, global) and the sharp Brown-derived bound.
f(x) = L log(1+x) - log(1+L x). -/

namespace FL

lemma mono_gen (G G' : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hd : ∀ y ∈ Set.Icc a b, HasDerivAt G (G' y) y) (hs : ∀ y ∈ Set.Icc a b, 0 ≤ G' y) :
    G a ≤ G b := by
  have hmono : MonotoneOn G (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro y hy
      exact (hd y ⟨hy.1.le, hy.2.le⟩).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro y hy
      rw [(hd y ⟨hy.1.le, hy.2.le⟩).deriv]
      exact hs y ⟨hy.1.le, hy.2.le⟩
  exact hmono ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab

lemma anti_gen (G G' : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hd : ∀ y ∈ Set.Icc a b, HasDerivAt G (G' y) y) (hs : ∀ y ∈ Set.Icc a b, G' y ≤ 0) :
    G b ≤ G a := by
  have hanti : AntitoneOn G (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro y hy
      exact (hd y ⟨hy.1.le, hy.2.le⟩).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro y hy
      rw [(hd y ⟨hy.1.le, hy.2.le⟩).deriv]
      exact hs y ⟨hy.1.le, hy.2.le⟩
  exact hanti ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab

/-- global signed cubic lower bound: for L > 1 and 1 + L x > 0 -/
lemma cubic_lb (L : ℝ) (hL : 1 < L) (x : ℝ) (hx : 0 < 1 + L * x) :
    L * (L - 1) / 2 * x ^ 2 - L * (L - 1) * (L + 1) / 3 * x ^ 3
      ≤ L * Real.log (1 + x) - Real.log (1 + L * x) := by
  have hL0 : 0 < L := by linarith
  have hx1 : 0 < 1 + x := by
    by_contra hcon
    push_neg at hcon
    have hxle : x ≤ -1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hxle hL0.le]
  set G : ℝ → ℝ := fun y => L * Real.log (1 + y) - Real.log (1 + L * y)
      - L * (L - 1) / 2 * y ^ 2 + L * (L - 1) * (L + 1) / 3 * y ^ 3 with hG
  set G' : ℝ → ℝ := fun y => L * (1 / (1 + y)) - L / (1 + L * y)
      - L * (L - 1) / 2 * (2 * y) + L * (L - 1) * (L + 1) / 3 * (3 * y ^ 2) with hG'
  have hder : ∀ y, 0 < 1 + y → 0 < 1 + L * y → HasDerivAt G (G' y) y := by
    intro y hy1 hy2
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 y := (hasDerivAt_id y).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => 1 + L * y) L y := by
      simpa using ((hasDerivAt_id y).const_mul L).const_add 1
    have l1 := h1.log hy1.ne'
    have l2 := h2.log hy2.ne'
    have q2 : HasDerivAt (fun y : ℝ => L * (L - 1) / 2 * y ^ 2) (L * (L - 1) / 2 * (2 * y)) y := by
      simpa using ((hasDerivAt_pow 2 y).const_mul (L * (L - 1) / 2))
    have q3 : HasDerivAt (fun y : ℝ => L * (L - 1) * (L + 1) / 3 * y ^ 3)
        (L * (L - 1) * (L + 1) / 3 * (3 * y ^ 2)) y := by
      simpa using ((hasDerivAt_pow 3 y).const_mul (L * (L - 1) * (L + 1) / 3))
    exact ((((l1.const_mul L).sub l2).sub q2).add q3)
  have hform : ∀ y, 0 < 1 + y → 0 < 1 + L * y → G' y
      = y ^ 3 * (L * (L - 1) * (L ^ 2 + L + 1 + L * (L + 1) * y) / ((1 + y) * (1 + L * y))) := by
    intro y hy1 hy2
    have a1 := hy1.ne'
    have a2 := hy2.ne'
    simp only [hG']
    field_simp
    ring
  have hpos : ∀ y, 0 < 1 + y → 0 < 1 + L * y →
      0 ≤ L * (L - 1) * (L ^ 2 + L + 1 + L * (L + 1) * y) / ((1 + y) * (1 + L * y)) := by
    intro y hy1 hy2
    have hK : 0 ≤ L * (L - 1) := by nlinarith
    have hN : 0 < L ^ 2 + L + 1 + L * (L + 1) * y := by
      have e : L * (L + 1) * y = (L + 1) * (L * y) := by ring
      nlinarith [mul_pos (by linarith : (0:ℝ) < L + 1) hy2]
    exact div_nonneg (mul_nonneg hK hN.le) (mul_pos hy1 hy2).le
  have hG0 : G 0 = 0 := by simp [hG]
  rcases le_total 0 x with hx0 | hx0
  · have key := mono_gen G G' 0 x hx0
      (fun y hy => hder y (by linarith [hy.1]) (by nlinarith [hy.1]))
      (fun y hy => by
        have hy1 : 0 < 1 + y := by linarith [hy.1]
        have hy2 : 0 < 1 + L * y := by nlinarith [hy.1]
        rw [hform y hy1 hy2]
        exact mul_nonneg (pow_nonneg hy.1 3) (hpos y hy1 hy2))
    simp only [hG] at key hG0
    linarith
  · have key := anti_gen G G' x 0 hx0
      (fun y hy => hder y (by linarith [hy.1]) (by nlinarith [hy.1]))
      (fun y hy => by
        have hy1 : 0 < 1 + y := by linarith [hy.1]
        have hy2 : 0 < 1 + L * y := by nlinarith [hy.1]
        rw [hform y hy1 hy2]
        have hQ := hpos y hy1 hy2
        have hy3 : y ^ 3 ≤ 0 := by
          have h3 : y ^ 3 = y * y ^ 2 := by ring
          rw [h3]
          exact mul_nonpos_of_nonpos_of_nonneg hy.2 (sq_nonneg y)
        exact mul_nonpos_of_nonpos_of_nonneg hy3 hQ)
    simp only [hG] at key hG0
    linarith

lemma drag_eq2 {T : ℕ} (m c : Fin T → ℝ) (hc : ∀ t, 0 < 1 + c t) (L : ℝ) (hL : 1 < L)
    (hsol : ∀ t, 0 < 1 + L * ((m t - c t) / (1 + c t))) :
    L * Real.log (W m c 1) + (1 - L) * Real.log (W m c 0) - Real.log (W m c L)
      = ∑ t, (L * Real.log (1 + (m t - c t) / (1 + c t))
              - Real.log (1 + L * ((m t - c t) / (1 + c t)))) := by
  have hL0 : 0 < L := by linarith
  set x : Fin T → ℝ := fun t => (m t - c t) / (1 + c t) with hx
  have hz0 : ∀ t, 0 < 1 + (0:ℝ) * x t := by intro t; simp
  have hz1 : ∀ t, 0 < 1 + (1:ℝ) * x t := by
    intro t
    have h := hsol t
    by_contra hcon
    push_neg at hcon
    have hxle : x t ≤ -1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hxle hL0.le]
  rw [logW_eq m c hc 1 hz1, logW_eq m c hc 0 hz0, logW_eq m c hc L hsol]
  have hsum0 : ∑ t, Real.log (1 + (0:ℝ) * x t) = 0 := by simp
  rw [hsum0]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [one_mul]
  ring

theorem al005 {T : ℕ} (m c : Fin T → ℝ) (L τ : ℝ) (hL : 1 < L) (hc : ∀ t, 0 < 1 + c t)
    (hsol : ∀ t, 0 < 1 + L * ((m t - c t) / (1 + c t)))
    (hP : (∑ t, ((m t - c t) / (1 + c t)) ^ 3) ≤ τ * ∑ t, ((m t - c t) / (1 + c t)) ^ 2) :
    (L * (L - 1) / 2 - L * (L - 1) * (L + 1) / 3 * τ) * (∑ t, ((m t - c t) / (1 + c t)) ^ 2)
      ≤ L * Real.log (W m c 1) + (1 - L) * Real.log (W m c 0) - Real.log (W m c L) := by
  rw [drag_eq2 m c hc L hL hsol]
  have hcc : 0 ≤ L * (L - 1) * (L + 1) / 3 := by
    have : 0 ≤ L * (L - 1) := by nlinarith
    positivity
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) =>
    cubic_lb L hL ((m t - c t) / (1 + c t)) (hsol t))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  nlinarith [mul_le_mul_of_nonneg_left hP hcc]

/-- sharp per-day bound: |x| <= M gives f(x) <= S x^2 with S = f(-M)/M^2 -/
lemma sharp_day (L M : ℝ) (hL : 1 < L) (hM0 : 0 < M) (hLM : L * M < 1) :
    ∀ x ∈ Set.Icc (-M) M, L * Real.log (1 + x) - Real.log (1 + L * x)
      ≤ (L * Real.log (1 - M) - Real.log (1 - L * M)) / M ^ 2 * x ^ 2 := by
  have hM1 : M < 1 := by nlinarith
  have hL0 : 0 < L := by linarith
  have hK0 : 0 ≤ L * (L - 1) := by nlinarith
  have hp1 : ∀ y ∈ Set.Icc (-M) M, 0 < 1 + y := by
    intro y hy; have := hy.1; linarith
  have hp2 : ∀ y ∈ Set.Icc (-M) M, 0 < 1 + L * y := by
    intro y hy; have := hy.1; nlinarith
  set S := (L * Real.log (1 - M) - Real.log (1 - L * M)) / M ^ 2 with hS
  have hfM : S * M ^ 2 = L * Real.log (1 - M) - Real.log (1 - L * M) := by
    rw [hS]; field_simp
  have hSK : L * (L - 1) / 2 ≤ S := by
    have h0 := day_neg L M hL.le hM0 hLM (-M) ⟨le_refl _, by linarith⟩
    have e1 : 1 + -M = 1 - M := by ring
    have e2 : 1 + L * -M = 1 - L * M := by ring
    rw [e1, e2] at h0
    have h1 : L * (L - 1) / 2 * M ^ 2 ≤ S * M ^ 2 := by
      rw [hfM]; nlinarith [h0]
    exact le_of_mul_le_mul_right h1 (by positivity)
  set h : ℝ → ℝ := fun y => S * y ^ 2 - (L * Real.log (1 + y) - Real.log (1 + L * y)) with hh
  set h' : ℝ → ℝ := fun y => S * (2 * y) - (L * (1 / (1 + y)) - L / (1 + L * y)) with hh'
  have hd : ∀ y ∈ Set.Icc (-M) M, HasDerivAt h (h' y) y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 y := (hasDerivAt_id y).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => 1 + L * y) L y := by
      simpa using ((hasDerivAt_id y).const_mul L).const_add 1
    have l1 := h1.log (hp1 y hy).ne'
    have l2 := h2.log (hp2 y hy).ne'
    have q : HasDerivAt (fun y : ℝ => S * y ^ 2) (S * (2 * y)) y := by
      simpa using ((hasDerivAt_pow 2 y).const_mul S)
    exact q.sub ((l1.const_mul L).sub l2)
  have hform : ∀ y ∈ Set.Icc (-M) M,
      h' y = y * (2 * S - L * (L - 1) / ((1 + y) * (1 + L * y))) := by
    intro y hy
    have a1 := (hp1 y hy).ne'
    have a2 := (hp2 y hy).ne'
    have a2' : 1 + y * L ≠ 0 := by rw [mul_comm]; exact a2
    simp only [hh']
    field_simp
    ring
  have hDle : ∀ y1 ∈ Set.Icc (-M) M, ∀ y2 ∈ Set.Icc (-M) M, y1 ≤ y2 →
      (1 + y1) * (1 + L * y1) ≤ (1 + y2) * (1 + L * y2) := by
    intro y1 hy1 y2 hy2 hle
    have := hy1.1
    have := hy2.1
    nlinarith [mul_nonneg (sub_nonneg.2 hle) (by nlinarith : 0 ≤ 1 + L + L * (y1 + y2))]
  have hq : ∀ y1 ∈ Set.Icc (-M) M, ∀ y2 ∈ Set.Icc (-M) M, y1 ≤ y2 →
      2 * S - L * (L - 1) / ((1 + y1) * (1 + L * y1))
        ≤ 2 * S - L * (L - 1) / ((1 + y2) * (1 + L * y2)) := by
    intro y1 hy1 y2 hy2 hle
    have hDpos := mul_pos (hp1 y1 hy1) (hp2 y1 hy1)
    have := div_le_div_of_nonneg_left hK0 hDpos (hDle y1 hy1 y2 hy2 hle)
    linarith
  have hq0 : 0 ≤ 2 * S - L * (L - 1) / ((1 + 0) * (1 + L * 0)) := by
    simp only [add_zero, mul_zero, mul_one, div_one]
    linarith
  have hhM : h (-M) = 0 := by
    simp only [hh]
    have e1 : 1 + -M = 1 - M := by ring
    have e2 : 1 + L * -M = 1 - L * M := by ring
    rw [e1, e2]
    nlinarith [hfM]
  have hh0 : h 0 = 0 := by simp [hh]
  intro x hx
  have key : 0 ≤ h x := by
    rcases le_total 0 x with hx0 | hx0
    · have := mono_gen h h' 0 x hx0
        (fun y hy => hd y ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩)
        (fun y hy => by
          have hyM : y ∈ Set.Icc (-M) M := ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩
          have h0M : (0:ℝ) ∈ Set.Icc (-M) M := ⟨by linarith, by linarith⟩
          rw [hform y hyM]
          exact mul_nonneg hy.1 (le_trans hq0 (hq 0 h0M y hyM hy.1)))
      linarith
    · by_cases hqx : 2 * S - L * (L - 1) / ((1 + x) * (1 + L * x)) ≤ 0
      · have := mono_gen h h' (-M) x hx.1
          (fun y hy => hd y ⟨hy.1, by linarith [hy.2, hx0, hx.2]⟩)
          (fun y hy => by
            have hyM : y ∈ Set.Icc (-M) M := ⟨hy.1, by linarith [hy.2, hx0]⟩
            rw [hform y hyM]
            have hyle : y ≤ 0 := by linarith [hy.2, hx0]
            have hqy := le_trans (hq y hyM x hx hy.2) hqx
            nlinarith)
        linarith
      · push_neg at hqx
        have := anti_gen h h' x 0 hx0
          (fun y hy => hd y ⟨by linarith [hy.1, hx.1], by linarith [hy.2, hx.2]⟩)
          (fun y hy => by
            have hyM : y ∈ Set.Icc (-M) M := ⟨by linarith [hy.1, hx.1], by linarith [hy.2]⟩
            rw [hform y hyM]
            have hqy := le_trans hqx.le (hq x hx y hyM hy.1)
            exact mul_nonpos_of_nonpos_of_nonneg hy.2 hqy)
        linarith
  simp only [hh] at key
  linarith

theorem sharp_drag {T : ℕ} (m c : Fin T → ℝ) (L M : ℝ) (hL : 1 < L) (hM0 : 0 < M)
    (hLM : L * M < 1) (hc : ∀ t, 0 < 1 + c t)
    (hM : ∀ t, |(m t - c t) / (1 + c t)| ≤ M) :
    L * Real.log (W m c 1) + (1 - L) * Real.log (W m c 0) - Real.log (W m c L)
      ≤ (L * Real.log (1 - M) - Real.log (1 - L * M)) / M ^ 2
          * (∑ t, ((m t - c t) / (1 + c t)) ^ 2) := by
  have hM1 : M < 1 := by nlinarith
  rw [drag_eq m c hc L M (by linarith) hM1 hLM hM]
  calc _ ≤ ∑ t, (L * Real.log (1 - M) - Real.log (1 - L * M)) / M ^ 2
        * ((m t - c t) / (1 + c t)) ^ 2 :=
        Finset.sum_le_sum (fun t _ =>
          sharp_day L M hL hM0 hLM _ ⟨(abs_le.1 (hM t)).1, (abs_le.1 (hM t)).2⟩)
    _ = _ := by rw [← Finset.mul_sum]

/-- non-vacuity of al005: T = 2, L = 2, tau = 1/100, c = 0, m = (1/10, -1/10) -/
example : ∃ (m c : Fin 2 → ℝ) (L τ : ℝ), 1 < L ∧ (∀ t, 0 < 1 + c t) ∧
    (∀ t, 0 < 1 + L * ((m t - c t) / (1 + c t))) ∧
    (∑ t, ((m t - c t) / (1 + c t)) ^ 3) ≤ τ * ∑ t, ((m t - c t) / (1 + c t)) ^ 2 := by
  refine ⟨![1/10, -1/10], ![0, 0], 2, 1/100, ?_, ?_, ?_, ?_⟩
  · norm_num
  · intro t; fin_cases t <;> simp
  · intro t; fin_cases t <;> simp <;> norm_num
  · simp [Fin.sum_univ_two]
    norm_num

#print axioms cubic_lb
#print axioms al005
#print axioms sharp_day
#print axioms sharp_drag

end FL
