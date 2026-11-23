import Fl.H3

/-! Formal lane, agent-lab hypotheses AL-002 (tight bound and constant corollary) and AL-004.
x_t = (m_t - c_t)/(1 + c_t); f(x) = L*log(1+x) - log(1+L*x); drag = L log W(1) + (1-L) log W(0) - log W(L). -/

namespace FL

/-- per-day upper bound: for L >= 1 and |x| <= u, f(x) <= L(L-1) x^2 / (2(1-u)(1-L u)) -/
lemma day_up (L u : ℝ) (hL : 1 ≤ L) (hu : 0 < u) (hLu : L * u < 1) :
    ∀ x ∈ Set.Icc (-u) u, L * Real.log (1 + x) - Real.log (1 + L * x)
      ≤ L * (L - 1) / (2 * (1 - u) * (1 - L * u)) * x ^ 2 := by
  have hu1 : u < 1 := by nlinarith
  have hK0 : 0 ≤ L * (L - 1) := by nlinarith
  have hp1 : ∀ y ∈ Set.Icc (-u) u, 0 < 1 + y := by
    intro y hy; have := hy.1; linarith
  have hp2 : ∀ y ∈ Set.Icc (-u) u, 0 < 1 + L * y := by
    intro y hy; have := hy.1; nlinarith
  have hq1 : 0 < 1 - u := by linarith
  have hq2 : 0 < 1 - L * u := by linarith
  set B := L * (L - 1) / (2 * (1 - u) * (1 - L * u)) with hB
  set h : ℝ → ℝ := fun y => B * y ^ 2 - (L * Real.log (1 + y) - Real.log (1 + L * y)) with hh
  have hd : ∀ y ∈ Set.Icc (-u) u, HasDerivAt h
      (B * (2 * y) - (L * (1 / (1 + y)) - L / (1 + L * y))) y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 y := (hasDerivAt_id y).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => 1 + L * y) L y := by
      simpa using ((hasDerivAt_id y).const_mul L).const_add 1
    have l1 := h1.log (hp1 y hy).ne'
    have l2 := h2.log (hp2 y hy).ne'
    have q : HasDerivAt (fun y : ℝ => B * y ^ 2) (B * (2 * y)) y := by
      simpa using ((hasDerivAt_pow 2 y).const_mul B)
    exact q.sub ((l1.const_mul L).sub l2)
  have hsign : ∀ y ∈ Set.Icc (-u) u,
      B * (2 * y) - (L * (1 / (1 + y)) - L / (1 + L * y))
        = y * (L * (L - 1) / ((1 - u) * (1 - L * u)) - L * (L - 1) / ((1 + y) * (1 + L * y))) := by
    intro y hy
    have a1 := (hp1 y hy).ne'
    have a2 := (hp2 y hy).ne'
    have a3 := hq1.ne'
    have a4 := hq2.ne'
    rw [hB]
    field_simp
    ring
  have hk : ∀ y ∈ Set.Icc (-u) u,
      0 ≤ L * (L - 1) / ((1 - u) * (1 - L * u)) - L * (L - 1) / ((1 + y) * (1 + L * y)) := by
    intro y hy
    apply sub_nonneg.2
    have hDpos : 0 < (1 - u) * (1 - L * u) := mul_pos hq1 hq2
    apply div_le_div_of_nonneg_left hK0 hDpos
    have hy1 := hy.1
    have hy2 := hy.2
    nlinarith [mul_nonneg (by linarith : 0 ≤ y + u) (by nlinarith : 0 ≤ 1 + L - L * (u - y))]
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

/-- down days: for L >= 1 and -u <= x <= 0, f(x) >= L(L-1)/2 x^2 -/
lemma day_neg (L u : ℝ) (hL : 1 ≤ L) (hu : 0 < u) (hLu : L * u < 1) :
    ∀ x ∈ Set.Icc (-u) 0, L * (L - 1) / 2 * x ^ 2
      ≤ L * Real.log (1 + x) - Real.log (1 + L * x) := by
  have hK0 : 0 ≤ L * (L - 1) := by nlinarith
  have hp1 : ∀ y ∈ Set.Icc (-u) 0, 0 < 1 + y := by
    intro y hy; have := hy.1; nlinarith
  have hp2 : ∀ y ∈ Set.Icc (-u) 0, 0 < 1 + L * y := by
    intro y hy; have := hy.1; nlinarith
  set h : ℝ → ℝ := fun y =>
    L * Real.log (1 + y) - Real.log (1 + L * y) - L * (L - 1) / 2 * y ^ 2 with hh
  have hd : ∀ y ∈ Set.Icc (-u) 0, HasDerivAt h
      (L * (1 / (1 + y)) - L / (1 + L * y) - L * (L - 1) / 2 * (2 * y)) y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 y := (hasDerivAt_id y).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => 1 + L * y) L y := by
      simpa using ((hasDerivAt_id y).const_mul L).const_add 1
    have l1 := h1.log (hp1 y hy).ne'
    have l2 := h2.log (hp2 y hy).ne'
    have q : HasDerivAt (fun y : ℝ => L * (L - 1) / 2 * y ^ 2) (L * (L - 1) / 2 * (2 * y)) y := by
      simpa using ((hasDerivAt_pow 2 y).const_mul (L * (L - 1) / 2))
    exact ((l1.const_mul L).sub l2).sub q
  have hsign : ∀ y ∈ Set.Icc (-u) 0,
      L * (1 / (1 + y)) - L / (1 + L * y) - L * (L - 1) / 2 * (2 * y)
        = y * (L * (L - 1) / ((1 + y) * (1 + L * y)) - L * (L - 1)) := by
    intro y hy
    have a1 := (hp1 y hy).ne'
    have a2 := (hp2 y hy).ne'
    field_simp
    ring
  have hk : ∀ y ∈ Set.Icc (-u) 0, 0 ≤ L * (L - 1) / ((1 + y) * (1 + L * y)) - L * (L - 1) := by
    intro y hy
    have hDpos : 0 < (1 + y) * (1 + L * y) := mul_pos (hp1 y hy) (hp2 y hy)
    have hD1 : (1 + y) * (1 + L * y) ≤ 1 := by
      have h1 := hy.1
      have h2 := hy.2
      have h3 : 0 ≤ 1 + L + L * y := by nlinarith
      nlinarith [mul_nonneg (neg_nonneg.2 h2) h3]
    have := div_le_div_of_nonneg_left hK0 hDpos hD1
    rw [div_one] at this
    linarith
  have h0 : h 0 = 0 := by simp [hh]
  have hanti : AntitoneOn h (Set.Icc (-u) 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (-u) 0)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro y hy
      exact (hd y ⟨hy.1.le, hy.2.le⟩).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro y hy
      have hy' : y ∈ Set.Icc (-u) 0 := ⟨hy.1.le, hy.2.le⟩
      rw [(hd y hy').deriv, hsign y hy']
      exact mul_nonpos_of_nonpos_of_nonneg hy.2.le (hk y hy')
  intro x hx
  have := hanti ⟨hx.1, hx.2⟩ ⟨by linarith, le_refl 0⟩ hx.2
  have key : 0 ≤ h x := by linarith
  simp only [hh] at key
  linarith

/-- concavity: for 0 <= L <= 1 and 1 + x > 0, L*log(1+x) <= log(1+L*x) -/
lemma day_small (L x : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hx : 0 < 1 + x) :
    L * Real.log (1 + x) ≤ Real.log (1 + L * x) := by
  have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hx)
    (Set.mem_Ioi.2 (by norm_num : (0:ℝ) < 1)) hL0 (by linarith : 0 ≤ 1 - L) (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at this
  have e : L * (1 + x) + (1 - L) * 1 = 1 + L * x := by ring
  rw [e] at this
  exact this

lemma drag_eq {T : ℕ} (m c : Fin T → ℝ) (hc : ∀ t, 0 < 1 + c t) (L M : ℝ)
    (hL0 : 0 ≤ L) (hM1 : M < 1) (hLM : L * M < 1)
    (hM : ∀ t, |(m t - c t) / (1 + c t)| ≤ M) :
    L * Real.log (W m c 1) + (1 - L) * Real.log (W m c 0) - Real.log (W m c L)
      = ∑ t, (L * Real.log (1 + (m t - c t) / (1 + c t))
              - Real.log (1 + L * ((m t - c t) / (1 + c t)))) := by
  set x : Fin T → ℝ := fun t => (m t - c t) / (1 + c t) with hx
  have hxM : ∀ t, -M ≤ x t ∧ x t ≤ M := fun t => abs_le.1 (hM t)
  have hz0 : ∀ t, 0 < 1 + (0:ℝ) * x t := by intro t; simp
  have hz1 : ∀ t, 0 < 1 + (1:ℝ) * x t := by intro t; have := (hxM t).1; linarith
  have hzL : ∀ t, 0 < 1 + L * x t := by intro t; have := (hxM t).1; nlinarith
  rw [logW_eq m c hc 1 hz1, logW_eq m c hc 0 hz0, logW_eq m c hc L hzL]
  have hsum0 : ∑ t, Real.log (1 + (0:ℝ) * x t) = 0 := by simp
  rw [hsum0]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [one_mul]
  ring

theorem al002_tight {T : ℕ} (m c : Fin T → ℝ) (L M : ℝ) (hL : 1 ≤ L) (hM0 : 0 < M)
    (hLM : L * M < 1) (hc : ∀ t, 0 < 1 + c t)
    (hM : ∀ t, |(m t - c t) / (1 + c t)| ≤ M) :
    L * Real.log (W m c 1) + (1 - L) * Real.log (W m c 0) - Real.log (W m c L)
      ≤ L * (L - 1) * (∑ t, ((m t - c t) / (1 + c t)) ^ 2) / (2 * (1 - M) * (1 - L * M)) := by
  have hM1 : M < 1 := by nlinarith
  rw [drag_eq m c hc L M (by linarith) hM1 hLM hM]
  calc _ ≤ ∑ t, L * (L - 1) / (2 * (1 - M) * (1 - L * M)) * ((m t - c t) / (1 + c t)) ^ 2 :=
        Finset.sum_le_sum (fun t _ =>
          day_up L M hL hM0 hLM _ ⟨(abs_le.1 (hM t)).1, (abs_le.1 (hM t)).2⟩)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem al004 {T : ℕ} (m c : Fin T → ℝ) (L M s : ℝ) (hL : 1 < L) (hM0 : 0 < M)
    (hLM : L * M < 1) (_hs0 : 0 ≤ s) (hc : ∀ t, 0 < 1 + c t)
    (hM : ∀ t, |(m t - c t) / (1 + c t)| ≤ M)
    (hP : s * (∑ t, ((m t - c t) / (1 + c t)) ^ 2)
      ≤ ∑ t ∈ Finset.univ.filter (fun t => (m t - c t) / (1 + c t) < 0),
          ((m t - c t) / (1 + c t)) ^ 2) :
    (s * (L * (L - 1) / 2) + (1 - s) * Cc L M) * (∑ t, ((m t - c t) / (1 + c t)) ^ 2)
      ≤ L * Real.log (W m c 1) + (1 - L) * Real.log (W m c 0) - Real.log (W m c L) := by
  have hM1 : M < 1 := by nlinarith
  rw [drag_eq m c hc L M (by linarith) hM1 hLM hM]
  set x : Fin T → ℝ := fun t => (m t - c t) / (1 + c t) with hx
  have hK0 : 0 ≤ L * (L - 1) := by nlinarith
  have hCle : Cc L M ≤ L * (L - 1) / 2 := by
    unfold Cc
    have hL0' : 0 < L := by linarith
    have hden : 1 ≤ (1 + L * M) * (1 + M) := by
      nlinarith [mul_pos hL0' hM0, mul_pos (mul_pos hL0' hM0) hM0]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hterm : ∀ t, Cc L M * x t ^ 2
        + (L * (L - 1) / 2 - Cc L M) * (if x t < 0 then x t ^ 2 else 0)
      ≤ L * Real.log (1 + x t) - Real.log (1 + L * x t) := by
    intro t
    have hxt := abs_le.1 (hM t)
    by_cases hneg : x t < 0
    · rw [if_pos hneg]
      have := day_neg L M hL.le hM0 hLM (x t) ⟨hxt.1, hneg.le⟩
      linarith
    · rw [if_neg hneg]
      have := day_aux L M hL hM0 hLM (x t) ⟨hxt.1, hxt.2⟩
      linarith
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hterm t)
  have h1 : ∑ t, (Cc L M * x t ^ 2
        + (L * (L - 1) / 2 - Cc L M) * (if x t < 0 then x t ^ 2 else 0))
      = Cc L M * (∑ t, x t ^ 2)
        + (L * (L - 1) / 2 - Cc L M) * ∑ t ∈ Finset.univ.filter (fun t => x t < 0), x t ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_filter]
  rw [h1] at hsum
  nlinarith [mul_le_mul_of_nonneg_left hP (sub_nonneg.2 hCle)]

/-- leverage rule of AL-002: L = min Lmax (sqrt (V / RV_prev)) -/
noncomputable def Lvt (Lmax V RVp : ℝ) : ℝ := min Lmax (Real.sqrt (V / RVp))

theorem al002_const {T : ℕ} (mc cc : Fin T → ℝ) (RVp Lmax V M γ : ℝ)
    (hLmax : 1 < Lmax) (hV : 0 < V) (hM0 : 0 < M) (hLM : Lmax * M < 1) (hγ : 0 < γ)
    (hRVp : 0 < RVp) (hcc : ∀ t, 0 < 1 + cc t)
    (hMc : ∀ t, |(mc t - cc t) / (1 + cc t)| ≤ M)
    (hP : (∑ t, ((mc t - cc t) / (1 + cc t)) ^ 2) ≤ γ * RVp) :
    Lvt Lmax V RVp * Real.log (W mc cc 1) + (1 - Lvt Lmax V RVp) * Real.log (W mc cc 0)
        - Real.log (W mc cc (Lvt Lmax V RVp))
      ≤ (Lmax - 1) / Lmax * (γ * V) / (2 * (1 - M) * (1 - Lmax * M)) := by
  set L := Lvt Lmax V RVp with hLdef
  have hLmax0 : 0 < Lmax := by linarith
  have hM1 : M < 1 := by nlinarith
  have hL0 : 0 ≤ L := le_min hLmax0.le (Real.sqrt_nonneg _)
  have hLle : L ≤ Lmax := min_le_left _ _
  have hLM' : L * M < 1 := by nlinarith
  have hL2 : L ^ 2 * RVp ≤ V := by
    have hs : L ≤ Real.sqrt (V / RVp) := min_le_right _ _
    have h2 : L ^ 2 ≤ (Real.sqrt (V / RVp)) ^ 2 := pow_le_pow_left₀ hL0 hs 2
    rw [Real.sq_sqrt (div_nonneg hV.le hRVp.le)] at h2
    exact (le_div_iff₀ hRVp).1 h2
  have hDm : 0 < 2 * (1 - M) * (1 - Lmax * M) := by
    have : 0 < 1 - M := by linarith
    have : 0 < 1 - Lmax * M := by linarith
    positivity
  have hRHS0 : 0 ≤ (Lmax - 1) / Lmax * (γ * V) / (2 * (1 - M) * (1 - Lmax * M)) := by
    apply div_nonneg _ hDm.le
    exact mul_nonneg (div_nonneg (by linarith) hLmax0.le) (mul_nonneg hγ.le hV.le)
  rcases lt_or_ge L 1 with hlt | hge
  · rw [drag_eq mc cc hcc L M hL0 hM1 hLM' hMc]
    refine le_trans ?_ hRHS0
    apply Finset.sum_nonpos
    intro t _
    have hxt := abs_le.1 (hMc t)
    have := day_small L ((mc t - cc t) / (1 + cc t)) hL0 hlt.le (by linarith [hxt.1])
    linarith
  · have hT := al002_tight mc cc L M hge hM0 hLM' hcc hMc
    set RVk := ∑ t, ((mc t - cc t) / (1 + cc t)) ^ 2 with hRVk
    have hRVk0 : 0 ≤ RVk := Finset.sum_nonneg (fun t _ => sq_nonneg _)
    have hDn : 0 < 2 * (1 - M) * (1 - L * M) := by
      have : 0 < 1 - M := by linarith
      have : 0 < 1 - L * M := by linarith
      positivity
    have hDmn : 2 * (1 - M) * (1 - Lmax * M) ≤ 2 * (1 - M) * (1 - L * M) := by
      have : 0 < 1 - M := by linarith
      nlinarith [mul_nonneg this.le (sub_nonneg.2 hLle), hM0]
    have hc1 : 0 ≤ (Lmax - 1) / Lmax := div_nonneg (by linarith) hLmax0.le
    have hcoef : L * (L - 1) ≤ (Lmax - 1) / Lmax * L ^ 2 := by
      have e : (Lmax - 1) / Lmax * L ^ 2 - L * (L - 1) = L * (Lmax - L) / Lmax := by
        field_simp
        ring
      have : 0 ≤ L * (Lmax - L) / Lmax :=
        div_nonneg (mul_nonneg hL0 (sub_nonneg.2 hLle)) hLmax0.le
      linarith
    have e2 : L ^ 2 * RVk ≤ γ * V := by
      calc L ^ 2 * RVk ≤ L ^ 2 * (γ * RVp) := mul_le_mul_of_nonneg_left hP (sq_nonneg L)
        _ = γ * (L ^ 2 * RVp) := by ring
        _ ≤ γ * V := mul_le_mul_of_nonneg_left hL2 hγ.le
    have hN : L * (L - 1) * RVk ≤ (Lmax - 1) / Lmax * (γ * V) := by
      calc L * (L - 1) * RVk ≤ (Lmax - 1) / Lmax * L ^ 2 * RVk :=
            mul_le_mul_of_nonneg_right hcoef hRVk0
        _ = (Lmax - 1) / Lmax * (L ^ 2 * RVk) := by ring
        _ ≤ (Lmax - 1) / Lmax * (γ * V) := mul_le_mul_of_nonneg_left e2 hc1
    have hN0 : 0 ≤ (Lmax - 1) / Lmax * (γ * V) := mul_nonneg hc1 (mul_nonneg hγ.le hV.le)
    calc _ ≤ L * (L - 1) * RVk / (2 * (1 - M) * (1 - L * M)) := hT
      _ ≤ (Lmax - 1) / Lmax * (γ * V) / (2 * (1 - M) * (1 - L * M)) := by
          first
            | exact div_le_div_of_nonneg_right hN hDn.le
            | exact (div_le_div_iff_of_pos_right hDn).2 hN
      _ ≤ _ := div_le_div_of_nonneg_left hN0 hDm hDmn

/-- non-vacuity of al004: T = 2, L = 2, M = 1/5, s = 9/20, c = 0, m = (1/10, -1/10) -/
example : ∃ (m c : Fin 2 → ℝ) (L M s : ℝ), 1 < L ∧ 0 < M ∧ L * M < 1 ∧ 0 ≤ s ∧
    (∀ t, 0 < 1 + c t) ∧ (∀ t, |(m t - c t) / (1 + c t)| ≤ M) ∧
    s * (∑ t, ((m t - c t) / (1 + c t)) ^ 2)
      ≤ ∑ t ∈ Finset.univ.filter (fun t => (m t - c t) / (1 + c t) < 0),
          ((m t - c t) / (1 + c t)) ^ 2 := by
  refine ⟨![1/10, -1/10], ![0, 0], 2, 1/5, 9/20, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro t; fin_cases t <;> simp
  · intro t; fin_cases t <;> simp [abs_of_pos, abs_of_neg] <;> norm_num
  · simp [Finset.sum_filter, Fin.sum_univ_two]
    norm_num

/-- non-vacuity of al002_tight / al002_const hypotheses: T = 2, L = 3/2, M = 1/5, m = (3/100, -3/100) -/
example : ∃ (m c : Fin 2 → ℝ) (L M : ℝ), 1 ≤ L ∧ 0 < M ∧ L * M < 1 ∧
    (∀ t, 0 < 1 + c t) ∧ (∀ t, |(m t - c t) / (1 + c t)| ≤ M) := by
  refine ⟨![3/100, -3/100], ![0, 0], 3/2, 1/5, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · intro t; fin_cases t <;> simp
  · intro t; fin_cases t <;> simp [abs_of_pos, abs_of_neg] <;> norm_num

#print axioms day_up
#print axioms day_neg
#print axioms al002_tight
#print axioms al002_const
#print axioms al004

end FL
