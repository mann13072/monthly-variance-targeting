import Fl.AL

/-! Formal lane, AL-001 round 2: third-order bound.
|f(x) - L(L-1)/2 x^2| <= K' |x|^3 for |x| <= u, K' = L^3/(3 (1 - L u)^3), f(x) = L log(1+x) - log(1+L x). -/

namespace FL

lemma pos_side (G G' : ℝ → ℝ) (u : ℝ) (hd : ∀ y ∈ Set.Icc 0 u, HasDerivAt G (G' y) y)
    (h0 : G 0 = 0) (hs : ∀ y ∈ Set.Icc 0 u, 0 ≤ G' y) (hu : 0 ≤ u) :
    ∀ x ∈ Set.Icc 0 u, 0 ≤ G x := by
  have hmono : MonotoneOn G (Set.Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro y hy
      exact (hd y ⟨hy.1.le, hy.2.le⟩).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro y hy
      rw [(hd y ⟨hy.1.le, hy.2.le⟩).deriv]
      exact hs y ⟨hy.1.le, hy.2.le⟩
  intro x hx
  have := hmono ⟨le_refl 0, hu⟩ hx hx.1
  linarith

lemma neg_side (G G' : ℝ → ℝ) (u : ℝ) (hd : ∀ y ∈ Set.Icc (-u) 0, HasDerivAt G (G' y) y)
    (h0 : G 0 = 0) (hs : ∀ y ∈ Set.Icc (-u) 0, G' y ≤ 0) (hu : 0 ≤ u) :
    ∀ x ∈ Set.Icc (-u) 0, 0 ≤ G x := by
  have hanti : AntitoneOn G (Set.Icc (-u) 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (-u) 0)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro y hy
      exact (hd y ⟨hy.1.le, hy.2.le⟩).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro y hy
      rw [(hd y ⟨hy.1.le, hy.2.le⟩).deriv]
      exact hs y ⟨hy.1.le, hy.2.le⟩
  intro x hx
  have := hanti hx ⟨by linarith, le_refl 0⟩ hx.2
  linarith

/-- key algebraic inequality behind the third-derivative bound -/
lemma key_ineq (L u y : ℝ) (hL : 1 ≤ L) (hu : 0 < u) (hLu : L * u < 1)
    (hy1 : -u ≤ y) (hy2 : y ≤ u) :
    L * (L - 1) * (1 + L + L * y) * (1 - L * u) ^ 3 ≤ L ^ 3 * ((1 + y) * (1 + L * y)) := by
  have hL0 : 0 < L := by linarith
  have hv0 : 0 < L * u := mul_pos hL0 hu
  have hv1 : 0 < 1 - L * u := by linarith
  set v := L * u with hv
  have hD : (1 - u) * (1 - v) ≤ (1 + y) * (1 + L * y) := by
    rw [hv]
    nlinarith [mul_nonneg (by linarith : 0 ≤ y + u) (by nlinarith : 0 ≤ 1 + L - L * (u - y))]
  have h2 : 1 + L + L * y ≤ 1 + L + v := by rw [hv]; nlinarith
  have h3 : 0 ≤ 1 + L + L * y := by rw [hv] at hv1; nlinarith
  have hLm1 : 0 ≤ L - 1 := by linarith
  have s1 : (1 + L + v) * (1 - v) ≤ 1 + L := by nlinarith [mul_nonneg hL0.le hv0.le, sq_nonneg v]
  have s2 : (L - 1) * ((1 + L + v) * (1 - v)) * (1 - v) ≤ (L - 1) * (1 + L) * (1 - v) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left s1 hLm1) hv1.le
  have s4 : (L - 1) * (1 + L) * (1 - v) ≤ L * (L - v) := by
    nlinarith [mul_nonneg hv0.le (by nlinarith : 0 ≤ L ^ 2 - L)]
  have s5 : (L - 1) * (1 + L + v) * (1 - v) ^ 2 ≤ L * (L - v) := by nlinarith [s2, s4]
  have s6 : L * (L - 1) * (1 + L + v) * (1 - v) ^ 3 ≤ L ^ 3 * ((1 - u) * (1 - v)) := by
    have e1 : L * (L - 1) * (1 + L + v) * (1 - v) ^ 3
        = (L * (1 - v)) * ((L - 1) * (1 + L + v) * (1 - v) ^ 2) := by ring
    have e2 : L ^ 3 * ((1 - u) * (1 - v)) = (L * (1 - v)) * (L * (L - v)) := by
      rw [hv]; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left s5 (mul_nonneg hL0.le hv1.le)
  calc L * (L - 1) * (1 + L + L * y) * (1 - L * u) ^ 3
      ≤ L * (L - 1) * (1 + L + v) * (1 - v) ^ 3 := by
        rw [← hv]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (mul_nonneg hL0.le hLm1))
          (pow_nonneg hv1.le 3)
    _ ≤ L ^ 3 * ((1 - u) * (1 - v)) := s6
    _ ≤ L ^ 3 * ((1 + y) * (1 + L * y)) :=
        mul_le_mul_of_nonneg_left hD (pow_nonneg hL0.le 3)

lemma day_cubic (L u : ℝ) (hL : 1 ≤ L) (hu : 0 < u) (hLu : L * u < 1) :
    ∀ x ∈ Set.Icc (-u) u,
      |L * Real.log (1 + x) - Real.log (1 + L * x) - L * (L - 1) / 2 * x ^ 2|
        ≤ L ^ 3 / (3 * (1 - L * u) ^ 3) * |x| ^ 3 := by
  have hu1 : u < 1 := by nlinarith
  have hL0 : 0 < L := by linarith
  have hK0 : 0 ≤ L * (L - 1) := by nlinarith
  have hq1 : 0 < 1 - L * u := by linarith
  have hp1 : ∀ y ∈ Set.Icc (-u) u, 0 < 1 + y := by
    intro y hy; have := hy.1; linarith
  have hp2 : ∀ y ∈ Set.Icc (-u) u, 0 < 1 + L * y := by
    intro y hy; have := hy.1; nlinarith
  set c := L ^ 3 / (3 * (1 - L * u) ^ 3) with hc
  have hc0 : 0 ≤ c := by positivity
  set r : ℝ → ℝ := fun y => L * Real.log (1 + y) - Real.log (1 + L * y) - L * (L - 1) / 2 * y ^ 2
    with hr
  set rd : ℝ → ℝ := fun y => L * (1 / (1 + y)) - L / (1 + L * y) - L * (L - 1) / 2 * (2 * y)
    with hrd
  have hd : ∀ y ∈ Set.Icc (-u) u, HasDerivAt r (rd y) y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 y := (hasDerivAt_id y).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => 1 + L * y) L y := by
      simpa using ((hasDerivAt_id y).const_mul L).const_add 1
    have l1 := h1.log (hp1 y hy).ne'
    have l2 := h2.log (hp2 y hy).ne'
    have q : HasDerivAt (fun y : ℝ => L * (L - 1) / 2 * y ^ 2) (L * (L - 1) / 2 * (2 * y)) y := by
      simpa using ((hasDerivAt_pow 2 y).const_mul (L * (L - 1) / 2))
    exact ((l1.const_mul L).sub l2).sub q
  have hform : ∀ y ∈ Set.Icc (-u) u, rd y
      = -(y ^ 2 * (L * (L - 1) * (1 + L + L * y) / ((1 + y) * (1 + L * y)))) := by
    intro y hy
    have a1 := (hp1 y hy).ne'
    have a2 := (hp2 y hy).ne'
    simp only [hrd]
    field_simp
    ring
  have hq0 : ∀ y ∈ Set.Icc (-u) u, 0 ≤ L * (L - 1) * (1 + L + L * y) / ((1 + y) * (1 + L * y)) := by
    intro y hy
    have h3 : 0 ≤ 1 + L + L * y := by have := hy.1; nlinarith
    exact div_nonneg (mul_nonneg hK0 h3) (mul_pos (hp1 y hy) (hp2 y hy)).le
  have hq3 : ∀ y ∈ Set.Icc (-u) u,
      L * (L - 1) * (1 + L + L * y) / ((1 + y) * (1 + L * y)) ≤ 3 * c := by
    intro y hy
    have hDpos := mul_pos (hp1 y hy) (hp2 y hy)
    have e3 : 3 * c = L ^ 3 / (1 - L * u) ^ 3 := by
      rw [hc]; field_simp
    rw [e3, div_le_div_iff₀ hDpos (pow_pos hq1 3)]
    exact key_ineq L u y hL hu hLu hy.1 hy.2
  have hbd : ∀ y ∈ Set.Icc (-u) u, rd y ≤ 0 ∧ -(3 * c * y ^ 2) ≤ rd y := by
    intro y hy
    rw [hform y hy]
    have h0 := hq0 y hy
    have h3 := hq3 y hy
    constructor
    · nlinarith [mul_nonneg (sq_nonneg y) h0]
    · nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg y)]
  have hr0 : r 0 = 0 := by simp [hr]
  -- four auxiliary functions
  have G1 := pos_side (fun y => c * y ^ 3 - r y) (fun y => 3 * c * y ^ 2 - rd y) u
    (fun y hy => by
      have hy' : y ∈ Set.Icc (-u) u := ⟨by linarith [hy.1], hy.2⟩
      have := ((hasDerivAt_pow 3 y).const_mul c).sub (hd y hy')
      exact this.congr_deriv (by norm_num <;> ring))
    (by simp [hr0]) (fun y hy => by have := (hbd y ⟨by linarith [hy.1], hy.2⟩).1; nlinarith [sq_nonneg y])
    hu.le
  have G2 := pos_side (fun y => c * y ^ 3 + r y) (fun y => 3 * c * y ^ 2 + rd y) u
    (fun y hy => by
      have hy' : y ∈ Set.Icc (-u) u := ⟨by linarith [hy.1], hy.2⟩
      have := ((hasDerivAt_pow 3 y).const_mul c).add (hd y hy')
      exact this.congr_deriv (by norm_num <;> ring))
    (by simp [hr0]) (fun y hy => by have := (hbd y ⟨by linarith [hy.1], hy.2⟩).2; linarith)
    hu.le
  have G3 := neg_side (fun y => -(c * y ^ 3) - r y) (fun y => -(3 * c * y ^ 2) - rd y) u
    (fun y hy => by
      have hy' : y ∈ Set.Icc (-u) u := ⟨hy.1, by linarith [hy.2]⟩
      have := (((hasDerivAt_pow 3 y).const_mul c).neg).sub (hd y hy')
      exact this.congr_deriv (by norm_num <;> ring))
    (by simp [hr0]) (fun y hy => by have := (hbd y ⟨hy.1, by linarith [hy.2]⟩).2; linarith) hu.le
  have G4 := neg_side (fun y => -(c * y ^ 3) + r y) (fun y => -(3 * c * y ^ 2) + rd y) u
    (fun y hy => by
      have hy' : y ∈ Set.Icc (-u) u := ⟨hy.1, by linarith [hy.2]⟩
      have := (((hasDerivAt_pow 3 y).const_mul c).neg).add (hd y hy')
      exact this.congr_deriv (by norm_num <;> ring))
    (by simp [hr0]) (fun y hy => by have := (hbd y ⟨hy.1, by linarith [hy.2]⟩).1; nlinarith [sq_nonneg y])
    hu.le
  intro x hx
  change |r x| ≤ c * |x| ^ 3
  rcases le_total 0 x with hx0 | hx0
  · have g1 : 0 ≤ c * x ^ 3 - r x := G1 x ⟨hx0, hx.2⟩
    have g2 : 0 ≤ c * x ^ 3 + r x := G2 x ⟨hx0, hx.2⟩
    rw [abs_of_nonneg hx0, abs_le]
    constructor <;> linarith
  · have g3 : 0 ≤ -(c * x ^ 3) - r x := G3 x ⟨hx.1, hx0⟩
    have g4 : 0 ≤ -(c * x ^ 3) + r x := G4 x ⟨hx.1, hx0⟩
    have e : |x| ^ 3 = -(x ^ 3) := by rw [abs_of_nonpos hx0]; ring
    rw [e, abs_le]
    constructor <;> linarith

theorem al001 {T : ℕ} (m c : Fin T → ℝ) (L M θ : ℝ) (hL : 1 < L) (hM0 : 0 < M)
    (hLM : L * M < 1) (_hθ : 0 < θ) (hc : ∀ t, 0 < 1 + c t)
    (hM : ∀ t, |(m t - c t) / (1 + c t)| ≤ M)
    (hP : (∑ t, |(m t - c t) / (1 + c t)| ^ 3) ≤ θ * ∑ t, ((m t - c t) / (1 + c t)) ^ 2) :
    |(L * Real.log (W m c 1) + (1 - L) * Real.log (W m c 0) - Real.log (W m c L))
        - L * (L - 1) / 2 * (∑ t, ((m t - c t) / (1 + c t)) ^ 2)|
      ≤ L ^ 3 / (3 * (1 - L * M) ^ 3) * θ * (∑ t, ((m t - c t) / (1 + c t)) ^ 2) := by
  have hM1 : M < 1 := by nlinarith
  rw [drag_eq m c hc L M (by linarith) hM1 hLM hM]
  have hK : 0 ≤ L ^ 3 / (3 * (1 - L * M) ^ 3) := by
    have : 0 < 1 - L * M := by linarith
    positivity
  have hsum : (∑ t, (L * Real.log (1 + (m t - c t) / (1 + c t))
        - Real.log (1 + L * ((m t - c t) / (1 + c t))))) - L * (L - 1) / 2 * (∑ t, ((m t - c t) / (1 + c t)) ^ 2)
      = ∑ t, (L * Real.log (1 + (m t - c t) / (1 + c t))
        - Real.log (1 + L * ((m t - c t) / (1 + c t))) - L * (L - 1) / 2 * ((m t - c t) / (1 + c t)) ^ 2) := by
    simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum]
  calc _ ≤ ∑ t, |L * Real.log (1 + (m t - c t) / (1 + c t))
        - Real.log (1 + L * ((m t - c t) / (1 + c t))) - L * (L - 1) / 2 * ((m t - c t) / (1 + c t)) ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t, L ^ 3 / (3 * (1 - L * M) ^ 3) * |(m t - c t) / (1 + c t)| ^ 3 :=
        Finset.sum_le_sum (fun t _ =>
          day_cubic L M hL.le hM0 hLM _ ⟨(abs_le.1 (hM t)).1, (abs_le.1 (hM t)).2⟩)
    _ = L ^ 3 / (3 * (1 - L * M) ^ 3) * ∑ t, |(m t - c t) / (1 + c t)| ^ 3 := by
        rw [Finset.mul_sum]
    _ ≤ L ^ 3 / (3 * (1 - L * M) ^ 3) * (θ * ∑ t, ((m t - c t) / (1 + c t)) ^ 2) :=
        mul_le_mul_of_nonneg_left hP hK
    _ = _ := by ring

/-- non-vacuity of al001: T = 2, L = 2, M = 1/4, theta = 1/25, c = 0, m = (3/100, -2/100) -/
example : ∃ (m c : Fin 2 → ℝ) (L M θ : ℝ), 1 < L ∧ 0 < M ∧ L * M < 1 ∧ 0 < θ ∧
    (∀ t, 0 < 1 + c t) ∧ (∀ t, |(m t - c t) / (1 + c t)| ≤ M) ∧
    (∑ t, |(m t - c t) / (1 + c t)| ^ 3) ≤ θ * ∑ t, ((m t - c t) / (1 + c t)) ^ 2 := by
  refine ⟨![3/100, -2/100], ![0, 0], 2, 1/4, 1/25, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro t; fin_cases t <;> simp
  · intro t; fin_cases t <;> simp [abs_of_pos, abs_of_neg] <;> norm_num
  · simp [Fin.sum_univ_two]
    norm_num [abs_of_pos, abs_of_neg]

#print axioms day_cubic
#print axioms al001

end FL
