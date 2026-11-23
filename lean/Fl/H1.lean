import Mathlib

/-! Formal lane, hypothesis H1 (round 2, accepted 2026-11-22).
Plain claim: for daily-rebalanced portfolios with leverage L0 and L, both solvent every day,
log W(L) - log W(L0) <= (L - L0) * sum_t (m_t - c_t) / (1 + R_t(L0)).
Lean checks derivation only; the assumptions are definitions plus two solvency hypotheses. -/

namespace FL

/-- daily return of leverage L: L*m + (1-L)*c -/
def R (L m c : ℝ) : ℝ := L * m + (1 - L) * c

/-- terminal wealth: product of (1 + R_t(L)), W_0 = 1 -/
noncomputable def W {T : ℕ} (m c : Fin T → ℝ) (L : ℝ) : ℝ := ∏ t, (1 + R L (m t) (c t))

theorem h1 {T : ℕ} (_hT : 1 ≤ T) (m c : Fin T → ℝ) (L0 L : ℝ)
    (h2 : ∀ t, 0 < 1 + R L0 (m t) (c t))
    (h3 : ∀ t, 0 < 1 + R L (m t) (c t)) :
    Real.log (W m c L) - Real.log (W m c L0)
      ≤ (L - L0) * ∑ t, ((m t - c t) / (1 + R L0 (m t) (c t))) := by
  unfold W
  rw [Real.log_prod (fun t _ => (h3 t).ne'), Real.log_prod (fun t _ => (h2 t).ne'),
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have hb := h2 t
  have ha := h3 t
  rw [← Real.log_div ha.ne' hb.ne']
  calc Real.log ((1 + R L (m t) (c t)) / (1 + R L0 (m t) (c t)))
      ≤ (1 + R L (m t) (c t)) / (1 + R L0 (m t) (c t)) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos ha hb)
    _ = (L - L0) * ((m t - c t) / (1 + R L0 (m t) (c t))) := by
        field_simp
        unfold R
        ring

/-- non-vacuity: the round-2 instance T=2, L0=1, L=2, c=0, m=(0.10,-0.10) satisfies every hypothesis -/
example : ∃ (m c : Fin 2 → ℝ) (L0 L : ℝ),
    (∀ t, 0 < 1 + R L0 (m t) (c t)) ∧ (∀ t, 0 < 1 + R L (m t) (c t)) ∧
    W m c L = 24/25 ∧ W m c L0 = 99/100 := by
  refine ⟨![1/10, -1/10], ![0, 0], 1, 2, ?_, ?_, ?_, ?_⟩
  · intro t; fin_cases t <;> simp [R] <;> norm_num
  · intro t; fin_cases t <;> simp [R] <;> norm_num
  · simp [W, R, Fin.prod_univ_two]; norm_num
  · simp [W, R, Fin.prod_univ_two]; norm_num

-- axiom check (lean check b): expect only propext, Classical.choice, Quot.sound
#print axioms h1

end FL
