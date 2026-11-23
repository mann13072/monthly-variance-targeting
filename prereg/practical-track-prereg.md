---
type: workbench
status: developing
created: 2026-11-22
up: "[[practical-track-plan]]"
---
# practical-track-prereg

Pre-registration of the practical volatility-targeting confirmation (session 2), frozen before the Europe and Japan files are opened for this purpose. Plan and the user's decisions: [[practical-track-plan]]. Theory: [[agent-lab-ideas]] AL-002 and the sharp bound ([[agent-lab-lead-review-addendum]]). Code: formal/py/practical_vt.py.

## Question and claims (kept separate)
1. Theorem: with the leverage rule L_k = min(L_max, sqrt(V_tar / RV_(k-1))), the monthly drag is at most the sharp bound S(L, M) RV_k whenever |x_t| <= M and L M < 1, and at most C_const when RV_k <= gamma RV_(k-1) (Lean: sharp_drag, al002_const). Checked by an integrity count, not a market claim.
2. Premise frequency: how often RV_k / RV_(k-1) exceeds gamma = 4 in each region, and what happens the month after.
3. Practical: whether the rule keeps monthly realised portfolio variance closer to the target than the unlevered regional index, net of costs and with realistic monthly implementation.

## Pre-registered definitions and parameters (do not change)
- Data: Ken French daily 3-factor files for Europe and Japan (raw/data/french/regions/, 1990-07-02 to 2026-09-30, 9,458 rows each, USD). x_t = (Mkt-RF/100) / (1 + RF/100), c_t = RF/100. Asia Pacific ex Japan may be reported as a third region; it is not part of the pass rule. North America and Developed are excluded (they overlap the US file).
- Months: calendar months (YYYYMM of the date). RV_k = sum over the days of month k of x_t^2. Month 1 is used only to set the first leverage and is excluded from all results.
- Rule: L_k = min(1.5, sqrt(0.0020 / RV_(k-1))), applied from the first trading day of month k. V_tar = 0.0020 per month (sum of squared daily decimal excess returns in the month; about 15.5 percent annualised using 12 months). L_max = 1.5, M = 0.20, gamma = 4.0.
- Implementation A (theorem convention): exposure L_k maintained daily. Implementation B (primary, tradable): at the first trading day of month k hold weight L_k in the index and (1 - L_k) in cash (borrowing if above 1), no intra-month rebalancing, so the exposure drifts.
- Costs (base case): 5 bp times the notional traded at the month start (A: |L_k - L_(k-1)|; B: |L_k - drifted weight|), 50 bp a year on exposure (fund fee), 50 bp a year above the reference rate on borrowed capital. Half-cost and double-cost cases are reported. The unlevered index comparator carries no costs.
- Primary statistic, per region, on implementation B: d_k = |H_k - 1| with H_k = realised variance of the strategy's daily excess return in month k divided by V_tar; e_k = |RV_k / V_tar - 1| for the index; Delta = mean(d_k - e_k). Moving-block bootstrap over months (block 3, 2,000 resamples), seeds Europe 20260902, Japan 20260903, Asia Pacific ex Japan 20260904. A region passes if the upper end of the 95 percent interval of Delta is below 0. The primary test passes only if both Europe and Japan pass. Implementation A is reported with the same statistic as a secondary result; the difference between A and B is the implementation shortfall.
- Secondary (reported, not gating): the log-scale deviation; the frequency of RV_k / RV_(k-1) above 4; the distribution of next month's ratio and H_k after such a month.
- Absolute practical gates, reported pass or fail for each implementation: maximum drawdown at most 40 percent, worst one-day loss at most 10 percent, longest time under water at most 36 months (21 trading days per month), annual turnover at most 12 times. The unlevered index is shown beside them. These absolute gates are expected to fail for any fully invested equity exposure (the US index itself had an 84 percent drawdown); they are reported as they fall, with the relative comparison to the index.
- Theorem integrity (not evidence about markets): for every month with |x_t| <= 0.20 on all days, drag <= S(L_k, 0.20) RV_k (and drag <= 0 for L_k below 1), and drag <= C_const = 0.00238095 when RV_k <= 4 RV_(k-1); count violations (expected 0) and months where the cap is exceeded (guarantee not applicable, reported).
- Decision: PRIMARY TEST PASSED if both regions pass; otherwise NOT PASSED. A pass says the rule keeps realised variance nearer the target than the index in those samples, nothing about returns. Net return, volatility, worst day, drawdown, recovery and turnover are reported for every case.

## Development check on the US file (disclosed; the US file is no longer clean)
Run once on 2026-11-22 before the freeze, to debug the code (formal/results/practical_us_dev_2026-11-22.json); no parameter was changed after it. Results: primary statistic on B: strategy mean deviation 0.663 against index 1.057, Delta -0.394 (95 percent interval -0.556 to -0.251); implementation A 0.657, so the implementation shortfall is small (0.006). Premise: 46 of 1202 month pairs above 4 (3.83 percent); after those 46 months the next month's ratio had mean 0.90 and median 0.45, above 1 in only 6 cases and above 4 in 1. Net: CAGR B 10.22 percent, volatility 16.0 percent, maximum drawdown 63.8 percent, worst day -18.4 percent, longest under water 113 months, turnover 2.2 times a year; the index: CAGR 9.80 percent, volatility 17.1 percent, drawdown 84.1 percent. Absolute gates: drawdown, one-day loss and time under water FAIL for both implementations over 1926 to 2026, turnover passes. Theorem integrity: 1202 months checked, 0 violations of the sharp bound, 0 of the constant, 0 months above the cap.
Two readings recorded now, before the regional run: (1) a synthetic self-test with non-persistent volatility gave the opposite sign (the rule deviates more than the index), so the primary test can fail and depends on volatility persistence; (2) mean reversion after a spike means the rule is under-invested in the month after, which costs return and is a real practical price of the rule.

## Rules until the regional run
- No parameter, statistic, threshold or cost value above may change. Code defects may be fixed only if logged here with the reason before the run, and any fix restarts nothing else.
- The regional files are opened once, by the frozen script; the reported results are whatever comes out.
