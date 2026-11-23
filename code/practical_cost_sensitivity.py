# Saved from the session scratch folder on 2026-11-22 so the result files can be reproduced (absolute paths inside are those of this PC).

import sys, json
sys.path.insert(0,'code')
import practical_vt as p
base={k:p.PARAMS[k] for k in ['SPREAD','BORROW_YR','FEE_YR']}
out={}
for reg,seed in [('Europe',20260902),('Japan',20260903),('Asia_Pacific_ex_Japan',20260904)]:
    for lab,f in [('half',0.5),('base',1.0),('double',2.0)]:
        for k in base: p.PARAMS[k]=base[k]*f
        r=p.run('./raw/data/french/regions/%s_3_Factors_Daily.csv'%reg,seed,reg)
        out[reg+'_'+lab]=dict(B_cagr=r['metrics_B_monthly_drift']['cagr'],B_sharpe=r['metrics_B_monthly_drift']['sharpe'],B_maxdd=r['metrics_B_monthly_drift']['max_dd'],
            primary_delta=r['primary_B_monthly_drift']['delta'],primary_ci=r['primary_B_monthly_drift']['ci95'],primary_pass=r['primary_B_monthly_drift']['passes'],index_cagr=r['metrics_index']['cagr'])
print(json.dumps(out,indent=1))
