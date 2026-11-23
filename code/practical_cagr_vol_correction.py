# Saved from the session scratch folder on 2026-11-22 so the result files can be reproduced (absolute paths inside are those of this PC).

import json, re, numpy as np, datetime as dt, sys
sys.path.insert(0,'code')
import practical_vt as pv
out={}
for nm,path in [('Europe','raw/data/french/regions/Europe_3_Factors_Daily.csv'),('Japan','raw/data/french/regions/Japan_3_Factors_Daily.csv'),('Asia_Pacific_ex_Japan','raw/data/french/regions/Asia_Pacific_ex_Japan_3_Factors_Daily.csv')]:
    d,mk,rf=pv.load('./'+path);mon=d//100;um=np.unique(mon);first_eval_idx=int(np.where(mon==um[1])[0][0])
    n_eval=len(d)-first_eval_idx;rep_years=n_eval/252
    s=dt.date(int(str(d[first_eval_idx])[:4]),int(str(d[first_eval_idx])[4:6]),int(str(d[first_eval_idx])[6:]));e=dt.date(int(str(d[-1])[:4]),int(str(d[-1])[4:6]),int(str(d[-1])[6:]))
    true_years=(e-s).days/365.25;j=json.load(open('./formal/results/practical_%s_2026-11-22.json'%nm))
    f=lambda c:(1+c)**(rep_years/true_years)-1
    out[nm]=dict(rows_per_year=round(n_eval/true_years,1),rep_years=round(rep_years,2),true_years=round(true_years,2),
        B_cagr=(j['metrics_B_monthly_drift']['cagr'],f(j['metrics_B_monthly_drift']['cagr'])),A_cagr=(j['metrics_A_daily_maintained']['cagr'],f(j['metrics_A_daily_maintained']['cagr'])),
        index_cagr=(j['metrics_index']['cagr'],f(j['metrics_index']['cagr'])),vol_scale=float(np.sqrt((n_eval/true_years)/252)),
        B_vol=(j['metrics_B_monthly_drift']['vol'],j['metrics_B_monthly_drift']['vol']*float(np.sqrt((n_eval/true_years)/252))),index_vol=(j['metrics_index']['vol'],j['metrics_index']['vol']*float(np.sqrt((n_eval/true_years)/252))))
print(json.dumps(out))
