# Saved from the session scratch folder on 2026-11-22 so the result files can be reproduced (absolute paths inside are those of this PC).

import numpy as np, math, re, sys
sys.path.insert(0,'code')
import practical_vt as p
out={}
for nm,path in [('Europe','raw/data/french/regions/Europe_3_Factors_Daily.csv'),('Japan','raw/data/french/regions/Japan_3_Factors_Daily.csv'),('US_dev','raw/data/french/F-F_Research_Data_Factors_daily.csv')]:
    d,mk,rf=p.load('./'+path);x=mk/(1+rf);mon=d//100;um=np.unique(mon)
    RV=np.array([np.sum(x[mon==m]**2) for m in um]);L=np.array([min(1.5,math.sqrt(0.002/RV[k-1])) for k in range(1,len(um))])
    w=L/2
    out[nm]=dict(mean_L=float(L.mean()),share_L_at_cap=float((L>=1.5-1e-12).mean()),mean_w_xs2d=float(w.mean()),fee_bp_at_60bp=float(60*w.mean()),max_w=float(w.max()),share_months_w_above_833=float((w>5/6).mean()))
print(out)
