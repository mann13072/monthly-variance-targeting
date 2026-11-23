# Saved from the session scratch folder on 2026-11-22 so the result files can be reproduced (absolute paths inside are those of this PC).

import numpy as np, math, sys, json
sys.path.insert(0,'code')
import practical_vt as p
rng=np.random.default_rng(5)
n=252*12;dates=[];y,m,d=2000,1,1
import datetime
dt=datetime.date(2000,1,3);rows=[]
while len(rows)<n:
    if dt.weekday()<5: rows.append(dt)
    dt+=datetime.timedelta(days=1)
mk=rng.standard_t(5,n)/math.sqrt(5/3)*0.0095+0.0003; rf=np.full(n,0.00012)
open('synth_factors.csv','w').write('hdr\n,Mkt-RF,SMB,HML,RF\n'+'\n'.join(f"{r.strftime('%Y%m%d')},{a*100:.4f},0,0,{b*100:.4f}" for r,a,b in zip(rows,mk,rf)))
res=p.run('synth_factors.csv',1,'synthetic self-test')
print(json.dumps({k:res[k] for k in ['months','primary_A_daily_maintained','primary_B_monthly_drift','premise','theorem_integrity','turnover_per_year','practical_gates']},indent=1))
