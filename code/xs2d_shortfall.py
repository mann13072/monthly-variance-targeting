# Saved from the session scratch folder on 2026-11-22 so the result files can be reproduced (absolute paths inside are those of this PC).

import json, numpy as np, math, datetime as dt, re, warnings, bisect
warnings.filterwarnings('ignore')
def load(fn):
    j=json.load(open(fn));r=j['chart']['result'][0];ts=r['timestamp'];adj=r['indicators']['adjclose'][0]['adjclose'];cl=r['indicators']['quote'][0]['close']
    d=[dt.datetime.fromtimestamp(t,dt.UTC).strftime('%Y%m%d') for t in ts]
    return [(a,(b if b is not None else c)) for a,b,c in zip(d,adj,cl)]
base='./raw/data/etf/yahoo_chart_%s_daily_2026-11-22.json'
idx=load(base%'SP500TR');xs=load(base%'XS2D.L');sso=load(base%'SSO')
RF={}
for ln in open('./raw/data/french/F-F_Research_Data_Factors_daily.csv',errors='ignore'):
    p=[s.strip() for s in ln.split(',')]
    if len(p)>=5 and re.fullmatch(r'\d{8}',p[0]): RF[p[0]]=float(p[4])/100
idates=[d for d,_ in idx];ival=np.array([v for _,v in idx])
mret={idates[i]:ival[i]/ival[i-1]-1 for i in range(1,len(idates))}
days=[d for d in idates[1:] if d in RF]
def price_at(series,date):
    ds=[d for d,_ in series];i=bisect.bisect_right(ds,date)-1;return ds[i],series[i][1]
def decomp(series,L,start,end):
    ds0,p0=price_at(series,start);ds1,p1=price_at(series,end)
    sel=[d for d in days if ds0<d<=ds1]
    m=np.array([mret[d] for d in sel]);c=np.array([RF[d] for d in sel])
    target=L*np.sum(np.log1p(m))+(1-L)*np.sum(np.log1p(c));ideal=np.sum(np.log1p(c+L*(m-c)));G=math.log(p1/p0);yrs=len(sel)/252
    return dict(days=len(sel),years=round(yrs,2),total_pa=(target-G)/yrs,drag_pa=(target-ideal)/yrs,impl_pa=(ideal-G)/yrs,fund_cagr=math.exp(G/yrs)-1,ideal_cagr=math.exp(ideal/yrs)-1,index_cagr=math.exp(np.sum(np.log1p(m))/yrs)-1)
out={}
S,E='20100318','20260930'
out['XS2D.L (USD line, LSE close)']=decomp(xs,2.0,S,E)
out['SSO same window']=decomp(sso,2.0,S,E)
yrs=[]
for y in range(2011,2026):
    a=str(y-1)+'1231';b=str(y)+'1231'
    r1=decomp(xs,2.0,a,b);r2=decomp(sso,2.0,a,b)
    yrs.append((y,round(r1['impl_pa']*100,2),round(r2['impl_pa']*100,2),round(r1['drag_pa']*100,2)))
out['by_year[year, XS2D impl%, SSO impl%, drag%]']=yrs
print('JSON'+json.dumps(out))
