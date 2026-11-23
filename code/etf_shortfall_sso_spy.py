# Saved from the session scratch folder on 2026-11-22 so the result files can be reproduced (absolute paths inside are those of this PC).

import json, numpy as np, math, datetime as dt, re, warnings
warnings.filterwarnings('ignore')
def load(fn):
    j=json.load(open(fn));r=j['chart']['result'][0];ts=r['timestamp'];adj=r['indicators']['adjclose'][0]['adjclose'];cl=r['indicators']['quote'][0]['close']
    d=[dt.datetime.fromtimestamp(t,dt.UTC).strftime('%Y%m%d') for t in ts]
    return {a:(b if b is not None else c) for a,b,c in zip(d,adj,cl)}
base='./raw/data/etf/yahoo_chart_%s_daily_2026-11-22.json'
sso=load(base%'SSO');idx=load(base%'SP500TR');spy=load(base%'SPY')
RF={}
for ln in open('./raw/data/french/F-F_Research_Data_Factors_daily.csv',errors='ignore'):
    p=[s.strip() for s in ln.split(',')]
    if len(p)>=5 and re.fullmatch(r'\d{8}',p[0]): RF[p[0]]=float(p[4])/100
out={}
for name,fund,L in [('SSO (2x)',sso,2.0),('SPY (1x)',spy,1.0)]:
    ds=sorted(set(fund)&set(idx));F=np.array([fund[d] for d in ds]);I=np.array([idx[d] for d in ds])
    ds=ds[1:];rf_=F[1:]/F[:-1]-1;m=I[1:]/I[:-1]-1
    ok=np.array([d in RF for d in ds]);ds=[d for d,o in zip(ds,ok) if o];rf_=rf_[ok];m=m[ok];c=np.array([RF[d] for d in ds])
    Rid=c+L*(m-c)
    G=np.sum(np.log1p(rf_));target=L*np.sum(np.log1p(m))+(1-L)*np.sum(np.log1p(c));ideal=np.sum(np.log1p(Rid))
    yrs=len(m)/252
    out[name]=dict(days=len(m),first=ds[0],last=ds[-1],years=round(yrs,2),total_shortfall_pa=float((target-G)/yrs),drag_pa=float((target-ideal)/yrs),fund_impl_pa=float((ideal-G)/yrs),
        fund_cagr=float(math.exp(G/yrs)-1),index_cagr=float(math.exp(np.sum(np.log1p(m))/yrs)-1),ideal_cagr=float(math.exp(ideal/yrs)-1),mean_rf_pa=float(np.mean(c)*252))
    yy=sorted(set(d[:4] for d in ds));rows=[]
    for y in yy:
        mk=np.array([d[:4]==y for d in ds])
        if mk.sum()<100: continue
        t=L*np.sum(np.log1p(m[mk]))+(1-L)*np.sum(np.log1p(c[mk]));i2=np.sum(np.log1p(Rid[mk]));g=np.sum(np.log1p(rf_[mk]))
        rows.append([y,round(float(t-i2)*100,2),round(float(i2-g)*100,2),round(float(np.std(m[mk])*math.sqrt(252))*100,1)])
    out[name]['year[year, drag%, fund_impl%, vol%]']=rows
    if L==2.0:
        M=float(np.max(np.abs(m-c)/(1+c)));mm={}
        for d,v,cc in zip(ds,m,c): mm.setdefault(d[:6],[]).append(((v-cc)/(1+cc),cc))
        K0=L*(L-1);c3=L*(L-1)*(L+1)/3;S=(L*math.log(1-M)-math.log(1-L*M))/M**2;vs=vc=0;n=0
        for k,v in mm.items():
            xs=np.array([a for a,b in v]);cs=np.array([b for a,b in v])
            W1=np.sum(np.log1p(xs*(1+cs)+cs));W0=np.sum(np.log1p(cs));WL=np.sum(np.log1p(cs+L*xs*(1+cs)))
            D=L*W1+(1-L)*W0-WL;RV=float(np.sum(xs**2));S3=float(np.sum(xs**3));n+=1
            vs+= D>S*RV+1e-10; vc+= D<K0/2*RV-c3*S3-1e-10
        out[name]['theorem_monthly']=dict(months=n,M=M,S=S,sharp_violations=int(vs),cubic_lower_violations=int(vc))
print('JSON'+json.dumps(out))
