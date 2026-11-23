# account_sim_100k.py -- strict USD 100,000 account simulation of the frozen rule (implementation C), whole shares, no borrowing, FX costs on the EUR line.
import json, re, math, datetime as dt, warnings, sys
import numpy as np
warnings.filterwarnings('ignore')
sys.path.insert(0,'code')
import practical_vt as pv
P=pv.PARAMS
base='./raw/data/etf/yahoo_chart_%s_daily_2026-11-22.json'
def load(fn):
    j=json.load(open(fn));r=j['chart']['result'][0];ts=r['timestamp'];adj=r['indicators']['adjclose'][0]['adjclose'] if 'adjclose' in r['indicators'] else r['indicators']['quote'][0]['close'];cl=r['indicators']['quote'][0]['close']
    out={dt.datetime.fromtimestamp(t,dt.UTC).strftime('%Y%m%d'):(a if a is not None else c) for t,a,c in zip(ts,adj,cl)}
    return {k:v for k,v in out.items() if v is not None}
idx=load(base%'SP500TR');xs=load(base%'XS2D.L');db=load(base%'DBPG.DE');eur=load(base%'EURUSD');spy=load(base%'SPY')
RF={}
for ln in open('./raw/data/french/F-F_Research_Data_Factors_daily.csv',errors='ignore'):
    p=[s.strip() for s in ln.split(',')]
    if len(p)>=5 and re.fullmatch(r'\d{8}',p[0]): RF[p[0]]=float(p[4])/100
idates=sorted(d for d in idx if d in RF);iv=np.array([idx[d] for d in idates]);m={idates[i]:iv[i]/iv[i-1]-1 for i in range(1,len(idates))}
xidx={d:(m[d]-RF[d])/(1+RF[d]) for d in m}
def lastprior(series,d):
    ks=[k for k in series if k<=d];return series[max(ks)] if ks else None
def simulate(route,exec_bp,fx_bp,cash_spread=0.005,capital=100000.0,start='20100503',end='20260930'):
    ser=xs   # the EUR route is modelled from the USD line: the Yahoo Xetra series for DBPG.DE has bad ticks (see glitch count)
    days=sorted(d for d in ser if start<=d<=end and d in RF)
    months=sorted(set(d[:6] for d in days));first={mo:min(d for d in days if d[:6]==mo) for mo in months}
    RV={mo:sum(v**2 for d,v in xidx.items() if d[:6]==mo) for mo in sorted(set(d[:6] for d in xidx))}
    cash=capital;sh=0;vals=[];costs=0.0;traded=0.0;ntr=0;ws=[];datesv=[]
    for d in days:
        pu=ser[d]
        cash*=1+max(RF[d]-cash_spread/252,0.0)
        V=cash+sh*pu
        mo=d[:6]
        if d==first[mo]:
            pm=sorted(k for k in RV if k<mo)[-1]
            if pm in RV and RV[pm]>0:
                L=min(P['L_MAX'],math.sqrt(P['V_TAR']/RV[pm]));w=L/2
                want=int(math.floor(w*V/pu));delta=want-sh
                if delta>0:
                    while delta>0 and delta*pu*(1+(exec_bp+fx_bp)/1e4)>cash: delta-=1
                    N=delta*pu;c=N*(exec_bp+fx_bp)/1e4;cash-=N+c;sh+=delta;costs+=c;traded+=N;ntr+=1 if delta else 0
                elif delta<0:
                    N=-delta*pu;c=N*(exec_bp+fx_bp)/1e4;cash+=N-c;sh+=delta;costs+=c;traded+=N;ntr+=1
                V=cash+sh*pu
        vals.append(V);ws.append(sh*pu/V if V>0 else 0.0);datesv.append(d)
    vals=np.array(vals);r=vals[1:]/vals[:-1]-1;yrs=(dt.date(int(datesv[-1][:4]),int(datesv[-1][4:6]),int(datesv[-1][6:]))-dt.date(int(datesv[0][:4]),int(datesv[0][4:6]),int(datesv[0][6:]))).days/365.25
    peak=np.maximum.accumulate(vals);dd=1-vals/peak;uw=0;uwm=0
    for x in dd:
        uw=uw+1 if x>0 else 0;uwm=max(uwm,uw)
    # monthly variance score from daily account returns
    cmap=RF
    H=[];E=[]
    for mo in months:
        ids=[i for i,d in enumerate(datesv[1:],start=1) if d[:6]==mo]
        if not ids or mo not in RV: continue
        rv=sum(((r[i-1]-RF[datesv[i]])/(1+RF[datesv[i]]))**2 for i in ids);H.append(rv/P['V_TAR']);E.append(abs(RV[mo]/P['V_TAR']-1))
    H=np.array(H);E=np.array(E);dev=np.abs(H-1);lo,hi=pv.mbb(dev-E,3,2000,20260921)
    S=[float(np.mean(dev[i*12:(i+1)*12])) for i in range(len(dev)//12)]
    return dict(route=route,exec_bp=exec_bp,fx_bp=fx_bp,start=datesv[0],end=datesv[-1],years=round(yrs,1),final_value=float(vals[-1]),cagr=float(math.exp(np.log(vals[-1]/vals[0])/yrs)-1),
        max_dd=float(dd.max()),worst_day=float(r.min()),longest_uw_months=uwm/21.0,vol=float(np.std(r,ddof=1)*math.sqrt(len(r)/yrs)),total_costs_usd=costs,trades=ntr,traded_usd=traded,
        turnover_per_year=traded/float(np.mean(vals))/yrs,avg_fund_weight=float(np.mean(ws)),portfolio_fee_bp=60*float(np.mean(ws)),primary_delta=float((dev-E).mean()),primary_ci=[lo,hi],S_max=max(S),
        S_windows=len(S),min_value=float(vals.min()))
out={}
# data-quality diagnostic of the Xetra EUR line (Yahoo) against the LSE USD line, since 2012
cd=[d for d in sorted(db) if d>='20120101' and d in xs and lastprior(eur,d)]
u=np.array([db[d]*lastprior(eur,d) for d in cd]);xv=np.array([xs[d] for d in cd]);dr=np.abs((u[1:]/u[:-1]-1)-(xv[1:]/xv[:-1]-1))
out['xetra_eur_line_diagnostic']=dict(days=len(cd),days_disagree_over_5pct=int((dr>0.05).sum()),days_disagree_over_10pct=int((dr>0.10).sum()),corr=float(np.corrcoef(u[1:]/u[:-1]-1,xv[1:]/xv[:-1]-1)[0,1]),cumulative_ratio=float((u[-1]/u[0])/(xv[-1]/xv[0])))
for lab,route,eb,fb in [('USD line, 5 bp','USD',5,0),('USD line, 15 bp','USD',15,0),('EUR route modelled from USD line + FX, 5 bp + 10 bp','EUR',5,10),('EUR route modelled + FX, 15 bp + 30 bp','EUR',15,30)]:
    out[lab]=simulate(route,eb,fb)# comparators by endpoints over the same calendar span
def at(s,d):
    ks=[k for k in s if k<=d];return s[max(ks)]
s0,e0=out['USD line, 5 bp']['start'],out['USD line, 5 bp']['end'];yrs=(dt.date(2026,9,30)-dt.date(int(s0[:4]),int(s0[4:6]),int(s0[6:]))).days/365.25
cm={}
for n,sr in [('index_total_return',idx),('spy_adj_close',spy),('xs2d_alone',xs)]:
    r=at(sr,e0)/at(sr,s0);cm[n]=dict(final_value=100000*r,cagr=r**(1/yrs)-1)
vv=np.array([xs[d] for d in sorted(xs) if s0<=d<=e0]);cm['xs2d_alone']['max_dd']=float((1-vv/np.maximum.accumulate(vv)).max())
iv2=np.array([idx[d] for d in sorted(idx) if s0<=d<=e0]);cm['index_total_return']['max_dd']=float((1-iv2/np.maximum.accumulate(iv2)).max())
out['comparators']=cm
print(json.dumps(out,indent=1))
