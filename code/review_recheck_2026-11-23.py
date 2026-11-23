
import numpy as np, re, math, sys, json
root=sys.argv[1]
def load(p):
    d=[];m=[];r=[]
    for ln in open(p,errors='ignore'):
        q=[s.strip() for s in ln.split(',')]
        if len(q)>=5 and re.fullmatch(r'\d{8}',q[0]):
            v=[float(x) for x in q[1:5]]
            d.append(int(q[0])); m.append(v[0]/100); r.append(v[3]/100)
    return np.array(d),np.array(m),np.array(r)
def mbb(x,block,B=4000,seed=1):
    rng=np.random.default_rng(seed); n=len(x); k=math.ceil(n/block); mm=np.empty(B)
    for b in range(B):
        st=rng.integers(0,n-block+1,k); idx=(st[:,None]+np.arange(block)).ravel()[:n]; mm[b]=x[idx].mean()
    return np.percentile(mm,[2.5,97.5])
V=0.002; out={}
series={}
for nm,f in [('Europe','Europe'),('Japan','Japan'),('AP','Asia_Pacific_ex_Japan')]:
    d,m,r=load(f'{root}/raw/data/french/regions/{f}_3_Factors_Daily.csv')
    x=m/(1+r); mon=d//100; um=np.unique(mon)
    RV=np.array([np.sum(x[mon==u]**2) for u in um])
    L=np.minimum(1.5,np.sqrt(V/RV[:-1]))      # for months 1..K-1
    RVk=RV[1:]; HI=RVk/V; HS=L**2*RVk/V
    eI=np.abs(HI-1); dS=np.abs(HS-1)
    res={'n':len(RVk),'zero_ret_days':int((m==0).sum()),'meanRV_over_V':float(HI.mean()),'meanL':float(L.mean()),'share_cap':float((L>=1.5-1e-12).mean())}
    res['A_nocost_delta']=float((dS-eI).mean())
    # fair static benchmark: ex-post constant leverage so mean(H)=1 (oracle)
    Ls=math.sqrt(V/RVk.mean()); eS=np.abs(Ls**2*HI-1); res['static_L']=Ls; res['static_mad']=float(eS.mean()); res['rule_mad']=float(dS.mean()); res['idx_mad']=float(eI.mean())
    dd=dS-eS; res['delta_vs_static']=float(dd.mean()); res['delta_vs_static_ci3']=mbb(dd,3).tolist(); res['delta_vs_static_ci12']=mbb(dd,12).tolist()
    # also causal static: leverage from trailing-expanding mean RV (no look-ahead)
    em=np.cumsum(RV)[:-1]/np.arange(1,len(RV)); Lc=np.minimum(1.5,np.sqrt(V/em)); eC=np.abs(Lc**2*RVk/V-1)
    res['rule_vs_expanding_static']=float((dS-eC).mean()); res['expanding_ci12']=mbb(dS-eC,12).tolist()
    dl=dS-eI; res['ci_idx_b3']=mbb(dl,3).tolist(); res['ci_idx_b6']=mbb(dl,6).tolist(); res['ci_idx_b12']=mbb(dl,12).tolist()
    yr=(um[1:]//100)
    res['by_period']={a:float(dl[(yr>=lo)&(yr<=hi)].mean()) for a,(lo,hi) in {'1990-99':(1990,1999),'2000-09':(2000,2009),'2010-19':(2010,2019),'2020-26':(2020,2026)}.items()}
    res['share_months_rule_better']=float((dl<0).mean())
    top=np.argsort(-np.abs(dl))[:10]; mask=np.ones(len(dl),bool); mask[top]=False; res['delta_drop_top10_abs']=float(dl[mask].mean())
    res['median_delta']=float(np.median(dl))
    # underwater correction factor
    res['rows_per_month']=float(len(d)/len(um))
    series[nm]=dl; out[nm]=res
out['corr_delta_series']={ 'EU_JP':float(np.corrcoef(series['Europe'],series['Japan'])[0,1]),'EU_AP':float(np.corrcoef(series['Europe'],series['AP'])[0,1])}
dE,mE,_=load(f'{root}/raw/data/french/regions/Europe_3_Factors_Daily.csv'); dJ,mJ,_=load(f'{root}/raw/data/french/regions/Japan_3_Factors_Daily.csv')
out['daily_corr_EU_JP']=float(np.corrcoef(mE,mJ)[0,1])
print(json.dumps(out,indent=1))
