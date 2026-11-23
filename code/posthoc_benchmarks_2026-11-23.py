# posthoc_benchmarks_2026-11-23.py -- POST HOC checks added after the frozen test (not part of the pre-registration). numpy only.
# Uses the no-cost daily-maintained rule (implementation A: H_k = L_k^2 RV_k / V_tar); it differs from the frozen B by under 0.003 on Delta.
# Usage: python posthoc_benchmarks_2026-11-23.py <vault_root>   -> prints JSON
import numpy as np, re, math, sys, json
root=sys.argv[1]; V=0.002; LMAX=1.5; SEED=20261123; B=4000
def load(p):
    d=[];m=[];r=[]
    for ln in open(p,errors='ignore'):
        q=[s.strip() for s in ln.split(',')]
        if len(q)>=5 and re.fullmatch(r'\d{8}',q[0]): d.append(int(q[0])); m.append(float(q[1])/100); r.append(float(q[4])/100)
    return np.array(d),np.array(m),np.array(r)
def mbb(x,block):
    g=np.random.default_rng(SEED+block); n=len(x); k=math.ceil(n/block); mm=np.empty(B)
    for b in range(B):
        st=g.integers(0,n-block+1,k); mm[b]=x[(st[:,None]+np.arange(block)).ravel()[:n]].mean()
    return [float(v) for v in np.percentile(mm,[2.5,97.5])]
def stat(x,block=3): return dict(delta=float(x.mean()),ci95=mbb(x,block))
out={}
for nm,f in [('Europe','Europe'),('Japan','Japan'),('Asia_Pacific_ex_Japan','Asia_Pacific_ex_Japan')]:
    d,m,r=load(f'{root}/raw/data/french/regions/{f}_3_Factors_Daily.csv'); x=m/(1+r); mon=d//100; um=np.unique(mon)
    RV=np.array([np.sum(x[mon==u]**2) for u in um]); L=np.minimum(LMAX,np.sqrt(V/RV[:-1])); RVk=RV[1:]; yr=um[1:]//100
    eI=np.abs(RVk/V-1); eR=np.abs(L**2*RVk/V-1)
    em=np.cumsum(RV)[:-1]/np.arange(1,len(RV)); Lx=np.minimum(LMAX,np.sqrt(V/em)); eX=np.abs(Lx**2*RVk/V-1)   # causal: mean of all RV up to month k-1
    Ls=min(LMAX,math.sqrt(V/RVk.mean())); eS=np.abs(Ls**2*RVk/V-1)                                            # ex-post (look-ahead), illustration only
    keep=~((yr>=2000)&(yr<=2009)); dI=eR-eI; dX=eR-eX
    out[nm]=dict(months=int(len(RVk)),mean_RV_over_target=float((RVk/V).mean()),
      vs_index=stat(dI), vs_index_block6=stat(dI,6), vs_index_block12=stat(dI,12),
      vs_index_excl_2000_09=stat(dI[keep]), vs_expanding=stat(dX), vs_expanding_excl_2000_09=stat(dX[keep]),
      vs_expost_constant_illustration=dict(L=Ls,**stat(eR-eS)),
      by_decade={a:float(dI[(yr>=lo)&(yr<=hi)].mean()) for a,(lo,hi) in {'1990-99':(1990,1999),'2000-09':(2000,2009),'2010-19':(2010,2019),'2020-26':(2020,2026)}.items()},
      share_months_rule_closer=float((dI<0).mean()), mean_L=float(L.mean()), share_L_below_1=float((L<1).mean()), share_L_at_cap=float((L>=LMAX-1e-12).mean()),
      fee_bp_at_60bp_fund_fee=float(60*(L/2).mean()))
print(json.dumps(out,indent=1))
