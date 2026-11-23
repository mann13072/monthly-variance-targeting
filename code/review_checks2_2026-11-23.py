
import json,sys,numpy as np,re,math
p=sys.argv[1]; root=sys.argv[2]
d=json.load(open(p+'/results/practical_Asia_Pacific_ex_Japan_2026-11-22.json'))
print('AP',json.dumps({k:d[k] for k in ['primary_B_monthly_drift','premise','post_jump','practical_gates']}))
print('AP dd/uw/worst', {k:{a:d[k][a] for a in ['cagr','max_dd','worst_day','longest_underwater_months']} for k in ['metrics_B_monthly_drift','metrics_index']})
for f in ['etf_shortfall_exploratory_2026-11-22.json','xs2d_shortfall_exploratory_2026-11-22.json','paper_trade_threshold_2026-11-22.json']:
    j=json.load(open(p+'/results/'+f))
    def strip(o):
        if isinstance(o,dict): return {k:strip(v) for k,v in o.items() if not (isinstance(v,list) and len(v)>6)}
        return o
    print(f, json.dumps(strip(j))[:900])
# extra diagnostics
def load(q):
    D=[];M=[];R=[]
    for ln in open(q,errors='ignore'):
        s=[t.strip() for t in ln.split(',')]
        if len(s)>=5 and re.fullmatch(r'\d{8}',s[0]): D.append(int(s[0]));M.append(float(s[1])/100);R.append(float(s[4])/100)
    return np.array(D),np.array(M),np.array(R)
def mbb(x,b,B=4000,seed=7):
    g=np.random.default_rng(seed);n=len(x);k=math.ceil(n/b);m=np.empty(B)
    for i in range(B):
        st=g.integers(0,n-b+1,k);m[i]=x[(st[:,None]+np.arange(b)).ravel()[:n]].mean()
    return [round(float(v),3) for v in np.percentile(m,[2.5,97.5])]
V=.002
for nm,f in [('Europe','Europe'),('Japan','Japan'),('AP','Asia_Pacific_ex_Japan')]:
    D,M,R=load(f'{root}/raw/data/french/regions/{f}_3_Factors_Daily.csv'); x=M/(1+R); mon=D//100; um=np.unique(mon)
    RV=np.array([np.sum(x[mon==u]**2) for u in um]); L=np.minimum(1.5,np.sqrt(V/RV[:-1])); RVk=RV[1:]
    yr=um[1:]//100
    eI=abs(RVk/V-1); eS=abs(L**2*RVk/V-1)
    em=np.cumsum(RV)[:-1]/np.arange(1,len(RV)); Lc=np.minimum(1.5,np.sqrt(V/em)); eC=abs(Lc**2*RVk/V-1)
    keep=~((yr>=2000)&(yr<=2009))
    hi=RV[:-1]>V   # prior-month variance above target
    print(nm,'vs idx b3',round(float((eS-eI).mean()),3),mbb(eS-eI,3),'| vs expanding b3',round(float((eS-eC).mean()),3),mbb(eS-eC,3),
      '| excl2000-09 vs idx',round(float((eS-eI)[keep].mean()),3),mbb((eS-eI)[keep],3),'vs exp',round(float((eS-eC)[keep].mean()),3),mbb((eS-eC)[keep],3),
      '| share L<1',round(float((L<1).mean()),3),'share L>1',round(float((L>1).mean()),3),'share months prior RV>target',round(float(hi.mean()),3),
      '| mean|dev| expanding',round(float(eC.mean()),3),'rule',round(float(eS.mean()),3))
