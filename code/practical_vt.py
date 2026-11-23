# practical_vt.py -- practical volatility-targeting test (formal lane, practical track). numpy only.
# Pre-registered parameters are constants below; do not change after the development run (only code defects, logged).
import numpy as np, math, re, sys, json
PARAMS=dict(V_TAR=0.0020, L_MAX=1.5, M_CAP=0.20, GAMMA=4.0, SPREAD=0.0005, BORROW_YR=0.005, FEE_YR=0.005,
            BLOCK_MONTHS=3, B_RESAMPLES=2000, DD_LIMIT=0.40, DAY_LIMIT=0.10, UW_MONTHS_LIMIT=36, TURNOVER_LIMIT=12.0, DAYS_YR=252)
def load(path):
    d=[];mk=[];rf=[]
    for ln in open(path,errors='ignore'):
        p=[s.strip() for s in ln.split(',')]
        if len(p)>=5 and re.fullmatch(r'\d{8}',p[0]):
            v=[float(x) for x in p[1:5]]
            if any(x<=-99.0 for x in v): continue
            d.append(int(p[0])); mk.append(v[0]/100.0); rf.append(v[3]/100.0)
    return np.array(d),np.array(mk),np.array(rf)   # date, Mkt-RF (decimal), RF (decimal)
def metrics(r, rf):
    lw=np.cumsum(np.log1p(r)); n=len(r); yrs=n/PARAMS['DAYS_YR']
    w=np.exp(lw); peak=np.maximum.accumulate(w); dd=1-w/peak
    under=dd>0; muw=cur=0
    for u in under:
        cur=cur+1 if u else 0; muw=max(muw,cur)
    ex=r-rf
    return dict(cagr=float(np.exp(lw[-1]/yrs)-1), vol=float(np.std(r,ddof=1)*math.sqrt(252)), sharpe=float(np.mean(ex)/np.std(ex,ddof=1)*math.sqrt(252)),
                max_dd=float(dd.max()), worst_day=float(r.min()), longest_underwater_months=float(muw/21.0))
def mbb(delta, block, B, seed):
    rng=np.random.default_rng(seed); n=len(delta); k=int(math.ceil(n/block)); means=np.empty(B)
    for b in range(B):
        st=rng.integers(0,n-block+1,k); idx=(st[:,None]+np.arange(block)[None,:]).ravel()[:n]; means[b]=delta[idx].mean()
    return float(np.percentile(means,2.5)),float(np.percentile(means,97.5))
def run(path, seed, label):
    P=PARAMS; date,mkx,rf=load(path); n=len(date)
    x=mkx/(1+rf)                    # x_t = (m - c)/(1 + c), with m - c = Mkt-RF and c = RF
    month=date//100; um=np.unique(month); idxs=[np.where(month==m)[0] for m in um]
    RV=np.array([np.sum(x[i]**2) for i in idxs]); K=len(um)
    L=np.ones(K)*np.nan
    for k in range(1,K):
        L[k]=min(P['L_MAX'], math.sqrt(P['V_TAR']/RV[k-1])) if RV[k-1]>0 else np.nan
    start=1
    # --- implementation A: theorem convention, exposure L_k maintained daily (daily-reset), investor trades at month start
    rA=[];rIdx=[];rfs=[];turnA=0.0;prevL=1.0;ret_by_month=[]
    # --- implementation B: month-start weight L_k in index, rest cash/borrow, drifting inside the month
    rB=[];turnB=0.0;wdrift=1.0
    for k in range(start,K):
        ii=idxs[k]; Lk=L[k]
        # A
        tradeA=abs(Lk-prevL); turnA+=tradeA
        daily=[]
        for j,t in enumerate(ii):
            c=rf[t]; m_ex=mkx[t]
            cost=P['FEE_YR']/252*Lk+P['BORROW_YR']/252*max(Lk-1,0)+(P['SPREAD']*tradeA if j==0 else 0.0)
            daily.append(c+Lk*m_ex-cost)
        rA+=daily; prevL=Lk
        # B: wealth path with initial weight Lk in index, (1-Lk) in cash (borrowing if Lk>1), no intra-month rebalance
        tradeB=abs(Lk-wdrift); turnB+=tradeB
        V=1.0; idxW=Lk; cashW=1-Lk; series=[]
        for j,t in enumerate(ii):
            Vprev=idxW+cashW
            idxW*= (1+rf[t]+mkx[t]); cashW*=(1+rf[t])
            fee_fin=P['FEE_YR']/252*max(idxW,0)+P['BORROW_YR']/252*max(-cashW,0)
            cost_open=P['SPREAD']*tradeB*Vprev if j==0 else 0.0
            idxW-=fee_fin+cost_open
            Vnow=idxW+cashW
            series.append(Vnow/Vprev-1.0)
        rB+=series; Vend=idxW+cashW; wdrift=idxW/Vend if Vend>0 else 0.0
        rIdx+=list(rf[ii]+mkx[ii]); rfs+=list(rf[ii])
    rA=np.array(rA);rB=np.array(rB);rIdx=np.array(rIdx);rfs=np.array(rfs)
    nm=K-start; yrs=len(rA)/252
    # primary statistic per month
    def hk_from(r):   # realised variance of daily excess portfolio return, over month, in units of target
        out=[];pos=0
        for k in range(start,K):
            m=len(idxs[k]); ex=(r[pos:pos+m]-rfs[pos:pos+m])/(1+rfs[pos:pos+m]); out.append(np.sum(ex**2)/P['V_TAR']); pos+=m
        return np.array(out)
    HA=hk_from(rA);HB=hk_from(rB);HI=hk_from(rIdx)
    dA=np.abs(HA-1);dB=np.abs(HB-1);eI=np.abs(HI-1)
    res=dict(label=label,file=path,days=n,months=int(nm),first=int(date[0]),last=int(date[-1]),params=P)
    for name,d in [('A_daily_maintained',dA),('B_monthly_drift',dB)]:
        delta=d-eI; lo,hi=mbb(delta,P['BLOCK_MONTHS'],P['B_RESAMPLES'],seed)
        res['primary_'+name]=dict(mean_dev_strategy=float(d.mean()),mean_dev_index=float(eI.mean()),delta=float(delta.mean()),ci95=[lo,hi],passes=bool(hi<0))
    # log-scale secondary
    for name,H in [('A',HA),('B',HB)]:
        res['secondary_logdev_'+name]=dict(strategy=float(np.mean(np.abs(np.log(np.maximum(H,1e-12))))),index=float(np.mean(np.abs(np.log(np.maximum(HI,1e-12))))))
    # premise frequency and post-jump behaviour (Q = RV_k / RV_{k-1})
    Q=RV[1:]/RV[:-1]; jump=np.where(Q>P['GAMMA'])[0]
    res['premise']=dict(Q_gt_gamma=int((Q>P['GAMMA']).sum()),pairs=int(len(Q)),freq=float((Q>P['GAMMA']).mean()))
    nxt=[Q[j+1] for j in jump if j+1<len(Q)]
    res['post_jump']=dict(events=len(jump),next_month_Q_mean=float(np.mean(nxt)) if nxt else None,next_month_Q_median=float(np.median(nxt)) if nxt else None,
                           next_month_Q_gt_1=int(sum(q>1 for q in nxt)),next_month_Q_gt_gamma=int(sum(q>P['GAMMA'] for q in nxt)))
    # net metrics and gates
    for name,r in [('A_daily_maintained',rA),('B_monthly_drift',rB),('index',rIdx)]:
        m=metrics(r,rfs); res['metrics_'+name]=m
    res['turnover_per_year']=dict(A=float(turnA/yrs),B=float(turnB/yrs))
    gates={}
    for name in ['A_daily_maintained','B_monthly_drift']:
        m=res['metrics_'+name]
        gates[name]=dict(drawdown_ok=bool(m['max_dd']<=P['DD_LIMIT']),day_ok=bool(-m['worst_day']<=P['DAY_LIMIT']),underwater_ok=bool(m['longest_underwater_months']<=P['UW_MONTHS_LIMIT']),
                         turnover_ok=bool(res['turnover_per_year'][name[0]]<=P['TURNOVER_LIMIT']))
    res['practical_gates']=gates
    # theorem integrity: drag <= sharp bound and <= constant when Q<=gamma, per month, in theorem convention (daily maintained, no costs)
    viol_sharp=viol_const=capviol=0;chk=0
    Lmax=P['L_MAX'];M=P['M_CAP'];V=P['V_TAR']
    Cconst=(Lmax-1)/Lmax*P['GAMMA']*V/(2*(1-M)*(1-Lmax*M))
    for k in range(start,K):
        ii=idxs[k]; xk=x[ii]; Lk=L[k]
        if np.max(np.abs(xk))>M: capviol+=1; continue
        chk+=1
        D=float(np.sum(Lk*np.log1p(xk)-np.log1p(Lk*xk)))
        if Lk>1:
            S=(Lk*math.log(1-M)-math.log(1-Lk*M))/M**2
            if D>S*RV[k]+1e-12: viol_sharp+=1
        elif D>1e-12: viol_sharp+=1
        if RV[k]<=P['GAMMA']*RV[k-1] and D>Cconst+1e-12: viol_const+=1
    res['theorem_integrity']=dict(months_checked=chk,months_cap_exceeded=capviol,sharp_violations=viol_sharp,const_violations_when_premise_holds=viol_const,C_const=Cconst)
    return res
if __name__=='__main__':
    path,seed,label=sys.argv[1],int(sys.argv[2]),sys.argv[3]
    print(json.dumps(run(path,seed,label),indent=1))
