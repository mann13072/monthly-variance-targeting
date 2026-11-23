# make_paper.py v3 -- three-page two-column paper; math typeset with matplotlib mathtext (STIX), numbers read from formal/results/*.json
import json, os, io, hashlib
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.mathtext import math_to_image
from matplotlib.font_manager import FontProperties
from PIL import Image as PILImage
from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.lib import colors
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.enums import TA_JUSTIFY, TA_CENTER, TA_LEFT
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import BaseDocTemplate, PageTemplate, Frame, Paragraph, Spacer, Table, TableStyle, FrameBreak, NextPageTemplate, KeepTogether, Image
BASE=os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..'))+'/'
R=BASE+'results/'
OUT=BASE+'paper/volatility_targeting_paper.pdf'
MD=BASE+'paper/math/'
os.makedirs(MD,exist_ok=True)
BODY=float(os.environ.get('BODY','10'))
DPI=400
fd=os.path.join(matplotlib.get_data_path(),'fonts','ttf')
for n,f in [('STIX','STIXGeneral.ttf'),('STIX-B','STIXGeneralBol.ttf'),('STIX-I','STIXGeneralItalic.ttf'),('STIX-BI','STIXGeneralBolIta.ttf')]:
    pdfmetrics.registerFont(TTFont(n,os.path.join(fd,f)))
pdfmetrics.registerFontFamily('STIX',normal='STIX',bold='STIX-B',italic='STIX-I',boldItalic='STIX-BI')
plt.rcParams['font.family']='STIXGeneral';plt.rcParams['mathtext.fontset']='stix'
def M(tex,size=None):
    size=size or BODY
    key=hashlib.md5((tex+str(size)).encode()).hexdigest()[:16];path=MD+key+'.png'
    buf=io.BytesIO();depth=math_to_image('$'+tex+'$',buf,prop=FontProperties(size=size),dpi=DPI,format='png',color='black')
    im=PILImage.open(io.BytesIO(buf.getvalue()));w,h=im.size;im.save(path)
    return '<img src="%s" width="%.2f" height="%.2f" valign="%.2f"/>'%(path,w/DPI*72,h/DPI*72,-depth/DPI*72)
MINUS=chr(0x2212)
J=lambda n:json.load(open(R+n))
reg={k:J('practical_%s_2026-11-22.json'%k) for k in ['Europe','Japan','Asia_Pacific_ex_Japan']}
cor=J('practical_cagr_vol_correction_2026-11-22.json')
PH=J('posthoc_benchmarks_2026-11-23.json');RC=J('review_recheck_2026-11-23.json')
sens=J('practical_cost_sensitivity_2026-11-22.json')
etf=J('etf_shortfall_exploratory_2026-11-22.json');sso=etf['SSO (2x)'];spy=etf['SPY (1x)'];xs=J('xs2d_shortfall_exploratory_2026-11-22.json')['XS2D.L (USD line, LSE close)']
acc=J('account_sim_100k_2026-11-22.json');a5=acc['USD line, 5 bp'];a15=acc['EUR route modelled + FX, 15 bp + 30 bp'];ix=acc['comparators']['index_total_return']
f3=lambda v:('%.3f'%v).replace('-',MINUS);f2=lambda v:('%.2f'%v).replace('-',MINUS);p1=lambda v:'%.1f'%(v*100);p2=lambda v:'%.2f'%(v*100)
s3=lambda v:('+' if v>0 else '')+f3(v)
def dci(o): return '%s [%s, %s]'%(s3(o['delta']),s3(o['ci95'][0]),s3(o['ci95'][1]))
FEE_RANGE='%d–%d'%(round(min(PH[k]['fee_bp_at_60bp_fund_fee'] for k in PH)),round(max(PH[k]['fee_bp_at_60bp_fund_fee'] for k in PH)))
UW=lambda r,k:round(r[k]['longest_underwater_months']*21/(r['days']/(r['months']+1)))
names={'Europe':'Europe','Japan':'Japan','Asia_Pacific_ex_Japan':'Asia Pacific*'}
eu,jp,ap=reg['Europe'],reg['Japan'],reg['Asia_Pacific_ex_Japan']
def corr_cagr(k,lab):
    c=cor[k];return ((1+sens[k+'_'+lab]['B_cagr'])**(c['rep_years']/c['true_years'])-1)*100
DROPS=[corr_cagr(k,'base')-corr_cagr(k,'double') for k in ('Europe','Japan','Asia_Pacific_ex_Japan')]
# ---------------- figures
def fig1():
    fig,ax=plt.subplots(2,1,figsize=(3.45,2.7),dpi=300)
    ks=list(names);x=range(len(ks));w=0.36
    s=[reg[k]['primary_B_monthly_drift']['mean_dev_strategy'] for k in ks];i=[reg[k]['primary_B_monthly_drift']['mean_dev_index'] for k in ks]
    ax[0].bar([a-w/2 for a in x],i,w,color='#9aa5b1',label='unlevered index');ax[0].bar([a+w/2 for a in x],s,w,color='#1f4e79',label='variance-targeting rule')
    for a,k in zip(x,ks):
        ax[0].text(a,max(s[a],i[a])+0.05,r'$\Delta=%s$'%('%.2f'%reg[k]['primary_B_monthly_drift']['delta']).replace('-','-'),ha='center',fontsize=6.8)
    ax[0].set_xticks(list(x));ax[0].set_xticklabels([names[k] for k in ks],fontsize=7);ax[0].set_ylabel(r'mean $|$realised/target $-1|$',fontsize=6.6);ax[0].tick_params(labelsize=6.6);ax[0].legend(fontsize=6.2,frameon=False,loc='upper left');ax[0].set_ylim(0,1.7)
    ax[0].set_title('(a) Primary test: deviation from target variance (lower is better)',fontsize=6.9,loc='left')
    sc=[cor[k]['B_cagr'][1]*100 for k in ks];ic=[cor[k]['index_cagr'][1]*100 for k in ks]
    ax[1].bar([a-w/2 for a in x],ic,w,color='#9aa5b1');ax[1].bar([a+w/2 for a in x],sc,w,color='#1f4e79')
    for a in x:
        ax[1].text(a-w/2,ic[a]+0.15,'%.1f'%ic[a],ha='center',fontsize=6.2);ax[1].text(a+w/2,sc[a]+0.15,'%.1f'%sc[a],ha='center',fontsize=6.2)
    ax[1].set_xticks(list(x));ax[1].set_xticklabels([names[k] for k in ks],fontsize=7);ax[1].set_ylabel('CAGR, % a year',fontsize=6.6);ax[1].tick_params(labelsize=6.6);ax[1].set_ylim(0,10.8)
    ax[1].set_title('(b) Net return: the rule earns less than the index',fontsize=6.9,loc='left')
    for a in ax:
        a.spines['top'].set_visible(False);a.spines['right'].set_visible(False)
    fig.tight_layout(pad=0.4);fig.savefig(BASE+'paper/fig1.png');plt.close(fig)
def fig2():
    rows=[r for r in sso['year[year, drag%, fund_impl%, vol%]'] if 2007<=int(r[0])<=2025]
    fig,ax=plt.subplots(figsize=(3.45,1.85),dpi=300)
    yrs=[int(r[0]) for r in rows];d=[r[1] for r in rows];im=[r[2] for r in rows]
    ax.bar(yrs,d,color='#1f4e79',label='exact daily-reset drag');ax.bar(yrs,im,bottom=d,color='#c98a2b',label='fund implementation shortfall')
    ax.set_ylabel('% of capital, per year',fontsize=6.6);ax.tick_params(labelsize=6.4);ax.legend(fontsize=6.2,frameon=False,loc='upper right')
    ax.set_title(r'Shortfall of a $2\times$ daily-reset fund (SSO) against its ideal',fontsize=6.9,loc='left')
    ax.spines['top'].set_visible(False);ax.spines['right'].set_visible(False)
    ax.set_xticks(yrs[::2]);fig.tight_layout(pad=0.4);fig.savefig(BASE+'paper/fig2.png');plt.close(fig)
fig1();fig2()
# ---------------- styles
body=ParagraphStyle('b',fontName='STIX',fontSize=BODY,leading=BODY*1.27,alignment=TA_JUSTIFY,spaceAfter=3.2)
h1=ParagraphStyle('h',parent=body,fontName='STIX-B',fontSize=BODY+0.8,leading=BODY*1.3,spaceBefore=6,spaceAfter=2.4,alignment=TA_LEFT,keepWithNext=1)
ttl=ParagraphStyle('t',fontName='STIX-B',fontSize=14.2,leading=17,alignment=TA_CENTER,spaceAfter=5)
auth=ParagraphStyle('a',fontName='STIX',fontSize=10.5,leading=12.5,alignment=TA_CENTER,spaceAfter=1)
abs_=ParagraphStyle('ab',parent=body,fontSize=BODY-0.4,leading=BODY*1.17,leftIndent=16,rightIndent=16,spaceAfter=2)
cap=ParagraphStyle('c',parent=body,fontSize=BODY-1.5,leading=BODY*1.0,alignment=TA_JUSTIFY,spaceAfter=5)
ref=ParagraphStyle('r',parent=body,fontSize=BODY-1.2,leading=BODY*1.08,leftIndent=11,firstLineIndent=-11,spaceAfter=1.6)
cell=ParagraphStyle('cl',fontName='STIX',fontSize=7.6,leading=9,alignment=TA_CENTER)
cellb=ParagraphStyle('cb',parent=cell,fontName='STIX-B')
numst=ParagraphStyle('n',fontName='STIX',fontSize=BODY,leading=BODY*1.2,alignment=2)
def P(t,s=body): return Paragraph(t,s)
M_=lambda t:M(t)
M1=M('x_t');
M2=lambda t:M(t)
colw=(letter[0]-2*0.7*inch-0.24*inch)/2
def EQ(tex,n):
    buf=io.BytesIO();depth=math_to_image('$'+tex+'$',buf,prop=FontProperties(size=BODY+1.0),dpi=DPI,format='png',color='black')
    im=PILImage.open(io.BytesIO(buf.getvalue()));w,h=im.size;key=hashlib.md5((tex+'eq').encode()).hexdigest()[:16];path=MD+key+'.png';im.save(path)
    wp=w/DPI*72;hp=h/DPI*72;avail=colw-0.42*inch
    if wp>avail:
        hp*=avail/wp;wp=avail
    t=Table([[Image(path,width=wp,height=hp),Paragraph('(%d)'%n,numst)]],colWidths=[colw-0.42*inch,0.42*inch],hAlign='LEFT')
    t.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'MIDDLE'),('ALIGN',(0,0),(0,0),'CENTER'),('TOPPADDING',(0,0),(-1,-1),3),('BOTTOMPADDING',(0,0),(-1,-1),4),('LEFTPADDING',(0,0),(-1,-1),0),('RIGHTPADDING',(0,0),(-1,-1),0)]))
    return t
def tbl(data,widths):
    d=[[Paragraph(str(c),cellb if i==0 else cell) for c in r] for i,r in enumerate(data)]
    t=Table(d,colWidths=widths,hAlign='CENTER')
    t.setStyle(TableStyle([('LINEABOVE',(0,0),(-1,0),0.9,colors.black),('LINEBELOW',(0,0),(-1,0),0.45,colors.black),('LINEBELOW',(0,-1),(-1,-1),0.9,colors.black),('TOPPADDING',(0,0),(-1,-1),2.2),('BOTTOMPADDING',(0,0),(-1,-1),2.6),('LEFTPADDING',(0,0),(-1,-1),1.5),('RIGHTPADDING',(0,0),(-1,-1),1.5),('VALIGN',(0,0),(-1,-1),'MIDDLE')]))
    return t
def row(k):
    r=reg[k];b=r['primary_B_monthly_drift'];m=r['metrics_B_monthly_drift'];i=r['metrics_index'];c=cor[k]
    return [names[k],'%s<br/>[%s, %s]'%(f3(b['delta']),f3(b['ci95'][0]),f3(b['ci95'][1])),'%d / %d'%(r['premise']['Q_gt_gamma'],r['premise']['pairs']),'%s / %s'%(p2(c['B_cagr'][1]),p2(c['index_cagr'][1])),'%s / %s'%(p1(m['max_dd']),p1(i['max_dd'])),'%d / %d'%(UW(r,'metrics_B_monthly_drift'),UW(r,'metrics_index'))]
DRAGROWS=[['Leverage <i>L</i>','<i>σ</i> = 15%','<i>σ</i> = 20%','<i>σ</i> = 30%']]+[['%.1f'%L]+['%.2f'%(L*(L-1)/2*s*s*100) for s in (0.15,0.20,0.30)] for L in (1.5,2.0,3.0)]
COSTROWS=[['Region','Half costs','Base costs','Double costs']]+[[names[k]]+['%.2f'%corr_cagr(k,l) for l in ('half','base','double')] for k in ('Europe','Japan','Asia_Pacific_ex_Japan')]
SB=BODY-2.8
def v(b,s,size=None):
    s=s.replace(chr(0x2212),'-')
    sub=(r'\mathrm{%s}'%s) if (len(s)>1 and s.isalpha()) else s
    return M(b+'_{'+sub+'}',size)
S=[]
S.append(P('Does Monthly Variance Targeting Improve on Fixed Equity Exposure?<br/>Evidence from Europe and Japan',ttl))
S.append(P('Mann Shah<br/><i>Independent Researcher</i><br/>13072mann@gmail.com',auth))
S.append(P('Draft, 23 November 2026. Research, not investment advice.',auth))
S.append(Spacer(1,4))
S.append(P(f"<b>Abstract.</b> We ask one prespecified question: does a rule that sets each month's leverage (capped at 1.5×) from the previous month's realised variance keep next month's realised variance closer to a fixed target than holding the unlevered index? On Ken French daily data for Europe and Japan (1990–2026, USD), with the plan and code frozen before any return statistic was computed on these files, the rule reduced the mean absolute deviation from target in both regions (Δ = {dci(eu['primary_B_monthly_drift'])} and {dci(jp['primary_B_monthly_drift'])}); both met the prespecified bootstrap criterion. The gains are concentrated in 2000–09. In post hoc comparisons without costs, against exposure scaled by expanding historical variance the rule did better in Europe (Δ = {dci(PH['Europe']['vs_expanding'])}), but not once 2000–09 is excluded ({dci(PH['Europe']['vs_expanding_excl_2000_09'])}), and it did worse in Japan ({dci(PH['Japan']['vs_expanding'])}). Net return was <b>lower than the index</b> in every region and absolute drawdown limits were <b>not met</b>. A variance jump above 4× occurred in 4.4% of months. We also give a machine-checked (Lean 4) form of a pathwise leveraged-drag bound, a corollary of Brown's results (no novelty claimed). Fund implementation costs measured on SSO and XS2D were about 1.6% a year per unit of a 2× fund beyond drag; a USD 100,000 account replay is development evidence only.",abs_))
S.append(NextPageTemplate('later'));S.append(FrameBreak())
# ---- 1
S.append(P('1. Question and hypothesis',h1))
S.append(P('Let '+v('m','t')+' be the daily simple return of an equity index, '+v('c','t')+' the risk-free return and '+v('x','t')+' = ('+v('m','t')+' − '+v('c','t')+')/(1 + '+v('c','t')+') the excess return. A portfolio at leverage <i>L</i> that is reset daily earns '+v('c','t')+' + <i>L</i>('+v('m','t')+' − '+v('c','t')+'), so its growth factor is (1 + '+v('c','t')+')(1 + <i>L</i>'+v('x','t')+'). For calendar month <i>k</i> let '+v('RV','k')+' be the sum of '+M('x_t^2')+' over its trading days. The rule under test sets the month-<i>k</i> leverage from the previous month:'))
S.append(EQ(r'L_k=\min\left(L_{\max},\ \sqrt{V_{\mathrm{tar}}/RV_{k-1}}\right),\quad L_{\max}=1.5,\ V_{\mathrm{tar}}=0.0020',1))
S.append(P('where '+v('V','tar')+' is per month (about 15.5% a year). If the cap does not bind, the realised variance of month <i>k</i> equals '+v('H','k')+v('V','tar')+', with'))
S.append(EQ(r'H_k=\frac{L_k^{2}\,RV_k}{V_{\mathrm{tar}}}=Q_k\,\min\left(1,\ \frac{L_{\max}^{2}\,RV_{k-1}}{V_{\mathrm{tar}}}\right),\qquad Q_k=\frac{RV_k}{RV_{k-1}}.',2))
S.append(P('<b>Hypothesis.</b> The rule lowers the mean absolute deviation of realised monthly variance from target relative to the unlevered index. The prespecified primary statistic is'))
S.append(EQ(r'\Delta=\mathrm{mean}_k\left(\left|H_k-1\right|-\left|\frac{RV_k}{V_{\mathrm{tar}}}-1\right|\right),',3))
S.append(P('computed on a tradable monthly implementation whose weight drifts inside the month. A region passes if the upper end of the 95% moving-block bootstrap interval of Δ (3-month blocks, 2,000 resamples) is below 0, and the test passes only if both Europe and Japan pass. The question is about risk control; return is reported but is not part of the hypothesis.'))
S.append(P('<b>Contributions.</b> (a) A prespecified, frozen test on regional data not previously analysed, with its failures reported. (b) Post hoc comparisons that show how far the result depends on the benchmark and on one decade. (c) A machine-checked finite-sum form of a known drag bound (credited to Brown; no novelty claimed), and cost and implementation checks that separate the theorem, the premise and the tradable portfolio.'))
# ---- 2
S.append(P('2. Theorem and prior art',h1))
S.append(P('The drag of leverage <i>L</i> ≥ 1 over a window is'))
S.append(EQ(r'D=\sum_t\left[L\ln(1+x_t)-\ln(1+Lx_t)\right]\ \geq\ 0.',4))
S.append(P('If |'+v('x','t')+'| ≤ <i>M</i> on every day and <i>LM</i> &lt; 1, then for every path'))
S.append(EQ(r'D\ \leq\ S(L,M)\sum_t x_t^{2},\qquad S(L,M)=\frac{L\ln(1-M)-\ln(1-LM)}{M^{2}}.',5))
S.append(P('The coefficient is sharp (a single day at −<i>M</i> attains it); <i>S</i>(1.5, 0.2) = 0.549. If '+v('RV','k')+' ≤ <i>γ</i>'+v('RV','k−1')+', the rule gives a monthly drag of at most'))
S.append(EQ(r'\frac{L_{\max}-1}{L_{\max}}\cdot\frac{\gamma\,V_{\mathrm{tar}}}{2(1-M)(1-L_{\max}M)},',6))
S.append(P('which is 0.00238 for <i>γ</i> = 4 (0.00195 if (5) is used; that combination is checked numerically, not in Lean). A jump above 4× voids the guarantee for that month without falsifying the deduction. A signed cubic floor also holds. For <i>L</i> &gt; 1, 1 + <i>L</i>'+v('x','t')+' &gt; 0 on every day and <i>τ</i> &gt; 0,'))
S.append(EQ(r'D\ \geq\ \left[\frac{L(L-1)}{2}-\frac{L(L-1)(L+1)}{3}\,\tau\right]\sum_t x_t^{2}\quad\mathrm{whenever}\ \sum_t x_t^{3}\leq\tau\sum_t x_t^{2}.',7))
S.append(P('For <i>L</i> = 2 and <i>τ</i> = 0.01 the floor is 0.98 times the realised variance.'))
S.append(KeepTogether([tbl(DRAGROWS,[0.9*inch,0.75*inch,0.75*inch,0.75*inch]),P('<b>Table 1.</b> Approximate annual drag, <i>L</i>(<i>L</i>−1)<i>σ</i><super size="'+str(SB)+'">2</super>/2 (the leading-order term of the drag; the coefficient of the bound is <i>S</i>), in % of capital, for annual index volatility <i>σ</i>.',cap)]))
S.append(P('<b>Machine check.</b> Statement (5), the <i>γ</i>-ratio bound with the first constant and the cubic floor are proved in Lean 4.37.0-rc1 with Mathlib v4.37.0-rc1, using only the axioms propext, Classical.choice and Quot.sound and no <i>sorry</i>. Lean checks the deduction from the stated assumptions; it does not check the data. <b>Prior art.</b> Brown [1] states the pointwise inequality ln(1 + <i>Lx</i>) ≤ <i>L</i> ln(1 + <i>x</i>) (Remark 4) and gives quadratic bounds on the leveraged log-return in terms of the index’s daily log-returns (Theorem 1). Statement (5) is a bound of the same kind in simple-return form; we proved it directly in Lean and did not derive it from Theorem 1. Our contribution is the checked finite-sum form and its use with a leverage rule, not a new inequality. Avellaneda and Zhang [3] give an exact formula linking a leveraged fund’s return to its realised variance. Bongaerts, Kang and van Dijk [4] scale equity exposure by the previous month’s realised volatility, as the rule here does, and report that conventional volatility targeting does not consistently improve performance and can raise drawdowns; they judge it by Sharpe ratios, drawdowns and tail risk, while we judge it by how close realised variance stays to a fixed target. They also note that the scaling factors of Moreira and Muir [5] and Harvey et al. [6] are constructed ex post, which is the look-ahead issue behind our past-data benchmark, and Cederburg et al. [7] is a concurrent study of volatility-managed portfolios. We know [5]–[7] from the reference list of [4] and from bibliographic records, not from their texts.'))
# ---- 3
S.append(P('3. Data and prespecification',h1))
S.append(P('We use the Ken French daily three-factor files [2]: Europe and Japan, 9,458 trading days each (1990-07-02 to 2026-09-30), in USD; '+v('m','t')+' − '+v('c','t')+' is Mkt−RF and '+v('c','t')+' is RF. Asia Pacific ex Japan is reported but is not in the pass rule; North America and Developed overlap the US file and are excluded.'))
S.append(P('The rule, the statistic, the costs (5 bp per dollar traded, 50 bp a year on borrowing, 50 bp a year fund fee), the gates and the decision rule were <b>frozen on 2026-11-22 at 16:22:24 UTC</b> (code SHA-256 dd67fd2e…, plan 676ee670…; seeds 20260902 Europe, 20260903 Japan, 20260904 Asia Pacific). The regional files were downloaded and integrity-checked about 33 minutes before the freeze; no return statistic had been computed on either file. The freeze is documented only by local hashes and timestamps, with no external registration, and “prespecified” refers to that record. The primary statistic was computed once by the frozen script; later analyses on the same files (cost sensitivity, corrections, fund replays) are secondary.'))
S.append(P('<b>Development evidence.</b> The US file (1926–2026) was used to debug the code before the freeze, and a literature report had already stated summary statistics computed on it. It is therefore development evidence only and is not used for confirmation.'))
# ---- 4
S.append(P('4. Results (confirmatory)',h1))
S.append(KeepTogether([tbl([['Region','Δ<br/>[95% CI]','<i>Q</i> &gt; 4','CAGR %<br/>rule / index','Max DD %<br/>rule / index','Under water (mo.)<br/>rule / index'],row('Europe'),row('Japan'),row('Asia_Pacific_ex_Japan')],[0.60*inch,0.80*inch,0.40*inch,0.56*inch,0.56*inch,0.51*inch]),P('<b>Table 2.</b> Monthly-drift implementation, 434 months per region, costs 5/50/50 bp. Δ is the primary statistic; <i>Q</i> &gt; 4 counts month pairs with '+v('RV','k',BODY-1.5)+' &gt; 4'+v('RV','k−1',BODY-1.5)+'. CAGR uses calendar years; months under water use 21.74 trading days a month. *Not in the pass rule.',cap)]))
S.append(KeepTogether([Image(BASE+'paper/fig1.png',width=3.4*inch,height=3.4*inch*2.7/3.45),P('<b>Figure 1.</b> (a) Mean absolute deviation of realised monthly variance from target, rule against index. (b) Net CAGR.',cap)]))
S.append(P(f"<b>The primary test passed in both regions.</b> The rule kept realised monthly variance nearer the target than the index (mean deviation {f3(eu['primary_B_monthly_drift']['mean_dev_strategy'])} against {f3(eu['primary_B_monthly_drift']['mean_dev_index'])} in Europe, {f3(jp['primary_B_monthly_drift']['mean_dev_strategy'])} against {f3(jp['primary_B_monthly_drift']['mean_dev_index'])} in Japan), and trading monthly instead of daily changed the score by less than 0.003."))
PHE,PHJ,PHA=PH['Europe'],PH['Japan'],PH['Asia_Pacific_ex_Japan']
def phrow(lbl,key): return [lbl]+[dci(PH[k][key]).replace(' [','<br/>[') for k in ('Europe','Japan','Asia_Pacific_ex_Japan')]
S.append(P(f"<b>The result depends on the benchmark and on one decade (post hoc).</b> The target (about 15.5% a year) is below the index's usual variance: average realised monthly variance is {PHE['mean_RV_over_target']:.2f} times the target in Europe and {PHJ['mean_RV_over_target']:.2f} times in Japan, so the index is penalised on level. Against exposure set by the mean of all past monthly variances (same cap; an implementable benchmark) the rule did better in Europe and worse in Japan (Table 4). Excluding 2000–09 the rule's edge over the index shrinks (Europe {dci(PHE['vs_index_excl_2000_09'])}, with the upper end within 0.01 of zero and sensitive to the bootstrap seed; Japan {dci(PHJ['vs_index_excl_2000_09'])}), its edge over the past-data benchmark is not distinguishable from zero in Europe, and the rule stays worse in Japan. Mean Δ against the index by decade (1990s, 2000s, 2010s, 2020s): Europe {s3(PHE['by_decade']['1990-99'])}, {s3(PHE['by_decade']['2000-09'])}, {s3(PHE['by_decade']['2010-19'])}, {s3(PHE['by_decade']['2020-26'])}; Japan {s3(PHJ['by_decade']['1990-99'])}, {s3(PHJ['by_decade']['2000-09'])}, {s3(PHJ['by_decade']['2010-19'])}, {s3(PHJ['by_decade']['2020-26'])}. The rule was closer to target in {PHE['share_months_rule_closer']*100:.0f}% of months in Europe and {PHJ['share_months_rule_closer']*100:.0f}% in Japan; the monthly differences correlate {RC['corr_delta_series']['EU_JP']:.2f} across the two. With 6- and 12-month bootstrap blocks the intervals against the index stay below 0 (Europe upper ends {s3(PHE['vs_index_block6']['ci95'][1])} and {s3(PHE['vs_index_block12']['ci95'][1])}; Japan {s3(PHJ['vs_index_block6']['ci95'][1])} and {s3(PHJ['vs_index_block12']['ci95'][1])}). Leverage was below 1 in {PHJ['share_L_below_1']*100:.0f}% of months in Japan (mean {PHJ['mean_L']:.2f}) and {PHE['share_L_below_1']*100:.0f}% in Europe (mean {PHE['mean_L']:.2f}), so much of the Japanese gain is de-risking."))
S.append(KeepTogether([tbl([['Post hoc, Δ [95% CI]','Europe','Japan','Asia Pacific*'],phrow('vs index, excluding 2000–09','vs_index_excl_2000_09'),phrow('vs past-data benchmark','vs_expanding'),phrow('vs past-data benchmark, excluding 2000–09','vs_expanding_excl_2000_09')],[1.0*inch,0.81*inch,0.81*inch,0.81*inch]),P('<b>Table 4.</b> Post hoc comparisons, no costs (daily-maintained rule), 3-month blocks, 4,000 resamples, seed 20261123. Past-data benchmark: leverage from the mean of all earlier monthly variances, same cap. Negative Δ favours the rule. *Not in the pass rule.',cap)]))
S.append(P(f"<b>Return was lower than the index in all three regions</b>, by {(cor['Europe']['index_cagr'][1]-cor['Europe']['B_cagr'][1])*100:.2f}, {(cor['Japan']['index_cagr'][1]-cor['Japan']['B_cagr'][1])*100:.2f} and {(cor['Asia_Pacific_ex_Japan']['index_cagr'][1]-cor['Asia_Pacific_ex_Japan']['B_cagr'][1])*100:.2f} points a year; doubling costs lowers it by a further {min(DROPS):.2f}–{max(DROPS):.2f} points (Table 3). The absolute limits (drawdown 40%, one-day loss 10%, 36 months under water) were not met by the rule in Europe or Japan, nor by the index in any region; in Asia Pacific the rule met only the one-day limit. In Japan the rule drew down more ({p1(jp['metrics_B_monthly_drift']['max_dd'])}% against {p1(jp['metrics_index']['max_dd'])}%) and stayed under water {UW(jp,'metrics_B_monthly_drift')} months against {UW(jp,'metrics_index')}. Measured fund implementation shortfall (Section 5) is about {a5['avg_fund_weight']*sso['fund_impl_pa']*100:.2f}% of capital a year at the average fund weight of {a5['avg_fund_weight']:.2f}, which is above the base-case fee and borrowing charge; the double-cost case is a higher-cost sensitivity, not an estimate of any fund's cost."))
S.append(P(f"<b>The premise fails about 4% of the time.</b> A variance jump above 4× occurred in {eu['premise']['Q_gt_gamma']} of {eu['premise']['pairs']} month pairs (4.4%) in each region; the next month's ratio then had median {f2(eu['post_jump']['next_month_Q_median'])} (Europe), {f2(jp['post_jump']['next_month_Q_median'])} (Japan) and {f2(ap['post_jump']['next_month_Q_median'])} (Asia Pacific). Variance usually falls back, so the rule is under-invested right after a spike. Theorem integrity held: 0 violations of (5) in 434 months per region, and the move cap was never exceeded."))
# ---- 5
S.append(P('5. Implementation (development evidence)',h1))
S.append(P(f"<b>Fund shortfall.</b> We split the log shortfall of a 2× daily-reset fund against its ideal target into the exact drag and a fund implementation term (provisional, unofficial prices; Figure 2). SSO (2006–2026, 20.2 years) loses {p2(sso['total_shortfall_pa'])}% a year in total, made of {p2(sso['drag_pa'])}% drag and {p2(sso['fund_impl_pa'])}% implementation; the 1× control SPY loses {p2(spy['total_shortfall_pa'])}%. For the UCITS fund XS2D (2010–2026, LSE USD line) the figures are {p2(xs['total_pa'])}% = {p2(xs['drag_pa'])}% + {p2(xs['impl_pa'])}%, so a lower disclosed fee (0.60% for XS2D against about 0.9% for SSO, the latter unverified) did not lower the total. The exact drag is about the variance of the index and peaks in 2008 and 2020."))
S.append(KeepTogether([Image(BASE+'paper/fig2.png',width=3.4*inch,height=3.4*inch*1.85/3.45),P('<b>Figure 2.</b> Annual drag and fund implementation shortfall of SSO against its ideal 2× daily reset.',cap)]))
S.append(P(f"<b>A USD 100,000 account.</b> With whole shares, no borrowing and a 2× fund held at weight <i>L</i>/2, the frozen rule over 2010-05 to 2026-09 (16.4 years; a bull-market window with no 2000 or 2008 type crash) ended at USD {a5['final_value']:,.0f} with a maximum drawdown of {p1(a5['max_dd'])}% (execution cost 5 bp, costs paid USD {a5['total_costs_usd']:,.0f}), and at USD {a15['final_value']:,.0f} in a pessimistic currency-conversion case. The S&amp;P 500 total return index ended at USD {ix['final_value']:,.0f} with a drawdown of {p1(ix['max_dd'])}%. The rule gave up return for a smaller drawdown; this replay is not a test. The EUR line of the same fund could not be used because its public series has bad ticks, so the currency route was modelled from the USD line."))
S.append(KeepTogether([tbl(COSTROWS,[0.9*inch,0.8*inch,0.8*inch,0.8*inch]),P('<b>Table 3.</b> Rule CAGR (%) at half, base and double costs (calendar-year CAGR); the primary statistic does not change with costs.',cap)]))
S.append(P('At the planned fund weight <i>L</i>/2 in a 2× fund the portfolio fee (fund fee times average weight) would be '+FEE_RANGE+' bp a year at a 0.60% fund fee (Europe, Japan and Asia Pacific average weights), inside a 50 bp limit on total capital. <b>Prospective test.</b> A 12-month paper trade has a frozen protocol (variance score <i>Z</i> ≤ 1.336, frozen 2026-11-22 16:56:58 UTC). It has <b>not</b> started; it can verify execution and costs, not the confirmatory claim above.'))
# ---- 6
S.append(P('6. Limitations',h1))
S.append(P('(i) Europe and Japan share global shocks (1998, 2008, 2020): they are two looks, not two independent tests (their monthly differences from the index correlate about 0.6). (ii) The series are USD factor returns, not funds; public fund prices are unofficial and the UCITS NAV was not obtained. (iii) The frozen script annualised with 252 rows per year although the files hold about 261, which understated CAGR by about 3.6% and volatility by about 1.8% (CAGR and months under water are corrected here; the primary statistic, premise counts and drawdowns are unaffected). (iv) The primary statistic rewards volatility persistence: a synthetic market without persistence gave the opposite sign. (v) A search over investment designs on the US file reached higher returns only after four specifications on one data set and is excluded. (vi) The 4× threshold and <i>γ</i> are design choices and costs are research assumptions. (vii) The post hoc comparisons were run after the confirmatory results were seen, are exploratory, and some intervals lie close to zero.'))
# ---- 7
S.append(P('7. Conclusion',h1))
S.append(P('On regional data the rule was not tuned to, monthly variance targeting kept realised variance nearer the target than the unlevered index in both prespecified regions, at the cost of lower return and without meeting absolute loss limits. Post hoc, its advantage over an implementable benchmark that also scales exposure to the target is limited to Europe and to the 2000–09 decade, and the rule is worse in Japan. Whether a tradable fund reproduces any of this net of its own frictions remains open until the paper trade and official fund data exist.'))
S.append(P('<b>What the evidence shows.</b> (1) Against the unlevered index the prespecified test passed in Europe and Japan. (2) That advantage is not robust to the benchmark: against past-data scaling it holds in Europe only with 2000–09 included, and it reverses in Japan. (3) The premise (no more than a 4× monthly variance jump) failed in about 4.4% of months. (4) A finite-sum form of the known drag bound is machine-checked. <b>What it does not show.</b> That timing by last month’s variance beats past-data scaling in general, that the rule raises return (it lowered it), that absolute loss limits can be met (they were not), that a real fund reproduces the result net of its own costs, or that the inequality is new.'))
S.append(P('<b>Reproducibility.</b> Code, Lean sources, result files and SHA-256 hashes are in the project folder formal/ (practical_vt.py, posthoc_benchmarks_2026-11-23.py, paper/make_paper.py, results/*.json, results/freeze_practical_2026-11-22.txt); they are in the public repository github.com/mann13072/monthly-variance-targeting and archived on Zenodo (concept DOI 10.5281/zenodo.24461454, which always resolves to the latest version). The paper is licensed CC BY 4.0 and the code MIT (see the repository). Numbers in the abstract, tables and results text are read from results/*.json; dated constants (freeze times and hashes, the fund fee figures, the fee-weight range) are typed or derived in the text and are named as such.'))
S.append(P('<b>AI assistance.</b> Claude (Anthropic) wrote the code and the Lean proofs, ran the analyses, built the project wiki and drafted the text, working from the author’s design and decisions. A second AI agent was used to discuss the hypothesis. The author directed the work and is responsible for its content.'))
S.append(FrameBreak())
S.append(P('References',h1))
S.append(P('[1] H. Brown, Long-Term Returns Estimation of Leveraged Indexes and ETFs, Financial Markets and Portfolio Management 38(2), 165–190 (2024); arXiv:2301.03186 (2023). Theorem 1 and Remark 4 read in the preprint.',ref))
S.append(P('[2] K. R. French, Data Library, daily factor files for Europe, Japan, Asia Pacific ex Japan and the US (accessed 22 November 2026).',ref))
S.append(P('[3] M. Avellaneda and S. Zhang, Path-dependence of leveraged ETF returns, SIAM J. Financial Math. 1 (2010) 586–603; working-paper version of 19 May 2009 read.',ref))
S.append(P('[4] D. Bongaerts, X. Kang and M. van Dijk, Conditional volatility targeting, Financial Analysts Journal 76(4) (2020) 54–71; repository version read.',ref))
S.append(P('[5] A. Moreira and T. Muir, Volatility-managed portfolios, Journal of Finance 72(4) (2017) 1611–1644; cited as listed in [4], not read.',ref))
S.append(P('[6] C. R. Harvey, E. Hoyle, R. Korgaonkar, S. Rattray, M. Sargaison and O. Van Hemert, The impact of volatility targeting, Journal of Portfolio Management 45(1) (2018) 14–33; cited as listed in [4], not read.',ref))
S.append(P('[7] S. Cederburg, M. S. O’Doherty, F. Wang and X. Yan, On the performance of volatility-managed portfolios, Journal of Financial Economics 138(1) (2020) 95–117; details from a bibliographic record, not read.',ref))
M0=0.7*inch;W,Hh=letter;gap=0.24*inch;cw=(W-2*M0-gap)/2
def fr(x,y,w,h,i): return Frame(x,y,w,h,leftPadding=0,rightPadding=0,topPadding=0,bottomPadding=0,id=i)
hh=0.0
for _f in S[:5]:
    _w,_h=_f.wrap(W-2*M0,2000);hh+=_h+getattr(getattr(_f,'style',None),'spaceAfter',0)
title_h=hh+0.1*inch
first=PageTemplate(id='first',frames=[fr(M0,Hh-M0-title_h,W-2*M0,title_h,'T'),fr(M0,M0,cw,Hh-2*M0-title_h,'L1'),fr(M0+cw+gap,M0,cw,Hh-2*M0-title_h,'R1')],onPage=lambda c,d:(c.setFont('STIX',8),c.drawCentredString(W/2,0.4*inch,'1')))
later=PageTemplate(id='later',frames=[fr(M0,M0,cw,Hh-2*M0,'L'),fr(M0+cw+gap,M0,cw,Hh-2*M0,'R')],onPage=lambda c,d:(c.setFont('STIX',8),c.drawCentredString(W/2,0.4*inch,str(d.page))))
doc=BaseDocTemplate(OUT,pagesize=letter,pageTemplates=[first,later],title='Does Monthly Variance Targeting Improve on Fixed Equity Exposure? Evidence from Europe and Japan',author='Mann Shah')
doc.build(S)
print('built',OUT)
