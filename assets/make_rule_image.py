# Renders assets/rule-plain.png (the leverage rule). Run: python assets/make_rule_image.py
import os, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
plt.rcParams['font.family']='STIXGeneral'; plt.rcParams['mathtext.fontset']='stix'
fig=plt.figure(figsize=(8,2.0),dpi=300); fig.patch.set_facecolor('white')
ax=fig.add_axes([0,0,1,1]); ax.set_xlim(0,8); ax.set_ylim(0,2); ax.axis('off')
ax.text(4,1.2,r'$L_k\;=\;\min\!\left(\,1.5,\;\sqrt{\dfrac{V_{\mathrm{target}}}{RV_{k-1}}}\,\right)$',fontsize=26,color='black',ha='center',va='center')
ax.text(4,0.28,r'$V_{\mathrm{target}}=0.002$ per month (about 15.5% a year);  $RV_{k-1}$ = last month’s realised variance',fontsize=10,color='#444444',ha='center',va='center')
fig.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)),'rule-plain.png'),dpi=300,facecolor='white')
