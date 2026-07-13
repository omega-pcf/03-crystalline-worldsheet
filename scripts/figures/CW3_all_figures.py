"""
all_figures_v10.py — Six publication figures for The Crystalline Worldsheet v10.
Fig 1: alpha_s uniqueness | Fig 2: ER bridge identity
Fig 3: N_modes staircase  | Fig 4: Top-down Gauss-Eisenstein
Fig 5: AdS funnel+lattice+hypercube | Fig 6: Cylinder->Clifford torus
"""
import numpy as np, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.colors import LinearSegmentedColormap
from mpl_toolkits.mplot3d import Axes3D
import itertools

phi = (1+np.sqrt(5))/2; eps0 = np.log(phi)/(6*np.sqrt(3))
Mpcf = 6*np.sqrt(3)*np.pi/np.log(phi); lnphi = np.log(phi)
omega = np.exp(2j*np.pi/3)
def alpha(s): return np.arctan(eps0*phi**s)
def T_alg(s1,s2): return (1+eps0*phi**s1)/(1+eps0*phi**s2)
def T_trig(s1,s2):
    a1,a2=alpha(s1),alpha(s2)
    return np.sin(a1+np.pi/4)*np.cos(a2)/(np.sin(a2+np.pi/4)*np.cos(a1))

RC={'font.family':'serif','font.serif':['DejaVu Serif'],'mathtext.fontset':'stix',
    'font.size':12,'axes.labelsize':13,'axes.linewidth':0.8,'lines.linewidth':1.2}
plt.rcParams.update(RC)

def make_fig1():
    AE=0.1179
    def pred(s1,s2): return np.sin(alpha(s1))*np.cos(alpha(s2))
    N=9; sg=np.arange(N); S1,S2=np.meshgrid(sg,sg)
    PM=pred(S1,S2); EM=np.abs(PM-AE)/AE*100
    sf=np.linspace(0,8,60); F1,F2=np.meshgrid(sf,sf); PS=pred(F1,F2)
    assert np.unravel_index(EM.argmin(),EM.shape)==(3,2) and EM.min()<0.25
    fig=plt.figure(figsize=(14,7.5),facecolor='white')
    ax3=fig.add_axes([0.02,0.06,0.46,0.90],projection='3d')
    ax2=fig.add_axes([0.54,0.06,0.44,0.90])
    ax3.set_facecolor('white')
    for p in [ax3.xaxis.pane,ax3.yaxis.pane,ax3.zaxis.pane]: p.fill=False; p.set_edgecolor('#e0e0e0')
    grey=LinearSegmentedColormap.from_list('g',['#e8e8e8','#4a4a4a'])
    cs=grey((PS-PS.min())/(PS.max()-PS.min())); cs[...,3]=0.82
    ax3.plot_surface(F1,F2,PS,facecolors=cs,linewidth=0,antialiased=True,shade=True)
    ax3.plot_surface(F1,F2,np.full_like(PS,AE),color='#bb0000',alpha=0.18,linewidth=0)
    ax3.scatter(2,3,pred(2,3),s=80,c='#bb0000',edgecolors='white',linewidths=1,zorder=12)
    ax3.text(3.0,4.2,pred(2,3)+0.06,r'$(2,3)$: $0.1181$',fontsize=11,color='#bb0000',fontweight='bold')
    ax3.set_xlabel(r'$\sigma_1$'); ax3.set_ylabel(r'$\sigma_2$')
    ax3.set_zlabel(r'$\sin\alpha(\sigma_1)\cos\alpha(\sigma_2)$',fontsize=11)
    ax3.view_init(elev=26,azim=-52); ax3.set_box_aspect([1,1,0.62])
    ax3.text2D(0.03,0.95,'(a)',transform=ax3.transAxes,fontsize=13,fontweight='bold')
    cmap=LinearSegmentedColormap.from_list('e',['#145214','#3a8a3a','#c5e8c5','#ffffff','#f5c0c0','#cc4444','#880000'])
    im=ax2.imshow(np.clip(EM,0,160),cmap=cmap,aspect='equal',vmin=0,vmax=160,origin='lower',extent=[-0.5,8.5,-0.5,8.5])
    for i in range(N):
        for j in range(N):
            v=PM[j,i]; e=EM[j,i]; col='white' if e<10 or e>85 else '#111111'
            ax2.text(i,j,f'{v:.3f}\n{int(round(e))}%',ha='center',va='center',fontsize=6.5,color=col)
    ax2.add_patch(plt.Rectangle((1.52,2.52),0.96,0.96,fill=False,ec='#bb0000',lw=2.2))
    plt.colorbar(im,ax=ax2,fraction=0.046,pad=0.03,shrink=0.88).set_label('error (%)')
    ax2.set_xlabel(r'$\sigma_1$'); ax2.set_ylabel(r'$\sigma_2$')
    ax2.set_xticks(range(N)); ax2.set_yticks(range(N))
    ax2.text(-0.13,1.02,'(b)',transform=ax2.transAxes,fontsize=13,fontweight='bold')
    plt.savefig('fig1_alphas_uniqueness.png',dpi=150,bbox_inches='tight',facecolor='white'); plt.close()
    print(f"  Fig1 saved (min err {EM.min():.4f}%)")

def make_fig2():
    N=9; sf=np.linspace(0,8,55); F1,F2=np.meshgrid(sf,sf)
    LTS=np.vectorize(lambda s1,s2:np.log(T_alg(s1,s2)))(F1,F2)
    max_res=max(abs(T_alg(s1,s2)-T_trig(s1,s2)) for s1 in range(N) for s2 in range(N))
    assert max_res<1e-13
    Ta,Tt,res=[],[],[]
    for s1 in range(N):
        for s2 in range(N):
            ta=T_alg(s1,s2); tt=T_trig(s1,s2); Ta.append(ta); Tt.append(tt); res.append(ta-tt)
    Ta,Tt,res=np.array(Ta),np.array(Tt),np.array(res)
    fig=plt.figure(figsize=(14,7.5),facecolor='white')
    ax3=fig.add_axes([0.02,0.06,0.47,0.90],projection='3d')
    ax2=fig.add_axes([0.56,0.06,0.42,0.90])
    ax3.set_facecolor('white')
    for p in [ax3.xaxis.pane,ax3.yaxis.pane,ax3.zaxis.pane]: p.fill=False; p.set_edgecolor('#e0e0e0')
    rb=LinearSegmentedColormap.from_list('rb',['#1a3a6e','#e8e8e8','#8b1a1a'])
    cs=rb((LTS-LTS.min())/(LTS.max()-LTS.min())); cs[...,3]=0.85
    ax3.plot_surface(F1,F2,LTS,facecolors=cs,linewidth=0,antialiased=True,shade=False)
    d=np.linspace(0,8,100); ax3.plot(d,d,np.zeros(100),color='#111111',lw=1.5)
    for s1,s2,col in [(1,4,'#990000'),(4,7,'#990000'),(1,7,'#003388')]:
        ax3.scatter(s1,s2,np.log(T_alg(s1,s2)),s=55,c=col,edgecolors='white',linewidths=0.8,zorder=12)
    ax3.text(2.0,6.8,np.log(T_alg(1,4))+0.06,r'$T(1,4)\cdot T(4,7)=T(1,7)$',fontsize=10,color='#555555',style='italic')
    ax3.set_xlabel(r'$\sigma_1$'); ax3.set_ylabel(r'$\sigma_2$'); ax3.set_zlabel(r'$\ln T$',fontsize=11)
    ax3.view_init(elev=24,azim=-52); ax3.set_box_aspect([1,1,0.60])
    ax3.text2D(0.03,0.95,'(a)',transform=ax3.transAxes,fontsize=13,fontweight='bold')
    vn=min(Ta.min(),Tt.min()); vx=max(Ta.max(),Tt.max()); ln=np.linspace(vn*0.97,vx*1.03,200)
    ax2.plot(ln,ln,color='#111111',lw=1.5,label=r'$T_{\rm alg}=T_{\rm trig}$')
    ax2.scatter(Tt,Ta,s=22,c='#444444',alpha=0.7,edgecolors='none')
    ins=ax2.inset_axes([0.58,0.06,0.38,0.34]); ins.set_facecolor('#f8f8f8')
    ins.scatter(Tt,res,s=8,c='#990000',alpha=0.75,edgecolors='none')
    ins.axhline(0,color='#333333',lw=0.8); ins.ticklabel_format(style='sci',axis='y',scilimits=(0,0))
    ins.set_title(r'residuals $\sim 10^{-15}$',fontsize=9.5,color='#990000')
    ax2.set_xlabel(r'$T_{\rm trig}$',fontsize=12); ax2.set_ylabel(r'$T_{\rm alg}$',fontsize=12)
    ax2.legend(loc='upper left'); ax2.grid(True,color='#eeeeee',lw=0.4)
    ax2.text(-0.12,1.01,'(b)',transform=ax2.transAxes,fontsize=13,fontweight='bold')
    plt.savefig('fig2_ER_bridge_identity.png',dpi=150,bbox_inches='tight',facecolor='white'); plt.close()
    print(f"  Fig2 saved (max res {max_res:.2e})")

def make_fig3():
    smax=13; sigmas=np.arange(smax)
    Nm=np.array([int(np.floor(np.pi*phi**s)) for s in sigmas])
    ratios=[Nm[s]/Nm[s-1] for s in range(2,smax)]; rsig=list(range(2,smax))
    def kk_max(N_lev):
        L=np.zeros((N_lev,N_lev))
        for s in range(N_lev):
            L[s,s]=-2/lnphi**2
            if s>0: L[s,s-1]=phi**2/lnphi**2
            if s<N_lev-1: L[s,s+1]=phi**(-2)/lnphi**2
        return abs(np.sort(np.linalg.eigvalsh(L))[0])
    kk_sig=list(range(3,smax)); kk_vals=[kk_max(s) for s in kk_sig]
    assert Nm[0]==3 and Nm[6]==56
    fig,(ax1,ax2)=plt.subplots(1,2,figsize=(15,7),facecolor='white')
    sf=np.linspace(-0.3,smax-0.5,500)
    ax1.plot(sf,np.pi*phi**sf,'--',color='#cc6600',lw=1.5,label=r'$\pi\varphi^\sigma$ (continuous)')
    for s in sigmas:
        sn=s+1 if s<smax-1 else s+0.5
        ax1.plot([s,sn],[Nm[s],Nm[s]],'-',color='#1a4a8a',lw=2.0,zorder=5)
        if s<smax-1: ax1.plot([sn,sn],[Nm[s],Nm[s+1]],'-',color='#1a4a8a',lw=2.0,zorder=5)
    ax1.scatter(sigmas,Nm,s=40,c='#1a4a8a',zorder=6,edgecolors='white',linewidths=0.5)
    for s in sigmas: ax1.text(s+0.15,Nm[s]*1.12,str(Nm[s]),fontsize=8.5,color='#444444')
    ax1.axvline(6,color='#cc0000',lw=0.9,ls='--')
    ax1.text(6.15,5.5,r'$\sigma_\Lambda=6$'+'\n'+r'$N=56$',fontsize=10,color='#cc0000',style='italic')
    ax1.set_yscale('log'); ax1.set_xlabel(r'Tower level $\sigma$',fontsize=14)
    ax1.set_ylabel(r'$N_{\rm modes}(\sigma)$ (log)',fontsize=14)
    ax1.legend(loc='upper left',fontsize=11)
    ax1.text(6.5,8,r'$N_{\rm modes}(\sigma)=\lfloor\pi\varphi^\sigma\rfloor$'+'\nadjacent to Fibonacci'+'\n$\{3,5,8,13,21,34,55,89,\ldots\}$',fontsize=10,color='#555555',bbox=dict(boxstyle='round,pad=0.4',fc='#fffff0',ec='#cccc88',lw=0.8))
    ax1.text(0.03,0.97,'(a)',transform=ax1.transAxes,fontsize=14,fontweight='bold',va='top')
    ax2.plot(rsig,ratios,'o-',color='#1a4a8a',lw=1.5,ms=7,label=r'$N(\sigma)/N(\sigma{-}1)$')
    for s,r in zip(rsig,ratios): ax2.text(s+0.12,r+0.0008,f'{r:.4f}',fontsize=8,color='#444466')
    ax2.axhline(phi,color='#cc6600',lw=1.5,ls='--',label=r'$\varphi=1.618034$')
    ax2.set_xlabel(r'Tower level $\sigma$',fontsize=13)
    ax2.set_ylabel(r'$N(\sigma)/N(\sigma{-}1)$',fontsize=13)
    axk=ax2.twinx()
    axk.plot(kk_sig,kk_vals,'s--',color='#8833aa',lw=1.2,ms=6,label=r'KK $\lambda_{\max}(N)$')
    axk.set_ylabel(r'KK $\lambda_{\max}$',fontsize=12,color='#8833aa')
    axk.tick_params(axis='y',colors='#8833aa')
    l1,lb1=ax2.get_legend_handles_labels(); l2,lb2=axk.get_legend_handles_labels()
    ax2.legend(l1+l2,lb1+lb2,loc='upper left',fontsize=10.5)
    ax2.text(0.5,0.03,r'$\lim N(\sigma)/N(\sigma{-}1)=\varphi$ (Fibonacci ratio)',transform=ax2.transAxes,fontsize=11,ha='center',color='#cc6600',style='italic',bbox=dict(boxstyle='round,pad=0.3',fc='#fff8f0',ec='#cc8844',lw=0.8))
    ax2.text(0.03,0.97,'(b)',transform=ax2.transAxes,fontsize=14,fontweight='bold',va='top')
    fig.suptitle(r'$N_{\rm modes}(\sigma)=\lfloor\pi\varphi^\sigma\rfloor$: Fibonacci-adjacent UV cutoff  |  ratio $\to\varphi$  |  KK spectrum',fontsize=14,fontweight='bold',y=0.99)
    plt.tight_layout(rect=[0,0,1,0.96])
    plt.savefig('fig3_N_modes.png',dpi=150,bbox_inches='tight',facecolor='white'); plt.close()
    print(f"  Fig3 saved (N[0..6]={list(Nm[:7])})")

def make_fig4():
    phi_ = (1+np.sqrt(5))/2; omega_ = np.exp(2j*np.pi/3)
    lam_ = [0.5*omega_**k for k in range(3)]
    alpha1_ = np.array([1,0]); alpha2_ = np.array([omega_.real, omega_.imag])
    a1_plus_a2 = alpha1_ + alpha2_
    all_roots = [alpha1_, alpha2_, a1_plus_a2, -alpha1_, -alpha2_, -a1_plus_a2]
    for r in all_roots:
        assert abs(np.linalg.norm(r) - 1.0) < 1e-10, f"Root {r} has |r|={np.linalg.norm(r)}"
    plt.rcParams.update({'font.family':'serif','font.serif':['DejaVu Serif'],
        'mathtext.fontset':'stix','font.size':16,'axes.linewidth':0.6})
    fig = plt.figure(figsize=(20, 11), facecolor='white')
    ax = fig.add_axes([0.02, 0.06, 0.96, 0.84])
    ax.set_facecolor('white'); ax.set_aspect('equal')
    ax.set_xlim(-8.5, 8.5); ax.set_ylim(-4.5, 4.5)
    ax.set_xticks([]); ax.set_yticks([])
    for sp in ax.spines.values(): sp.set_visible(False)
    cx_e = -4.5
    for a in range(-6, 7):
        for b in range(-6, 7):
            z = a + b*omega_
            if abs(z) < 3.8:
                ax.plot(z.real+cx_e, z.imag, 'o', color='#8899aa', ms=5.5, alpha=0.5, zorder=2)
    root_data = [
        (alpha1_,      '#cc3300', 3.0),(-alpha1_,     '#cc3300', 3.0),
        (alpha2_,      '#0044cc', 3.0),(-alpha2_,     '#0044cc', 3.0),
        (a1_plus_a2,   '#009933', 2.5),(-a1_plus_a2,  '#009933', 2.5),]
    for rv, col, lw in root_data:
        ax.annotate('', xy=(rv[0]*1.5+cx_e, rv[1]*1.5), xytext=(cx_e, 0),
                    arrowprops=dict(arrowstyle='->', color=col, lw=lw, shrinkA=0, shrinkB=1))
    ax.text(alpha1_[0]*1.6+cx_e+0.05, 0.15, r'$\alpha_1$', fontsize=15, color='#cc3300', fontweight='bold')
    ax.text(-alpha1_[0]*1.6+cx_e-0.5, 0.15, r'$-\alpha_1$', fontsize=14, color='#cc3300')
    ax.text(alpha2_[0]*1.6+cx_e-0.1, alpha2_[1]*1.6+0.1, r'$\alpha_2$', fontsize=15, color='#0044cc', fontweight='bold')
    ax.text(-alpha2_[0]*1.6+cx_e+0.05, -alpha2_[1]*1.6-0.25, r'$-\alpha_2$', fontsize=14, color='#0044cc')
    ax.text(a1_plus_a2[0]*1.6+cx_e+0.1, a1_plus_a2[1]*1.6+0.05, r'$\alpha_1{+}\alpha_2$', fontsize=13, color='#009933')
    ax.text(-a1_plus_a2[0]*1.6+cx_e-0.8, -a1_plus_a2[1]*1.6-0.15, r'$-(\alpha_1{+}\alpha_2)$', fontsize=13, color='#009933')
    ax.add_patch(plt.Circle((cx_e, 0), 0.5, fill=False, ec='#cc6600', lw=3.0, ls='--', zorder=6))
    for k in range(3):
        l1, l2 = lam_[k], lam_[(k+1)%3]
        ax.plot([l1.real+cx_e, l2.real+cx_e], [l1.imag, l2.imag], '-', color='#cc6600', lw=2.5, zorder=7)
    pcf_colors = ['#cc6600', '#0044cc', '#9900cc']
    for k in range(3):
        ax.plot(lam_[k].real+cx_e, lam_[k].imag, 's', color=pcf_colors[k], ms=11, zorder=8, mec='white', mew=0.8)
    ax.text(cx_e+0.6, 0.08, r'$|\hat\Omega|{=}\frac{1}{2}$', fontsize=15, color='#cc6600', fontweight='bold')
    ax.text(cx_e, -4.0, r'Eisenstein $\mathbb{Z}[\omega]$  (algebra / boundary)'+'\n'+r'$120°$,  $S_3$ symmetry'+'\n'+r'$A_2$ root lattice $=$ SU(3)',
            fontsize=14, ha='center', color='#334455', bbox=dict(boxstyle='round,pad=0.5', fc='#f0f8ff', ec='#8899aa', lw=1.0))
    ax.annotate('', xy=(2.8, 0), xytext=(-2.0, 0), arrowprops=dict(arrowstyle='->', color='#cc6600', lw=4.0, shrinkA=0, shrinkB=0))
    ax.annotate('', xy=(-2.0, 0), xytext=(2.8, 0), arrowprops=dict(arrowstyle='->', color='#cc6600', lw=4.0, shrinkA=0, shrinkB=0))
    ax.text(0.4, 0.7, r'$\varphi$-mediation', fontsize=20, ha='center', color='#cc6600', fontweight='bold')
    ax.text(0.4, -0.6, r'$S_3 \to \mathbb{Z}_4$', fontsize=18, ha='center', color='#cc6600', fontweight='bold')
    ax.text(0.4, -1.4, r'bulk $\leftrightarrow$ boundary:  $V^\dagger V{=}I$', fontsize=14, ha='center', color='#cc6600')
    ax.text(0.4, -2.1, r'$\tau_{\rm PCF}=i$ fixed', fontsize=14, ha='center', color='#cc6600', style='italic')
    cx_g = 4.5
    for a in range(-4, 5):
        for b in range(-4, 5):
            z = a + b*1j
            if abs(z) < 3.8:
                ax.plot(z.real+cx_g, z.imag, 'o', color='#8899aa', ms=5.5, alpha=0.5, zorder=2)
    ax.add_patch(plt.Rectangle((cx_g-0.5, -0.5), 1.0, 1.0, fill=False, ec='#3366aa', lw=2.0, zorder=4))
    ax.add_patch(plt.Circle((cx_g, 0), 0.5, fill=False, ec='#cc6600', lw=3.0, ls='--', zorder=6))
    for k in range(3):
        l1, l2 = lam_[k], lam_[(k+1)%3]
        ax.plot([l1.real+cx_g, l2.real+cx_g], [l1.imag, l2.imag], '-', color='#cc6600', lw=2.5, zorder=7)
    for k in range(3):
        ax.plot(lam_[k].real+cx_g, lam_[k].imag, 's', color=pcf_colors[k], ms=11, zorder=8, mec='white', mew=0.8)
    ax.text(cx_g+0.6, 0.08, r'$|\hat\Omega|{=}\frac{1}{2}$', fontsize=15, color='#cc6600', fontweight='bold')
    ax.plot(cx_g, 1, '*', color='#cc0000', ms=20, zorder=10)
    ax.text(cx_g+0.25, 1.15, r'$\tau_{\rm PCF}=i$', fontsize=15, color='#cc0000', fontweight='bold')
    ax.text(cx_g+0.25, 0.7, r'$-1/i=i$ (fixed)', fontsize=12, color='#cc0000')
    ax.annotate('', xy=(cx_g+1.3, 0), xytext=(cx_g, 0), arrowprops=dict(arrowstyle='->', color='#3366aa', lw=2.2, shrinkA=0, shrinkB=1))
    ax.text(cx_g+1.4, -0.18, r'$1$', fontsize=14, color='#3366aa', fontweight='bold')
    ax.annotate('', xy=(cx_g, 1.3), xytext=(cx_g, 0), arrowprops=dict(arrowstyle='->', color='#3366aa', lw=2.2, shrinkA=0, shrinkB=1))
    ax.text(cx_g+0.12, 1.4, r'$i$', fontsize=14, color='#3366aa', fontweight='bold')
    ax.add_patch(mpatches.Arc((cx_g, 0), 0.45, 0.45, angle=0, theta1=0, theta2=90, color='#555555', lw=1.2))
    ax.text(cx_g+0.18, 0.22, r'$90°$', fontsize=12, color='#555555')
    ax.text(cx_g, -4.0, r'Gauss $\mathbb{Z}[i]$  (isometry / bulk)'+'\n'+r'$90°$,  $\mathbb{Z}_4$ symmetry'+'\n'+r'$\tau_{\rm PCF}=i$,  $\ell=1$',
            fontsize=14, ha='center', color='#334455', bbox=dict(boxstyle='round,pad=0.5', fc='#f0f8ff', ec='#8899aa', lw=1.0))
    fig.suptitle(r'Isometry $\leftrightarrow$ algebra (bulk--boundary) via $\varphi$:  '
                 r'$\mathbb{Z}[\omega]$ (algebra: $120°$, $S_3$) $\leftrightarrow$ $\mathbb{Z}[i]$ (isometry: $\tau{=}i$)'
                 r'  ---  $V: H_{\rm bulk}\to H_{\partial}$,  $V^\dagger V{=}I$,  $|\hat\Omega|{=}1/2$ preserved',
                 fontsize=16, fontweight='bold', y=0.97)
    plt.savefig('fig4_top_down.png', dpi=200, bbox_inches='tight', facecolor='white')
    plt.close()
    print("  Fig4 saved")

def make_fig5():
    fig=plt.figure(figsize=(18,7.5),facecolor='white')
    ax1=fig.add_subplot(131,projection='3d'); ax1.set_facecolor('white')
    for p in [ax1.xaxis.pane,ax1.yaxis.pane,ax1.zaxis.pane]: p.fill=False; p.set_edgecolor('#e8e8e8')
    for s in range(8):
        y=s*lnphi; r=min(0.15+0.05*phi**s,2.0); th=np.linspace(0,2*np.pi,60)
        ax1.plot(r*np.cos(th),np.full(60,y),r*np.sin(th),color='#2266aa',lw=0.8,alpha=0.7)
    s_a=np.linspace(0,7*lnphi,80); th=np.linspace(0,2*np.pi,40)
    S,T=np.meshgrid(s_a,th); R=np.minimum(0.15+0.05*np.exp(S),2.0)
    ax1.plot_surface(R*np.cos(T),S,R*np.sin(T),color='#4488cc',alpha=0.15,linewidth=0)
    names=['Superpoint','Superstring','Het str','M2','M5','NS5','10-brane']
    for s,nm in enumerate(names):
        ax1.text(1.8,s*lnphi,0,f'sigma={s}: {nm}',fontsize=7,color='#335577')
    thb=np.linspace(0,2*np.pi,40)
    ax1.plot(0.15*np.cos(thb),np.zeros(40),0.15*np.sin(thb),color='#cc0000',lw=2.0,zorder=10)
    ax1.text(0,-0.3,-0.5,r'CFT$_4$',fontsize=9,color='#cc0000')
    ax1.set_ylabel(r'$y=\sigma\ln\varphi$',fontsize=10)
    ax1.set_title(r'AdS$_5$: $z=\varphi^\sigma$, $\ell=1$, $G_N=1/2$',fontsize=10)
    ax1.view_init(elev=15,azim=-70)
    ax1.text2D(0.03,0.95,'(a)',transform=ax1.transAxes,fontsize=14,fontweight='bold')
    ax2=fig.add_subplot(132); ax2.set_facecolor('white'); ax2.set_aspect('equal')
    for s in range(7):
        r=phi**s*0.12; ax2.add_patch(plt.Circle((0,0),r,fill=False,ec='#cc6600',lw=1.0,ls='--',alpha=0.5+0.07*s))
        ax2.text(r+0.02,0.05,rf'$\varphi^{s}$',fontsize=7,color='#cc6600')
    for a in range(-12,13):
        for b in range(-12,13):
            z=(a+b*omega)*0.12
            if abs(z)<2.5: ax2.plot(z.real,z.imag,'.',color='#2266aa',ms=max(1,4-abs(z)),alpha=0.5)
    ax2.set_xlim(-2.5,2.5); ax2.set_ylim(-2.5,2.5); ax2.set_xticks([]); ax2.set_yticks([])
    ax2.set_title(r'$\Lambda_\sigma=\varphi^\sigma\Lambda_{\rm PCF}$ in $\mathbb{C}$',fontsize=10)
    ax2.text(0.03,0.97,'(b)',transform=ax2.transAxes,fontsize=14,fontweight='bold',va='top')
    ax3=fig.add_subplot(133,projection='3d'); ax3.set_facecolor('white')
    for p in [ax3.xaxis.pane,ax3.yaxis.pane,ax3.zaxis.pane]: p.fill=False; p.set_edgecolor('#e8e8e8')
    verts=list(itertools.product([0,1],repeat=5))
    def proj5(v): return (v[0]+0.3*v[3]-0.15*v[4],v[1]+0.3*v[4]-0.15*v[3],v[2]+0.2*v[3]+0.2*v[4])
    pts=[proj5(v) for v in verts]; hw=[sum(v) for v in verts]
    cols={0:'#114477',1:'#2277aa',2:'#44aa88',3:'#88cc44',4:'#ccaa22',5:'#cc4422'}
    bns={0:'Superpoint',1:'Superstring',2:'Het str',3:'M2',4:'M5',5:'NS5'}
    for i,v1 in enumerate(verts):
        for j,v2 in enumerate(verts):
            if j>i and sum(abs(a-b) for a,b in zip(v1,v2))==1:
                ax3.plot([pts[i][0],pts[j][0]],[pts[i][1],pts[j][1]],[pts[i][2],pts[j][2]],color='#aabbcc',lw=0.4,alpha=0.5)
    for i,(pt,h) in enumerate(zip(pts,hw)):
        ax3.scatter(*pt,s=20+h*15,c=cols[h],edgecolors='white',linewidths=0.3,zorder=8,alpha=0.85)
    for h in range(6): ax3.scatter([],[],[],s=40,c=cols[h],label=rf'$\sigma={h}$: {bns[h]}')
    ax3.legend(loc='upper right',fontsize=7.5)
    ax3.set_title(r'$H_5=\{0,1\}^5$: Hamming $=$ H-S level',fontsize=10)
    ax3.view_init(elev=20,azim=-60)
    ax3.text2D(0.03,0.95,'(c)',transform=ax3.transAxes,fontsize=14,fontweight='bold')
    ax3.text2D(0.5,0.02,r'Hopf: $S^1\to S^5\to\mathbb{C}P^2$; $\chi(\mathbb{C}P^2)=3=n$',transform=ax3.transAxes,fontsize=8.5,ha='center',color='#335577',bbox=dict(boxstyle='round,pad=0.3',fc='#f0f4ff',ec='#8899bb',lw=0.7))
    fig.suptitle(r'AdS$_5$ funnel $\longleftrightarrow$ $\Lambda_\sigma$ tower $\longleftrightarrow$ $H_5$ hypercube: $\varphi^\sigma$ connects all three',fontsize=13,fontweight='bold',y=0.99)
    plt.tight_layout(rect=[0,0,1,0.95])
    plt.savefig('fig5_three_panel.png',dpi=150,bbox_inches='tight',facecolor='white'); plt.close()
    print(f"  Fig5 saved")

def make_fig6():
    fig=plt.figure(figsize=(16,8),facecolor='white')
    ax1=fig.add_subplot(121,projection='3d'); ax1.set_facecolor('white')
    for p in [ax1.xaxis.pane,ax1.yaxis.pane,ax1.zaxis.pane]: p.fill=False; p.set_edgecolor('#e0e0e0')
    th=np.linspace(0,2*np.pi,60); zc=np.linspace(-8,8,40); Th,Zc=np.meshgrid(th,zc)
    ax1.plot_surface(3*np.cos(Th),3*np.sin(Th),Zc,color='#aabbdd',alpha=0.08,linewidth=0)
    pcf={'P':(0,-0.5,'#cc4400'),'C':(2*np.pi/3,5.0,'#0044cc'),'F':(4*np.pi/3,-6.5,'#9900cc')}
    pts3={}
    for nm,(a,z,c) in pcf.items():
        x,y=3*np.cos(a),3*np.sin(a); pts3[nm]=(x,y,z)
        ax1.scatter(x,y,z,s=100,c=c,zorder=10,edgecolors='white',linewidths=1.0)
        ax1.text(x*1.15,y*1.15,z+0.3,nm,fontsize=14,color=c,fontweight='bold')
    for n1,n2 in [('P','C'),('C','F'),('F','P')]:
        p1,p2=pts3[n1],pts3[n2]
        ax1.plot([p1[0],p2[0]],[p1[1],p2[1]],[p1[2],p2[2]],color='#222266',lw=1.8,zorder=7)
    ax1.text2D(0.02,0.05,r'$|P|\cdot|C|\cdot|F|=\frac{1}{\sqrt{3}}\cdot 1\cdot\frac{\sqrt{3}}{2}=\frac{1}{2}$',transform=ax1.transAxes,fontsize=9,color='#334455',bbox=dict(boxstyle='round,pad=0.3',fc='#f8f8ff',ec='#8888bb',lw=0.7))
    ax1.set_xlabel('x'); ax1.set_ylabel('y'); ax1.set_zlabel(r'$z=\varphi y$')
    ax1.view_init(elev=18,azim=-65)
    ax1.set_title(r'Cylinder $C_0$ with P,C,F at $120°$',fontsize=11)
    ax1.text2D(0.03,0.95,'(a)',transform=ax1.transAxes,fontsize=14,fontweight='bold')
    fig.text(0.49,0.5,r'$\longleftrightarrow$'+'\n'+r'$S_3\to\mathbb{Z}_4$',fontsize=14,ha='center',va='center',color='#cc0000',fontweight='bold')
    ax2=fig.add_subplot(122,projection='3d'); ax2.set_facecolor('white')
    for p in [ax2.xaxis.pane,ax2.yaxis.pane,ax2.zaxis.pane]: p.fill=False; p.set_edgecolor('#e0e0e0')
    r1,r2=0.5,np.sqrt(3)/2; assert abs(r1**2+r2**2-1)<1e-10
    u=np.linspace(0,2*np.pi,80); v=np.linspace(0,2*np.pi,40); U,V=np.meshgrid(u,v)
    X=(r2+r1*np.cos(V))*np.cos(U); Y=(r2+r1*np.cos(V))*np.sin(U); Z=r1*np.sin(V)
    ax2.plot_surface(X,Y,Z,color='#4488bb',alpha=0.25,linewidth=0,antialiased=True)
    R_a=r2+r1+0.05; ths=np.linspace(0,2*np.pi,60); zs=np.linspace(-r1-0.1,r1+0.1,20)
    Ts,Zs=np.meshgrid(ths,zs)
    ax2.plot_surface(R_a*np.cos(Ts),R_a*np.sin(Ts),Zs,color='#aabbcc',alpha=0.06,linewidth=0)
    zh=np.linspace(-0.8,0.8,50)
    ax2.plot(np.zeros(50),np.zeros(50),zh,color='#cc00cc',lw=2.5,zorder=10,label=r'$S^1\cong U(1)$: Hopf')
    ax2.scatter(r2+r1,0,0,s=60,c='#0044cc',zorder=12,edgecolors='white')
    ax2.text(r2+r1+0.1,0.1,0.1,r'$\lambda_1$',fontsize=12,color='#0044cc')
    ax2.scatter(0,r2,r1,s=60,c='#9900cc',zorder=12,edgecolors='white')
    ax2.text(0.1,r2+0.1,r1+0.1,r'$\lambda_2$',fontsize=12,color='#9900cc')
    ax2.legend(loc='lower left',fontsize=10)
    ax2.set_xlabel(r'Re($z_1$)'); ax2.set_ylabel(r'Im($z_1$)')
    ax2.set_title(r'Clifford torus $T^2_{\rm PCF}\hookrightarrow S^3\cong$ SU(2)',fontsize=11)
    ax2.text2D(0.97,0.05,r'$|z_1|^2+|z_2|^2=\frac{1}{4}+\frac{3}{4}=1$ ($S^3$)',transform=ax2.transAxes,fontsize=9.5,ha='right',color='#555555')
    ax2.view_init(elev=22,azim=-55)
    ax2.text2D(0.03,0.95,'(b)',transform=ax2.transAxes,fontsize=14,fontweight='bold')
    fig.suptitle(r'From $\varphi^2=\varphi+1$: $C_0$ with P,C,F $\to$ $T^2_{\rm PCF}\hookrightarrow S^3$ $\to$ SU(3)$\times$SU(2)$\times$U(1)',fontsize=13,fontweight='bold',y=0.99)
    plt.tight_layout(rect=[0,0,1,0.95])
    plt.savefig('fig6_cylinder_torus.png',dpi=150,bbox_inches='tight',facecolor='white'); plt.close()
    print(f"  Fig6 saved")

if __name__=='__main__':
    print("Generating 6 figures...")
    make_fig1(); make_fig2(); make_fig3(); make_fig4(); make_fig5(); make_fig6()
    print("Done.")
