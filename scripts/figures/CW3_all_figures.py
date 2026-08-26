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
from fractions import Fraction as Fr
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
    # Panel (a): spectral angle surface sin a(s1) cos a(s2).  Panel (b): integer
    # uniqueness of eq:interval-levels.  No fitted constants: the pair (2,3) is
    # DERIVED from arity n=3 (sigma_G=n-1, sigma_EM=n).
    n_ar = 3
    muSq = Fr(1, 4)
    PSq = Fr(1, 3)

    def pred(s1, s2):
        return np.sin(alpha(s1)) * np.cos(alpha(s2))

    def closed(s1, s2):
        return eps0 * phi ** s1 / np.sqrt(
            (1 + eps0 ** 2 * phi ** (2 * s1)) * (1 + eps0 ** 2 * phi ** (2 * s2)))

    N = 9
    sg = np.arange(N)
    S1, S2 = np.meshgrid(sg, sg)
    PM = pred(S1, S2)
    sf = np.linspace(0, 8, 60)
    F1, F2 = np.meshgrid(sf, sf)
    PS = pred(F1, F2)

    # Assertion 1: surface matches closed form
    assert max(abs(pred(a, b) - closed(a, b)) for a in range(N) for b in range(N)) < 1e-14
    # Assertion 2: tan a(s+1)/tan a(s) = phi exactly
    assert max(abs(np.tan(alpha(s + 1)) / np.tan(alpha(s)) - phi) for s in range(N)) < 1e-13

    # Assertion 3: unique integer triple satisfying four constraints is (2,3,6)
    def sols(n, hi=15):
        return [(g, e, l) for g in range(hi) for e in range(g + 1, hi + 1)
                for l in range(e + 1, hi + 2)
                if l == 2 * n and l - g == n + 1
                and Fr(e - g, l - g) == muSq and Fr(e - g, l - e) == PSq]

    assert sols(n_ar) == [(n_ar - 1, n_ar, 2 * n_ar)] == [(2, 3, 6)]
    assert sols(2) == [] and sols(4) == []   # discriminates by arity

    GRID = [(g, e, l) for g in range(9) for e in range(g + 1, 10) for l in range(e + 1, 11)]

    fig = plt.figure(figsize=(12, 16), facecolor='white')
    ax3 = fig.add_axes([0.05, 0.52, 0.90, 0.46], projection='3d')
    ax2 = fig.add_axes([0.08, 0.04, 0.88, 0.44])
    ax3.set_facecolor('white')
    for p in [ax3.xaxis.pane, ax3.yaxis.pane, ax3.zaxis.pane]:
        p.fill = False
        p.set_edgecolor('#e0e0e0')
    ax3.set_box_aspect([1, 1, 0.75])

    grey = LinearSegmentedColormap.from_list('g', ['#e8e8e8', '#4a4a4a'])
    cs = grey((PS - PS.min()) / (PS.max() - PS.min()))
    cs[..., 3] = 0.82
    ax3.plot_surface(F1, F2, PS, facecolors=cs, linewidth=0, antialiased=True, shade=True)
    ax3.scatter(2, 3, pred(2, 3), s=120, c='#bb0000', edgecolors='white', linewidths=1.5, zorder=12)
    ax3.text2D(0.62, 0.72, r'$(2,3)$: $0.1181$', transform=ax3.transAxes,
              fontsize=15, color='#bb0000', fontweight='bold',
              bbox=dict(boxstyle='round,pad=0.3', fc='white', ec='#bb0000', lw=1, alpha=0.9))
    ax3.set_xlabel(r'$\sigma_1$', fontsize=14)
    ax3.set_ylabel(r'$\sigma_2$', fontsize=14)
    ax3.set_xticklabels([]); ax3.set_yticklabels([])
    ax3.set_zlabel(r'$\sin\alpha(\sigma_1)\cos\alpha(\sigma_2)$', fontsize=13)
    ax3.view_init(elev=26, azim=-52)
    ax3.set_box_aspect([1, 1, 0.62])
    ax3.text2D(0.03, 0.95, '(a)', transform=ax3.transAxes, fontsize=13, fontweight='bold')

    # Panel (b): how many of four constraints each integer triple satisfies.
    def score(g, e, l):
        return (int(l == 2 * n_ar) + int(l - g == n_ar + 1)
                + int(Fr(e - g, l - g) == muSq) + int(Fr(e - g, l - e) == PSq))

    rows = sorted({(g, e) for g, e, l in GRID})
    ls = sorted({l for _, _, l in GRID})
    Mx = np.zeros((len(rows), len(ls)))
    for i, (g, e) in enumerate(rows):
        for j, l in enumerate(ls):
            Mx[i, j] = score(g, e, l) if l > e else np.nan

    # Trim: keep only rows/cols with at least one non-zero, non-NaN value
    row_mask = np.array([np.nanmax(Mx[i, :]) > 0 for i in range(len(rows))])
    col_mask = np.array([np.nanmax(Mx[:, j]) > 0 for j in range(len(ls))])
    rows_f = [r for r, m in zip(rows, row_mask) if m]
    ls_f = [l for l, m in zip(ls, col_mask) if m]
    Mx_f = Mx[np.ix_(row_mask, col_mask)]

    cmap = LinearSegmentedColormap.from_list(
        's', ['#f4f4f4', '#d8e6d8', '#a8ccA8', '#5aa05a', '#145214'])
    im = ax2.imshow(Mx_f, cmap=cmap, aspect='auto', vmin=0, vmax=4, origin='lower')
    for i, (g, e) in enumerate(rows_f):
        for j, l in enumerate(ls_f):
            if l <= e:
                continue
            v = int(Mx_f[i, j])
            ax2.text(j, i, str(v), ha='center', va='center', fontsize=9,
                      color='white' if v >= 3 else '#333333',
                      fontweight='bold' if v == 4 else 'normal')

    i0 = rows_f.index((2, 3))
    j0 = ls_f.index(6)
    ax2.add_patch(plt.Rectangle((j0 - 0.5, i0 - 0.5), 1, 1, fill=False, ec='#bb0000', lw=2.4))
    ax2.set_xticks(range(len(ls_f)))
    ax2.set_xticklabels(ls_f, fontsize=10)
    ax2.set_yticks(range(len(rows_f)))
    ax2.set_yticklabels([f'({g},{e})' for g, e in rows_f], fontsize=9)
    ax2.set_xlabel(r'$\sigma_\Lambda$')
    ax2.set_ylabel(r'$(\sigma_G,\sigma_{EM})$')
    plt.colorbar(im, ax=ax2, fraction=0.046, pad=0.03, shrink=0.88,
                 ticks=[0, 1, 2, 3, 4]).set_label('constraints satisfied (of 4)', fontsize=12)
    ax2.text(-0.13, 1.02, '(b)', transform=ax2.transAxes, fontsize=14, fontweight='bold')

    plt.savefig('fig1_alphas_uniqueness.pdf', dpi=150, facecolor='white')
    plt.close()
    print(f"  Fig1 saved (unique triple {sols(n_ar)[0]}, 4/4 constraints)")

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
    fig = plt.figure(figsize=(12, 14), facecolor='white')
    ax3 = fig.add_axes([0.05, 0.52, 0.90, 0.46], projection='3d')
    ax2 = fig.add_axes([0.08, 0.04, 0.88, 0.42])
    ax3.set_facecolor('white')
    for p in [ax3.xaxis.pane,ax3.yaxis.pane,ax3.zaxis.pane]: p.fill=False; p.set_edgecolor('#e0e0e0')
    ax3.set_box_aspect([1, 1, 0.75])
    rb=LinearSegmentedColormap.from_list('rb',['#1a3a6e','#e8e8e8','#8b1a1a'])
    cs=rb((LTS-LTS.min())/(LTS.max()-LTS.min())); cs[...,3]=0.85
    ax3.plot_surface(F1,F2,LTS,facecolors=cs,linewidth=0,antialiased=True,shade=False)
    d=np.linspace(0,8,100); ax3.plot(d,d,np.zeros(100),color='#111111',lw=1.5)
    for s1,s2,col in [(1,4,'#990000'),(4,7,'#990000'),(1,7,'#003388')]:
        ax3.scatter(s1,s2,np.log(T_alg(s1,s2)),s=55,c=col,edgecolors='white',linewidths=0.8,zorder=12)
    ax3.text(2.0,6.8,np.log(T_alg(1,4))+0.06,r'$T(1,4)\cdot T(4,7)=T(1,7)$',fontsize=16,color='#555555',style='italic')
    ax3.set_xlabel(r'$\sigma_1$',fontsize=15); ax3.set_ylabel(r'$\sigma_2$',fontsize=15); ax3.set_zlabel(r'$\ln T$',fontsize=15)
    ax3.set_xticklabels([]); ax3.set_yticklabels([]); ax3.set_zticklabels([])
    ax3.view_init(elev=24,azim=-52); ax3.set_box_aspect([1,1,0.60])
    ax3.text2D(0.03,0.95,'(a)',transform=ax3.transAxes,fontsize=13,fontweight='bold')
    vn=min(Ta.min(),Tt.min()); vx=max(Ta.max(),Tt.max()); ln=np.linspace(vn*0.97,vx*1.03,200)
    ax2.plot(ln,ln,color='#111111',lw=1.5,label=r'$T_{\rm alg}=T_{\rm trig}$')
    ax2.scatter(Tt,Ta,s=22,c='#444444',alpha=0.7,edgecolors='none')
    ins=ax2.inset_axes([0.04,0.58,0.38,0.34]); ins.set_facecolor('#f8f8f8')
    ins.scatter(Tt,res,s=8,c='#990000',alpha=0.75,edgecolors='none')
    ins.axhline(0,color='#333333',lw=0.8); ins.ticklabel_format(style='sci',axis='y',scilimits=(0,0))
    ins.set_title(r'residuals $\sim 10^{-15}$',fontsize=11,color='#990000')
    ax2.set_xlabel(r'$T_{\rm trig}$',fontsize=16); ax2.set_ylabel(r'$T_{\rm alg}$',fontsize=16)
    ax2.legend(loc='lower right',fontsize=12); ax2.grid(True,color='#eeeeee',lw=0.4)
    ax2.text(-0.12,1.01,'(b)',transform=ax2.transAxes,fontsize=13,fontweight='bold')
    plt.savefig('fig2_ER_bridge_identity.pdf',dpi=150,bbox_inches='tight',facecolor='white'); plt.close()
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
    for s in sigmas: ax1.text(s+0.15,Nm[s]*1.15,str(Nm[s]),fontsize=12,color='#444444',fontweight='bold')
    ax1.axvline(6,color='#cc0000',lw=0.9,ls='--')
    ax1.text(6.15,5.5,r'$\sigma_\Lambda=6$'+'\n'+r'$N=56$',fontsize=10,color='#cc0000',style='italic')
    ax1.set_yscale('log'); ax1.set_xlabel(r'Tower level $\sigma$',fontsize=15)
    ax1.set_ylabel(r'$N_{\rm modes}(\sigma)$ (log)',fontsize=15)
    ax1.legend(loc='upper left',fontsize=10,framealpha=0.9)
    ax1.text(1.0,400,r'$N_{\rm modes}(\sigma)=\lfloor\pi\varphi^\sigma\rfloor$'+'\nFibonacci-adjacent: $\{3,5,8,13,21,34,55,89,\ldots\}$',fontsize=11,color='#555555',bbox=dict(boxstyle='round,pad=0.4',fc='#fffff0',ec='#cccc88',lw=0.8))
    ax1.text(0.03,0.97,'(a)',transform=ax1.transAxes,fontsize=14,fontweight='bold',va='top')
    ax2.plot(rsig,ratios,'o-',color='#1a4a8a',lw=1.5,ms=7,label=r'$N(\sigma)/N(\sigma{-}1)$')
    for s,r in zip(rsig,ratios): ax2.text(s+0.12,r+0.0008,f'{r:.4f}',fontsize=11,color='#444466')
    ax2.axhline(phi,color='#cc6600',lw=1.5,ls='--',label=r'$\varphi=1.618034$')
    ax2.set_xlabel(r'Tower level $\sigma$',fontsize=14)
    ax2.set_ylabel(r'$N(\sigma)/N(\sigma{-}1)$',fontsize=14)
    axk=ax2.twinx()
    axk.plot(kk_sig,kk_vals,'s--',color='#8833aa',lw=1.2,ms=6,label=r'KK $\lambda_{\max}(N)$')
    axk.set_ylabel(r'KK $\lambda_{\max}$',fontsize=12,color='#8833aa')
    axk.tick_params(axis='y',colors='#8833aa')
    l1,lb1=ax2.get_legend_handles_labels(); l2,lb2=axk.get_legend_handles_labels()
    ax2.legend(l1+l2,lb1+lb2,loc='lower right',fontsize=10,framealpha=0.9)
    ax2.text(0.5,0.12,r'$\lim N(\sigma)/N(\sigma{-}1)=\varphi$ (Fibonacci ratio)',transform=ax2.transAxes,fontsize=12,ha='center',color='#cc6600',style='italic',bbox=dict(boxstyle='round,pad=0.3',fc='#fff8f0',ec='#cc8844',lw=0.8))
    ax2.text(0.03,0.97,'(b)',transform=ax2.transAxes,fontsize=14,fontweight='bold',va='top')
    plt.tight_layout()
    plt.savefig('fig3_N_modes.pdf',dpi=150,bbox_inches='tight',facecolor='white'); plt.close()
    print(f"  Fig3 saved (N[0..6]={list(Nm[:7])})")

def make_fig4():
    phi_ = (1+np.sqrt(5))/2; omega_ = np.exp(2j*np.pi/3)
    lam_ = [0.5*omega_**k for k in range(3)]
    alpha1_ = np.array([1,0]); alpha2_ = np.array([omega_.real, omega_.imag])
    a1_plus_a2 = alpha1_ + alpha2_
    plt.rcParams.update({'font.family':'serif','font.serif':['DejaVu Serif'],
        'mathtext.fontset':'stix','font.size':16,'axes.linewidth':0.6})
    fig = plt.figure(figsize=(20, 12), facecolor='white')
    ax = fig.add_axes([0.0, 0.0, 1.0, 1.0])
    ax.set_facecolor('white'); ax.set_aspect('equal')
    ax.set_xlim(-7, 7); ax.set_ylim(-5, 5)
    ax.set_xticks([]); ax.set_yticks([])
    for sp in ax.spines.values(): sp.set_visible(False)
    ax.set_clip_on(True)
    cx_e = -4
    for a in range(-5, 6):
        for b in range(-5, 6):
            z = a + b*omega_
            if abs(z) < 3.0:
                ax.plot(z.real+cx_e, z.imag, 'o', color='#8899aa', ms=10, alpha=0.5, zorder=2)
    root_data = [
        (alpha1_,      '#cc3300', 4.0),(-alpha1_,     '#cc3300', 4.0),
        (alpha2_,      '#0044cc', 4.0),(-alpha2_,     '#0044cc', 4.0),
        (a1_plus_a2,   '#009933', 3.5),(-a1_plus_a2,  '#009933', 3.5),]
    for rv, col, lw in root_data:
        ax.annotate('', xy=(rv[0]*1.5+cx_e, rv[1]*1.5), xytext=(cx_e, 0),
                    arrowprops=dict(arrowstyle='->', color=col, lw=lw, shrinkA=0, shrinkB=1))
    ax.text(alpha1_[0]*1.6+cx_e+0.05, 0.15, r'$\alpha_1$', fontsize=22, color='#cc3300', fontweight='bold')
    ax.text(-alpha1_[0]*1.6+cx_e-0.5, 0.15, r'$-\alpha_1$', fontsize=20, color='#cc3300')
    ax.text(alpha2_[0]*1.6+cx_e-0.1, alpha2_[1]*1.6+0.1, r'$\alpha_2$', fontsize=22, color='#0044cc', fontweight='bold')
    ax.text(-alpha2_[0]*1.6+cx_e+0.05, -alpha2_[1]*1.6-0.25, r'$-\alpha_2$', fontsize=20, color='#0044cc')
    ax.text(a1_plus_a2[0]*1.6+cx_e+0.1, a1_plus_a2[1]*1.6+0.05, r'$\alpha_1{+}\alpha_2$', fontsize=18, color='#009933')
    ax.text(-a1_plus_a2[0]*1.6+cx_e-0.8, -a1_plus_a2[1]*1.6-0.15, r'$-(\alpha_1{+}\alpha_2)$', fontsize=18, color='#009933')
    ax.add_patch(plt.Circle((cx_e, 0), 0.5, fill=False, ec='#cc6600', lw=4.0, ls='--', zorder=6))
    for k in range(3):
        l1, l2 = lam_[k], lam_[(k+1)%3]
        ax.plot([l1.real+cx_e, l2.real+cx_e], [l1.imag, l2.imag], '-', color='#cc6600', lw=3.5, zorder=7)
    pcf_colors = ['#cc6600', '#0044cc', '#9900cc']
    for k in range(3):
        ax.plot(lam_[k].real+cx_e, lam_[k].imag, 's', color=pcf_colors[k], ms=14, zorder=8, mec='white', mew=1.0)
    ax.text(cx_e+0.6, 0.08, r'$|\hat\Omega|{=}\frac{1}{2}$', fontsize=24, color='#cc6600', fontweight='bold')
    # Eisenstein label moved to caption
    ax.annotate('', xy=(3.5, 0), xytext=(-3.5, 0), arrowprops=dict(arrowstyle='->', color='#cc6600', lw=6.0, shrinkA=0, shrinkB=0))
    ax.annotate('', xy=(-3.5, 0), xytext=(3.5, 0), arrowprops=dict(arrowstyle='->', color='#cc6600', lw=6.0, shrinkA=0, shrinkB=0))
    ax.text(0, 1.2, r'$\varphi$-mediation', fontsize=30, ha='center', color='#cc6600', fontweight='bold')
    ax.text(0, -0.4, r'$S_3 \to \mathbb{Z}_4$', fontsize=28, ha='center', color='#cc6600', fontweight='bold')
    ax.text(0, -1.3, r'bulk $\leftrightarrow$ boundary:  $V^\dagger V{=}I$', fontsize=22, ha='center', color='#cc6600')
    ax.text(0, -2.2, r'$\tau_{\rm PCF}=i$ fixed', fontsize=22, ha='center', color='#cc6600', style='italic')
    cx_g = 4
    for a in range(-5, 6):
        for b in range(-5, 6):
            z = a + b*1j
            if abs(z) < 3.0:
                ax.plot(z.real+cx_g, z.imag, 'o', color='#8899aa', ms=10, alpha=0.5, zorder=2)
    ax.add_patch(plt.Rectangle((cx_g-0.5, -0.5), 1.0, 1.0, fill=False, ec='#3366aa', lw=3.0, zorder=4))
    ax.add_patch(plt.Circle((cx_g, 0), 0.5, fill=False, ec='#cc6600', lw=4.0, ls='--', zorder=6))
    for k in range(3):
        l1, l2 = lam_[k], lam_[(k+1)%3]
        ax.plot([l1.real+cx_g, l2.real+cx_g], [l1.imag, l2.imag], '-', color='#cc6600', lw=3.5, zorder=7)
    for k in range(3):
        ax.plot(lam_[k].real+cx_g, lam_[k].imag, 's', color=pcf_colors[k], ms=14, zorder=8, mec='white', mew=1.0)
    ax.text(cx_g+0.6, 0.08, r'$|\hat\Omega|{=}\frac{1}{2}$', fontsize=24, color='#cc6600', fontweight='bold')
    ax.plot(cx_g, 1, '*', color='#cc0000', ms=25, zorder=10)
    ax.text(cx_g+0.3, 1.2, r'$\tau_{\rm PCF}=i$', fontsize=18, color='#cc0000', fontweight='bold')
    ax.text(cx_g+0.3, 0.7, r'$-1/i=i$ (fixed)', fontsize=15, color='#cc0000')
    ax.annotate('', xy=(cx_g+1.5, 0), xytext=(cx_g, 0), arrowprops=dict(arrowstyle='->', color='#3366aa', lw=3.0, shrinkA=0, shrinkB=1))
    ax.text(cx_g+1.6, -0.18, r'$1$', fontsize=16, color='#3366aa', fontweight='bold')
    ax.annotate('', xy=(cx_g, 1.5), xytext=(cx_g, 0), arrowprops=dict(arrowstyle='->', color='#3366aa', lw=3.0, shrinkA=0, shrinkB=1))
    ax.text(cx_g+0.15, 1.6, r'$i$', fontsize=16, color='#3366aa', fontweight='bold')
    ax.add_patch(mpatches.Arc((cx_g, 0), 0.5, 0.5, angle=0, theta1=0, theta2=90, color='#555555', lw=1.5))
    ax.text(cx_g+0.2, 0.25, r'$90°$', fontsize=14, color='#555555')
    # Gauss label moved to caption
    plt.savefig('fig4_top_down.pdf', dpi=200, facecolor='white', bbox_inches='tight', pad_inches=0)
    plt.close()
    print("  Fig4 saved")

def make_fig5():
    fig=plt.figure(figsize=(10,18),facecolor='white')
    ax1=fig.add_subplot(311,projection='3d'); ax1.set_facecolor('white')
    for p in [ax1.xaxis.pane,ax1.yaxis.pane,ax1.zaxis.pane]: p.fill=False; p.set_edgecolor('#e8e8e8')
    for s in range(8):
        y=s*lnphi; r=min(0.15+0.05*phi**s,2.0); th=np.linspace(0,2*np.pi,60)
        ax1.plot(r*np.cos(th),np.full(60,y),r*np.sin(th),color='#2266aa',lw=0.8,alpha=0.7)
    s_a=np.linspace(0,7*lnphi,80); th=np.linspace(0,2*np.pi,40)
    S,T=np.meshgrid(s_a,th); R=np.minimum(0.15+0.05*np.exp(S),2.0)
    ax1.plot_surface(R*np.cos(T),S,R*np.sin(T),color='#4488cc',alpha=0.15,linewidth=0)
    # brane labels removed — described in caption
    thb=np.linspace(0,2*np.pi,40)
    ax1.plot(0.15*np.cos(thb),np.zeros(40),0.15*np.sin(thb),color='#cc0000',lw=2.0,zorder=10)
    ax1.text(0,-0.3,-0.5,r'CFT$_4$',fontsize=9,color='#cc0000')
    ax1.set_ylabel(r'$y=\sigma\ln\varphi$',fontsize=10)
    ax1.view_init(elev=15,azim=-70)
    ax1.text2D(0.03,0.95,'(a)',transform=ax1.transAxes,fontsize=14,fontweight='bold')
    ax1.set_xticklabels([]); ax1.set_yticklabels([]); ax1.set_zticklabels([])
    ax2=fig.add_subplot(312); ax2.set_facecolor('white'); ax2.set_aspect('equal')
    for s in range(7):
        r=phi**s*0.12; ax2.add_patch(plt.Circle((0,0),r,fill=False,ec='#cc6600',lw=1.5,ls='--',alpha=0.7+0.04*s))
        ax2.text(r*0.7,r*0.7,rf'$\varphi^{{{s}}}$',fontsize=13,color='white',fontweight='bold',
                 bbox=dict(boxstyle='round,pad=0.15',fc='#333333',ec='none',alpha=0.7))
    # Eisenstein dots removed — overlap with circles
    ax2.set_xlim(-2.5,2.5); ax2.set_ylim(-2.5,2.5); ax2.set_xticks([]); ax2.set_yticks([])
    ax2.text(0.03,0.97,'(b)',transform=ax2.transAxes,fontsize=14,fontweight='bold',va='top')
    ax3=fig.add_subplot(313,projection='3d'); ax3.set_facecolor('white')
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
    ax3.view_init(elev=20,azim=-60)
    ax3.set_xticklabels([]); ax3.set_yticklabels([]); ax3.set_zticklabels([])
    ax3.text2D(0.03,0.95,'(c)',transform=ax3.transAxes,fontsize=14,fontweight='bold')
    ax3.text2D(0.5,0.02,r'Hopf: $S^1\to S^5\to\mathbb{C}P^2$; $\chi(\mathbb{C}P^2)=3=n$',transform=ax3.transAxes,fontsize=8.5,ha='center',color='#335577',bbox=dict(boxstyle='round,pad=0.3',fc='#f0f4ff',ec='#8899bb',lw=0.7))
    plt.tight_layout()
    plt.savefig('fig5_three_panel.pdf',dpi=150,bbox_inches='tight',facecolor='white'); plt.close()
    print(f"  Fig5 saved")

def make_fig6():
    fig=plt.figure(figsize=(10,16),facecolor='white')
    ax1=fig.add_subplot(211,projection='3d'); ax1.set_facecolor('white')
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
    ax1.text2D(0.02,0.05,r'$|P|\cdot|C|\cdot|F|=\frac{1}{2}$',transform=ax1.transAxes,fontsize=16,color='#334455',bbox=dict(boxstyle='round,pad=0.3',fc='#f8f8ff',ec='#8888bb',lw=0.8))
    ax1.set_xlabel('x'); ax1.set_ylabel('y'); ax1.set_zlabel(r'$z=\varphi y$')
    ax1.set_xticks([]); ax1.set_yticks([]); ax1.set_zticks([])
    ax1.view_init(elev=18,azim=-65)
    ax1.text2D(0.03,0.95,'(a)',transform=ax1.transAxes,fontsize=14,fontweight='bold')
    fig.text(0.5,0.50,r'$\longleftrightarrow$'+'\n'+r'$S_3\to\mathbb{Z}_4$',fontsize=18,ha='center',va='center',color='#cc0000',fontweight='bold')
    ax2=fig.add_subplot(212,projection='3d'); ax2.set_facecolor('white')
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
    ax2.legend(loc='lower left',fontsize=13)
    ax2.set_xlabel(r'$\mathrm{Re}(z_1)$'); ax2.set_ylabel(r'$\mathrm{Im}(z_1)$')
    ax2.set_xticks([]); ax2.set_yticks([]); ax2.set_zticks([])
    ax2.text2D(0.97,0.05,r'$|z_1|^2+|z_2|^2=1$ ($S^3$)',transform=ax2.transAxes,fontsize=16,ha='right',color='#555555')
    ax2.view_init(elev=22,azim=-55)
    ax2.text2D(0.03,0.95,'(b)',transform=ax2.transAxes,fontsize=14,fontweight='bold')
    plt.tight_layout(pad=1.5)
    plt.savefig('fig6_cylinder_torus.pdf',dpi=150,facecolor='white'); plt.close()
    print(f"  Fig6 saved")

if __name__=='__main__':
    print("Generating 6 figures...")
    make_fig1(); make_fig2(); make_fig3(); make_fig4(); make_fig5(); make_fig6()
    print("Done.")
