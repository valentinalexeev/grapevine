import json, math, os, numpy as np, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import font_manager as fm
for f in fm.findSystemFonts():
    if "Liberation" in f: fm.fontManager.addfont(f)
plt.rcParams.update({"font.family": "Liberation Serif", "font.size": 8, "axes.titlesize": 8,
    "axes.labelsize": 8, "legend.fontsize": 7, "xtick.labelsize": 7, "ytick.labelsize": 7,
    "axes.spines.top": False, "axes.spines.right": False, "axes.linewidth": 0.6,
    "pdf.fonttype": 42})
BLUE = "#2563a8"; GREY = "#9a9a9a"
W = 3.35

# Рис. 1
rows = json.load(open(os.path.join(os.path.dirname(__file__), "data", "sim_rows.json")))
labels = {"0%": "Z ничего не знает", "50%": "Z угадывает 50%", "80%": "Z угадывает 80%"}
fig, ax = plt.subplots(figsize=(W, 2.3))
for k, pr in enumerate(["0%", "50%", "80%"]):
    xs = [r["speed"] for r in rows if r["prior"] == pr]; ys = [r["p"] for r in rows if r["prior"] == pr]
    cross = None
    for i in range(1, len(xs)):
        if ys[i-1] >= 0.5 > ys[i]:
            t = (ys[i-1]-0.5)/(ys[i-1]-ys[i]); cross = math.exp(math.log(xs[i-1]) + t*(math.log(xs[i])-math.log(xs[i-1]))); break
    a = 0.35 + 0.65*k/2
    ax.plot(xs, ys, color=BLUE, alpha=a, lw=1.4, label=f"{labels[pr]}: порог {round(cross)}")
    ax.plot([cross], [0.5], "o", color=BLUE, alpha=a, ms=4)
ax.axvline(50, color=GREY, ls="--", lw=0.7); ax.axhline(0.5, color=GREY, ls=":", lw=0.7)
ax.text(46, 0.62, "скорость одного\nзвена сети", ha="right", fontsize=6.5, color="#555")
ax.set_xscale("log"); ax.set_xticks([5, 10, 20, 50, 100, 200, 400]); ax.set_xticklabels(["5", "10", "20", "50", "100", "200", "400"])
ax.set_yticks([0, .25, .5, .75, 1]); ax.set_yticklabels(["0", "25%", "50%", "75%", "100%"])
ax.set_xlabel("Скорость прямого канала A→Z, символов/ед. времени")
ax.set_ylabel("P(сеть быстрее)")
ax.legend(loc="lower left", frameon=False, bbox_to_anchor=(0.0, 0.12))
fig.tight_layout(pad=0.3); fig.savefig(os.path.join(os.path.dirname(__file__), "figures", "fig_sim.pdf"))

# Рис. 2
fig, ax = plt.subplots(figsize=(W, 2.2))
days = np.arange(0, 31); q = 0.01
for i, k in enumerate([5, 20, 50]):
    risk = 1 - (1-q)**(k*days); fd = next(d for d in days if risk[d] >= 0.5)
    a = 0.35 + 0.65*i/2
    ax.plot(days, risk, color=BLUE, alpha=a, lw=1.4, label=f"{k} кругов: 50% на {fd}-й день")
    ax.plot([fd], [risk[fd]], "o", color=BLUE, alpha=a, ms=4)
ax.axhline(0.5, color=GREY, ls="--", lw=0.7)
ax.set_xlim(0, 30); ax.set_ylim(0, 1.02)
ax.set_yticks([0, .25, .5, .75, 1]); ax.set_yticklabels(["0", "25%", "50%", "75%", "100%"])
ax.set_xlabel("Дни до официального объявления"); ax.set_ylabel("Риск утечки")
ax.legend(loc="lower right", frameon=False)
fig.tight_layout(pad=0.3); fig.savefig(os.path.join(os.path.dirname(__file__), "figures", "fig_leak.pdf"))

# Рис. 3
fig, ax = plt.subplots(figsize=(W, 2.2))
bmin, bmax, bref = 0.001, 0.5, 0.01
up = lambda n: bmax if n == 1 else min(bmax, 1/(2*n*(n-1)))
lo = lambda n: max(bmin, 1/(2*(n+1)*n))
for n in range(1, 26):
    if lo(n) >= up(n): continue
    isref = lo(n) <= bref < up(n)
    ax.plot([lo(n), up(n)], [math.log2(n)]*2, color=BLUE if isref else GREY, lw=2.4 if isref else 1.4)
    if lo(n) > bmin: ax.plot([lo(n)]*2, [math.log2(n), math.log2(n+1)], color=GREY, lw=0.6)
ax.axvline(bref, color=GREY, ls="--", lw=0.7)
ax.plot([bref], [math.log2(7)], "o", color=BLUE, ms=4)
ax.annotate("b = 1%: N = 7, 2,8 бита", (bref, math.log2(7)), xytext=(0.013, 3.5), fontsize=7)
ax.text(0.2, 0.15, "b ≥ 1/4: 0 бит", ha="right", fontsize=6.5, color="#555")
ax.set_xscale("log"); ax.set_xticks([0.001, 0.003, 0.01, 0.03, 0.1, 0.25, 0.5])
ax.set_xticklabels(["0,001", "0,003", "0,01", "0,03", "0,1", "0,25", "0,5"])
ax.set_ylim(0, 5); ax.set_xlabel("Конфликт интересов b"); ax.set_ylabel("бит за раунд, log₂N(b)")
fig.tight_layout(pad=0.3); fig.savefig(os.path.join(os.path.dirname(__file__), "figures", "fig_cheap.pdf"))
print("ok")
