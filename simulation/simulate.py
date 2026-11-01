"""Монте-Карло к модели «сарафанного радио».

Сообщение из N символов делится на k частей и кодируется в m фрагментов
(как код Рида–Соломона: любые k верных фрагментов восстанавливают сообщение,
каждый искажённый фрагмент «съедает» ещё два).

Прямой канал A→Z:   T_direct = L_direct + N / c_direct
Сеть: каждый фрагмент идёт своим маршрутом из H пересылок (H случайно),
      на каждой пересылке: задержка ~ Exp(hop_latency) + f / c_hop,
      фрагмент теряется с вероятностью p_drop, искажается с вероятностью p_corrupt.
Z восстанавливает сообщение в первый момент, когда среди r пришедших
фрагментов e искажённых и r >= k_eff + 2e.
k_eff = ceil(k * (1 - prior)) — априорное знание Z уменьшает объём нужной информации
(prior = 0: Z ничего не знает; prior = 0.8: Z угадывает 80% по контексту).

Запуск: python3 simulate.py  → таблица в консоли и sarafan_sim.png
"""

import math
import os
import sys
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

RNG = np.random.default_rng(42)


def simulate(
    N=1000,            # длина сообщения, символов
    k=10,              # на сколько частей делим
    m=30,              # сколько фрагментов отправляем в сеть
    hops_mean=4.0,     # средняя длина маршрута в пересылках
    hop_latency=1.0,   # средняя задержка одной пересылки
    c_hop=50.0,        # скорость одного звена, символов в единицу времени
    p_drop=0.1,        # вероятность потерять фрагмент на пересылке
    p_corrupt=0.03,    # вероятность исказить фрагмент на пересылке
    prior=0.0,         # доля сообщения, которую Z угадывает по контексту
    L_direct=1.0,      # задержка прямого канала
    c_direct=20.0,     # скорость прямого канала
    trials=4000,
):
    f = N / k
    k_eff = max(1, math.ceil(k * (1 - prior)))
    t_direct = L_direct + N / c_direct

    hops = 1 + RNG.poisson(hops_mean - 1, size=(trials, m))
    max_h = hops.max()
    lat = RNG.exponential(hop_latency, size=(trials, m, max_h)) + f / c_hop
    mask = np.arange(max_h)[None, None, :] < hops[:, :, None]
    arrival = (lat * mask).sum(axis=2)

    alive = (RNG.random((trials, m, max_h)) >= p_drop) | ~mask
    delivered = alive.all(axis=2)
    clean = ((RNG.random((trials, m, max_h)) >= p_corrupt) | ~mask).all(axis=2)
    arrival = np.where(delivered, arrival, np.inf)

    order = np.argsort(arrival, axis=1)
    arr_sorted = np.take_along_axis(arrival, order, axis=1)
    bad_sorted = ~np.take_along_axis(clean, order, axis=1)
    r = np.arange(1, m + 1)[None, :]
    e = np.cumsum(bad_sorted, axis=1)
    ok = (r >= k_eff + 2 * e) & np.isfinite(arr_sorted)
    first = np.where(ok.any(axis=1), ok.argmax(axis=1), -1)
    t_net = np.where(first >= 0, arr_sorted[np.arange(trials), first], np.inf)

    return {
        "t_direct": t_direct,
        "t_net_median": float(np.median(t_net)),
        "p_win": float(np.mean(t_net < t_direct)),
        "p_fail": float(np.mean(~np.isfinite(t_net))),
    }


def simulate_tolerance(
    q=0.8,             # доля сообщения, которую Z должен знать верно
    N=1000, k=10, m=30, hops_mean=4.0, hop_latency=1.0, c_hop=50.0,
    p_drop=0.1, p_corrupt=0.03, L_direct=1.0, c_direct=20.0, trials=4000,
):
    """Без кодирования: сообщение режется на k кусков, каждый отправляется
    m // k копиями по разным маршрутам. Z берёт первую пришедшую копию куска.
    Искажённый кусок не исправляется — он просто входит в допустимую ошибку.
    Z принимает решение, когда верно известна доля q сообщения."""
    reps = m // k
    f = N / k
    t_direct = L_direct + N / c_direct

    hops = 1 + RNG.poisson(hops_mean - 1, size=(trials, k, reps))
    max_h = hops.max()
    mask = np.arange(max_h)[None, None, None, :] < hops[..., None]
    lat = RNG.exponential(hop_latency, size=(trials, k, reps, max_h)) + f / c_hop
    arrival = (lat * mask).sum(axis=3)
    delivered = ((RNG.random(lat.shape) >= p_drop) | ~mask).all(axis=3)
    clean = ((RNG.random(lat.shape) >= p_corrupt) | ~mask).all(axis=3)
    arrival = np.where(delivered, arrival, np.inf)

    first = arrival.argmin(axis=2)
    t_piece = np.take_along_axis(arrival, first[..., None], axis=2)[..., 0]
    ok_piece = np.take_along_axis(clean, first[..., None], axis=2)[..., 0]
    t_good = np.where(ok_piece, t_piece, np.inf)        # когда кусок стал известен верно

    need = math.ceil(q * k)
    t_net = np.sort(t_good, axis=1)[:, need - 1]
    return {
        "t_direct": t_direct,
        "p_win": float(np.mean(t_net < t_direct)),
        "p_fail": float(np.mean(~np.isfinite(t_net))),
    }


def main():
    print("Базовый сценарий:", simulate())
    print()

    speeds = np.geomspace(5, 400, 30)
    curves = {}
    for prior in (0.0, 0.5, 0.8):
        curves[prior] = [simulate(c_direct=c, prior=prior)["p_win"] for c in speeds]

    print("P(сарафан быстрее) в зависимости от скорости прямого канала:")
    print(f"{'c_direct':>9} | " + " | ".join(f"prior={p:.1f}" for p in curves))
    for i in range(0, len(speeds), 4):
        print(f"{speeds[i]:9.1f} | " + " | ".join(f"{curves[p][i]:9.2f}" for p in curves))
    print()

    print("Влияние доли искажений (c_direct=40, prior=0):")
    print(f"{'p_corrupt':>9} | {'P(win)':>6} | {'P(fail)':>7}")
    for pc in (0.0, 0.02, 0.05, 0.1, 0.2):
        res = simulate(c_direct=40, p_corrupt=pc)
        print(f"{pc:9.2f} | {res['p_win']:6.2f} | {res['p_fail']:7.2f}")

    print("Допустимая ошибка: P(сарафан быстрее), p_corrupt=0.03")
    tol_curves = {"точно, с кодированием": [simulate(c_direct=c)["p_win"] for c in speeds]}
    for q in (0.9, 0.8, 0.6):
        tol_curves[f"{int(q*100)}% верно"] = [
            simulate_tolerance(q=q, c_direct=c)["p_win"] for c in speeds
        ]
    print(f"{'c_direct':>9} | " + " | ".join(f"{name:>21}" for name in tol_curves))
    for i in range(0, len(speeds), 4):
        print(f"{speeds[i]:9.1f} | " + " | ".join(f"{tol_curves[n][i]:21.2f}" for n in tol_curves))
    print()

    print("Устойчивость к искажениям (c_direct=40):")
    print(f"{'p_corrupt':>9} | {'точно':>6} | {'80%':>6} | {'60%':>6}")
    for pc in (0.0, 0.05, 0.1, 0.2, 0.3):
        a = simulate(c_direct=40, p_corrupt=pc)["p_win"]
        b = simulate_tolerance(q=0.8, c_direct=40, p_corrupt=pc)["p_win"]
        c = simulate_tolerance(q=0.6, c_direct=40, p_corrupt=pc)["p_win"]
        print(f"{pc:9.2f} | {a:6.2f} | {b:6.2f} | {c:6.2f}")

    fig2, ax2 = plt.subplots(figsize=(8, 4.5))
    for name, ys in tol_curves.items():
        ax2.plot(speeds, ys, label=name, linewidth=2)
    ax2.axvline(50, color="grey", linestyle=":", label="скорость одного звена сети")
    ax2.set_xscale("log")
    ax2.set_xlabel("Скорость прямого канала A→Z (символов в единицу времени)")
    ax2.set_ylabel("Вероятность, что сеть быстрее")
    ax2.set_title("Допустимая ошибка: сколько нужно знать, чтобы решить")
    ax2.grid(alpha=0.3)
    ax2.legend()
    fig2.tight_layout()
    fig2.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)), "figures", "sarafan_tolerance.png"), dpi=150)
    print("График: sarafan_tolerance.png")

    fig, ax = plt.subplots(figsize=(8, 4.5))
    labels = {0.0: "Z ничего не знает", 0.5: "Z угадывает 50%", 0.8: "Z угадывает 80%"}
    for p, ys in curves.items():
        ax.plot(speeds, ys, label=labels[p], linewidth=2)
    ax.axvline(50, color="grey", linestyle=":", label="скорость одного звена сети")
    ax.set_xscale("log")
    ax.set_xlabel("Скорость прямого канала A→Z (символов в единицу времени)")
    ax.set_ylabel("Вероятность, что сеть быстрее")
    ax.set_title("Когда сарафанное радио обгоняет прямую передачу")
    ax.grid(alpha=0.3)
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)), "figures", "sarafan_sim.png"), dpi=150)
    print("График: sarafan_sim.png")


if __name__ == "__main__" and len(sys.argv) == 1:
    main()


def simulate_gossip(
    q=0.8,             # доля сообщения, которую Z должен знать верно
    rule="confirm",    # "first": верить первому услышанному; "confirm": ждать двух совпадающих версий
    rho=0.0,           # вероятность, что кусок искажён у самого источника (все копии одинаково неверны)
    N=1000, k=10, reps=3, hops_mean=4.0, hop_latency=1.0, c_hop=50.0,
    p_drop=0.1, p_corrupt=0.03, L_direct=1.0, c_direct=20.0, trials=4000,
):
    """Сарафан без кодирования: каждый кусок пересказывают reps людей разными путями.
    Независимые искажения дают разные неверные версии; общее искажение у источника
    (вероятность rho) делает все копии куска одинаково неверными.
    Возвращает вероятность успеть раньше прямого канала с долей верных кусков ≥ q
    и долю «уверенно неверных» кусков, которые Z принял за правду."""
    f = N / k
    t_direct = L_direct + N / c_direct
    hops = 1 + RNG.poisson(hops_mean - 1, size=(trials, k, reps))
    max_h = hops.max()
    mask = np.arange(max_h)[None, None, None, :] < hops[..., None]
    lat = RNG.exponential(hop_latency, size=(trials, k, reps, max_h)) + f / c_hop
    arrival = (lat * mask).sum(axis=3)
    delivered = ((RNG.random(lat.shape) >= p_drop) | ~mask).all(axis=3)
    clean = ((RNG.random(lat.shape) >= p_corrupt) | ~mask).all(axis=3)
    arrival = np.where(delivered, arrival, np.inf)
    source_bad = RNG.random((trials, k)) < rho            # общее искажение у источника
    # версия копии: 0 — правда; 1 — общая ложь источника; 2+ — уникальная случайная ошибка
    version = np.where(clean, 0, 2 + np.arange(reps)[None, None, :])
    version = np.where(source_bad[..., None] & clean, 1, version)

    order = np.argsort(arrival, axis=2)
    arr = np.take_along_axis(arrival, order, axis=2)
    ver = np.take_along_axis(version, order, axis=2)
    if rule == "first":
        t_known = arr[..., 0]
        v_known = ver[..., 0]
    else:  # первая пара совпадающих версий
        t_known = np.full((trials, k), np.inf)
        v_known = np.full((trials, k), -1)
        for j in range(1, reps):
            for i in range(j):
                same = (ver[..., i] == ver[..., j]) & np.isfinite(arr[..., j])
                better = same & (arr[..., j] < t_known)
                t_known = np.where(better, arr[..., j], t_known)
                v_known = np.where(better, ver[..., j], v_known)
    correct = (v_known == 0) & (t_known < t_direct)
    known = t_known < t_direct
    need = math.ceil(q * k)
    p_win = float(np.mean(correct.sum(axis=1) >= need))
    wrong_share = float(((known & (v_known != 0)).sum()) / max(1, known.sum()))
    return {"p_win": p_win, "wrong_share": wrong_share}


def gossip_table():
    print("Сарафан с повторением (3 пересказа на кусок), нужно 80% верного, c_direct=20:")
    print(f"{'rho':>5} | {'верить первому':>15} | {'ждать двух':>10} | {'ложь принята (первому / двух)':>30}")
    rows = []
    for rho in (0.0, 0.1, 0.3):
        a = simulate_gossip(rule="first", rho=rho)
        b = simulate_gossip(rule="confirm", rho=rho)
        rows.append((rho, a, b))
        print(f"{rho:5.1f} | {a['p_win']:15.2f} | {b['p_win']:10.2f} | "
              f"{a['wrong_share']:14.2f} / {b['wrong_share']:.2f}")
    return rows


def simulate_disclosure(
    policy="decision_first",  # "end": всё в момент T; "detail_first": главное последним; "decision_first": главное первым
    rho=0.0, relevant=3, step=5.0, t0=5.0,
    N=1000, k=10, reps=3, hops_mean=4.0, hop_latency=1.0, c_hop=50.0,
    p_drop=0.1, p_corrupt=0.03, L_direct=1.0, c_direct=20.0, trials=4000,
):
    """Официальный канал раскрывает по одному куску каждые `step` единиц времени.
    Решение Z зависит от `relevant` кусков. Каждый кусок Z узнаёт либо из слухов
    (первый услышанный пересказ, возможно неверный), либо из официального заявления
    (всегда верно). Возвращает: когда главное раскрыто официально, медиану опережения
    слухов, долю случаев, когда Z решил раньше официального раскрытия,
    и долю случаев, когда решил раньше и на неверных данных."""
    f = N / k
    T = L_direct + N / c_direct
    hops = 1 + RNG.poisson(hops_mean - 1, size=(trials, k, reps))
    max_h = hops.max()
    mask = np.arange(max_h)[None, None, None, :] < hops[..., None]
    lat = RNG.exponential(hop_latency, size=(trials, k, reps, max_h)) + f / c_hop
    arrival = (lat * mask).sum(axis=3)
    delivered = ((RNG.random(lat.shape) >= p_drop) | ~mask).all(axis=3)
    clean = ((RNG.random(lat.shape) >= p_corrupt) | ~mask).all(axis=3)
    arrival = np.where(delivered, arrival, np.inf)
    source_bad = RNG.random((trials, k)) < rho
    ok = clean & ~source_bad[..., None]
    first = arrival.argmin(axis=2)
    t_rum = np.take_along_axis(arrival, first[..., None], axis=2)[..., 0]
    ok_rum = np.take_along_axis(ok, first[..., None], axis=2)[..., 0]

    if policy == "end":
        t_off = np.full(k, T)
    else:
        order = list(range(k)) if policy == "decision_first" else list(range(relevant, k)) + list(range(relevant))
        t_off = np.empty(k)
        for pos, piece in enumerate(order):
            t_off[piece] = t0 + pos * step
    t_off_rel = t_off[:relevant].max()
    t_known = np.minimum(t_rum[:, :relevant], t_off[None, :relevant])
    from_rumour = t_rum[:, :relevant] < t_off[None, :relevant]
    wrong = (from_rumour & ~ok_rum[:, :relevant]).any(axis=1)
    t_dec = t_known.max(axis=1)
    early = t_dec < t_off_rel
    return {
        "t_off": float(t_off_rel),
        "lead_median": float(np.median(t_off_rel - t_dec)),
        "p_early": float(np.mean(early)),
        "p_early_wrong": float(np.mean(early & wrong)),
    }


def disclosure_table():
    print("Постепенное раскрытие: решение Z зависит от 3 кусков из 10, официально по куску каждые 5 единиц")
    print(f"{'политика':>15} | {'rho':>4} | {'главное офиц.':>13} | {'опережение (медиана)':>20} | {'решил раньше':>12} | {'раньше и неверно':>16}")
    names = {"end": "всё в конце", "detail_first": "сначала детали", "decision_first": "сначала главное"}
    for rho in (0.0, 0.3):
        for pol in ("end", "detail_first", "decision_first"):
            r = simulate_disclosure(policy=pol, rho=rho)
            print(f"{names[pol]:>15} | {rho:4.1f} | {r['t_off']:13.0f} | {r['lead_median']:20.1f} | {r['p_early']:12.2f} | {r['p_early_wrong']:16.2f}")


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "disclosure":
    disclosure_table()


def simulate_actions(
    policy="rumours",   # "rumours" | "date" | "partial" | "decision_first"
    depts=8, affected_n=3, per_dept=25, T=20.0, W0=40.0, t_disc=5.0,
    d=2.0, rumour_mean=5.0, e=0.1, rho=0.2, r_median=60.0, trials=2000, dt=0.5,
):
    """Преждевременные действия сотрудников.
    Каждый сотрудник действует (например, начинает искать работу), когда ожидаемая цена
    ожидания p·c·w превышает ожидаемую цену лишнего действия (1 − p)·R, то есть
    p / (1 − p) > r / w, где r = R / c индивидуально (логнормально), а w — сколько,
    по его мнению, ждать ответа: W0, если дата неизвестна, и T − t, если объявлена.
    Слух о своём отделе приходит в момент d + Exp(rumour_mean); с вероятностью rho
    он неверен у всего отдела (общий источник), иначе неверен с вероятностью e.
    До слуха или официального заявления сотрудник не знает о событии и не действует.
    Политики: rumours — только слухи, ответ в T; date — в t_disc объявлено только, когда будет ответ;
    partial — в t_disc объявлено, что два незатронутых отдела не затронуты;
    decision_first — в t_disc каждый отдел узнаёт свой статус."""
    n = depts * per_dept
    dept = np.repeat(np.arange(depts), per_dept)
    times = np.arange(0.0, T, dt)
    regret = np.zeros(trials)
    early_right = np.zeros(trials)
    for tr in range(trials):
        aff_d = RNG.choice(depts, affected_n, replace=False)
        aff = np.isin(dept, aff_d)
        r = np.exp(RNG.normal(np.log(r_median), 0.8, n))
        t_rum = d + RNG.exponential(rumour_mean, n)
        dept_wrong = RNG.random(depts) < rho
        wrong = dept_wrong[dept] | (RNG.random(n) < e)
        says_aff = np.where(wrong, ~aff, aff)
        unaff_d = np.setdiff1d(np.arange(depts), aff_d)
        excluded = np.isin(dept, unaff_d[:2])
        acted = np.zeros(n, bool)
        t_act = np.full(n, np.inf)
        e_eff = rho + (1 - rho) * e
        for t in times:
            if policy == "decision_first" and t >= t_disc:
                prior = aff.astype(float)
            elif policy == "partial" and t >= t_disc:
                prior = np.where(excluded, 0.0, affected_n / (depts - 2))
            else:
                prior = np.full(n, affected_n / depts)
            heard = t >= t_rum
            official = (policy != "rumours") and (t >= t_disc)
            aware = heard | official
            like_a = np.where(says_aff, 1 - e_eff, e_eff)
            like_n = np.where(says_aff, e_eff, 1 - e_eff)
            post = prior * like_a / (prior * like_a + (1 - prior) * like_n)
            p = np.where(heard & (prior > 0) & (prior < 1), post, prior)
            w = (T - t) if (policy == "date" and t >= t_disc) else W0
            with np.errstate(divide="ignore"):
                odds = np.where(p >= 1, np.inf, p / np.maximum(1 - p, 1e-12))
            go = (~acted) & aware & (odds * w > r)
            t_act[go] = t
            acted |= go
        regret[tr] = np.sum(acted & ~aff)
        early_right[tr] = np.sum(acted & aff)
    return {"regret": float(regret.mean()), "regret_share": float(regret.mean() / ((depts - affected_n) * per_dept)),
            "early_right": float(early_right.mean()), "early_right_share": float(early_right.mean() / (affected_n * per_dept))}


def actions_table():
    print("Преждевременные действия: 200 сотрудников, 8 отделов, 3 затронуты, ответ в T=20")
    names = {"rumours": "только слухи", "date": "объявлена дата", "partial": "частично (2 отдела)",
             "decision_first": "сначала главное"}
    print(f"{'политика':>20} | {'лишних действий':>15} | {'доля незатронутых':>17} | {'затронутых успели':>17}")
    for pol in ("rumours", "date", "partial", "decision_first"):
        r = simulate_actions(policy=pol)
        print(f"{names[pol]:>20} | {r['regret']:15.1f} | {r['regret_share']:17.2f} | {r['early_right_share']:17.2f}")


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "actions":
    actions_table()


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "gossip":
    gossip_table()
