# grapevine

An attempt to measure the speed of grapevine.

**When does a rumour network outrun the official channel?** This repository formalizes the hypothesis that a receiver *Z* can reconstruct a message from fragmentary, partly unreliable network reports faster than it receives the exact message directly from the source *A*, and studies what follows from it in organizations: leaks, gradual disclosure by an authoritative source, and premature actions taken on rumours.

- **Paper:** [`paper/sarafan.pdf`](paper/sarafan.pdf) — 7 pages, Russian, two columns, English abstract.
- **Proofs:** 91 theorems in Lean 4 + Mathlib, no `sorry`, only the standard axioms (`propext`, `Quot.sound`, `Classical.choice`).
- **Simulations:** Monte Carlo illustrations in [`simulation/simulate.py`](simulation/simulate.py).

## Main result

The network wins (Z can decide before direct delivery at time T) if and only if

```
⌈log₂ N(ε)⌉  ≤  C · (T − 1 − d)
```

where `N(ε)` is the covering number of what Z still does not know at error tolerance ε, `C` is the min-cut capacity of the network, and `d` its minimal delay. The left side is what Z needs to learn; the right side is what the network can deliver before the official message arrives.

Extensions proved in the repository:

| Topic | Result |
|---|---|
| Source does not know what Z knows | Exact criterion via colouring of a confusability graph; price of this ignorance ≤ log₂((Δ+1)/max_y\|M_y\|) bits |
| Mosaic effect | The same hint gives 0 bits to an outsider and everything to an insider; Shamir threshold sharing |
| Leakage risk | Risk over T days ≤ T·Σp_j — depends on the number of independent circles of insiders, not on headcount |
| Conflict of interest | Crawford–Sobel: an N-interval equilibrium exists iff 2N(N−1)b < 1, so credible information is ≤ log₂N(b) bits per round |
| Gradual disclosure | Decision-first order is optimal (⌈log₂K⌉ questions); silence carries information |
| Premature actions | Disclosure that fully resolves the key question for a group eliminates regretted actions there; partial disclosure that leaves it open can increase them |

## Repository layout

```
Sarafan.lean             model, theorems 1 and 2, corollaries, pentagon example
SarafanMosaic.lean       context, secret sharing, levers, leakage
SarafanCheapTalk.lean    Crawford–Sobel bound
SarafanExact.lean        exact theorem via covering number, price of ignorance,
                         inverse problem (estimating C), leakage by circles
SarafanDisclosure.lean   gradual disclosure, decision-first order, silence
SarafanActions.lean      consequence: premature actions on rumours
lakefile.toml, lean-toolchain, lake-manifest.json
simulation/              simulate.py and its figures
paper/                   LaTeX source, figures, data, compiled PDF
docs/theorems.md         full list of theorems with explanations (Russian)
```

## Checking the proofs

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh   # if Lean is not installed
lake exe cache get   # download prebuilt Mathlib
lake build           # check all proofs
```

The modules import only the parts of Mathlib they need (~2000 files), so building Mathlib from source without the cache takes about an hour.

To list the axioms a theorem depends on:

```lean
import SarafanActions
#print axioms Sarafan.Actions.regret_only_unresolved
```

## Simulations

```bash
cd simulation
python3 simulate.py              # base model: network vs direct channel, error tolerance
python3 simulate.py gossip       # repetition instead of coding, shared source of distortion
python3 simulate.py disclosure   # three official disclosure policies
python3 simulate.py actions      # premature actions of 200 employees under four policies
```

Requires `numpy` and `matplotlib`. Simulations illustrate the model with chosen parameters; they are not evidence about real organizations.

## Building the paper

```bash
cd paper
python3 figs.py                  # regenerate figures (optional)
xelatex sarafan.tex && xelatex sarafan.tex
```

Uses XeLaTeX with Liberation Serif, Latin Modern Math and DejaVu Sans Mono.

## Status and limitations

What Lean guarantees is that the conclusions follow from the stated assumptions. The assumptions themselves — a network characterized by capacity C after delay d, receiver knowledge as a set of compatible messages, independent circles of insiders, the receiver choosing the interval midpoint in the Crawford–Sobel model — are modelling choices. Asymptotic (Shannon, Slepian–Wolf, Wyner–Ziv) results are cited, not formalized. Numbers in the examples are assumed, not measured; the paper states six falsifiable predictions and an inverse-problem method for estimating C from past announcements.

---

## Кратко по-русски

Репозиторий формализует гипотезу о «сарафанном радио»: получатель Z может восстановить сообщение по обрывкам из сети раньше, чем получит его напрямую, тогда и только тогда, когда ему не хватает меньше информации, чем сеть успевает доставить до прихода прямого сообщения. Практическое следствие: раскрытие главного факта, которое полностью закрывает вопрос для группы, убирает у неё действия, совершённые на слухах, а частичное раскрытие, оставляющее вопрос открытым, может их увеличить.

Статья — [`paper/sarafan.pdf`](paper/sarafan.pdf), полный список теорем с пояснениями — [`docs/theorems.md`](docs/theorems.md).
