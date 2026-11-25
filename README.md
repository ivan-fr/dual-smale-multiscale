# Exact Radial-Lift Stability, Multi-Scale Cluster Confinement, and the Non-Vanishing Threshold for the Dual Smale Mean Value Conjecture

Pure **Lean 4.36.0** formalization (**5,571 lines across 7 modules**, **25 audited theorems**, zero `sorry`, zero `native_decide`, strictly `[propext, Classical.choice, Quot.sound]`, zero floating-point or external numerical dependencies) establishing a unified suite of **exact all-degree ($n \ge 2$)** theorems on the Dual Smale Mean Value Conjecture:

$$\forall P(z) = z + a_2 z^2 + \dots + a_n z^n \in \mathbb{C}[z]\ (a_n \neq 0, n \ge 2), \qquad \max_{P'(\zeta) = 0} \left|\frac{P(\zeta)}{\zeta}\right| \ge \frac{1}{n}.$$

## Main Formally Verified Theorems

1. **Exact Radial-Integral Master Theorem, Harmonic Mean Bound, and Quantitative Circle Stability** ([`DualSmaleMultiscale/RadialLift.lean`](lean/DualSmaleMultiscale/RadialLift.lean), [`DualSmaleMultiscale/ExactCriticalValue.lean`](lean/DualSmaleMultiscale/ExactCriticalValue.lean)):
   $$\max_j |P(\zeta_j)| \ge \int_0^{r_1} \prod_{k=1}^{n-1} (1 - |w_k|\, r)\, dr \ge \frac{1}{\frac{1}{r_1} + \sum_{k=1}^{n-1} |w_k|} \ge \frac{r_1}{n}.$$
   - Immediate exact corollaries: harmonic mean $\ge \frac{1}{2\sum |w_k|}$, bounded spread $\ge \frac{1}{\kappa n}$, closest-critical-point $1/n$ dichotomy, and exact equal-modulus Dual Smale $\ge 1/n$.
   - **Quantitative Circle Stability & Strict Uniqueness**: For $|\zeta_k| = R$ with $u_k = R w_k \in \partial\mathbb{D}$,
     $$\max_j \left|\frac{P(\zeta_j)}{\zeta_j}\right| \ge \frac{1}{n} + \frac{|u_{i_0} - u_{j_0}|^2}{16\, n(n - 1)} \qquad (\forall\, i_0, j_0),$$
     implying strict uniqueness of $P_{n,c}(z) = \frac{1 - (1 - cz)^n}{nc}$ on every circle.

2. **Multi-Scale Inner-Cluster Confinement Theorem** ([`DualSmaleMultiscale/MultiScaleConfinement.lean`](lean/DualSmaleMultiscale/MultiScaleConfinement.lean)):
   If a nonempty inner cluster $I$ satisfies $r_1 \le |\zeta_k| \le r_m$ ($k \in I$) and $r_m \sum_{k \notin I} |w_k| \le \frac{1}{36}$ (constant threshold independent of $m$ and $n$), then $|P(z)| > 6 r_m$ everywhere on $|z| = 6 r_m$ (via Grace–Walsh–Szegő with external holomorphic multiplier), confining the radial lift to hit an **inner** critical point $\zeta_j$ ($j \in I$) with:
   $$\left|\frac{P(\zeta_j)}{\zeta_j}\right| \ge \frac{1}{\frac{r_m}{r_1} + \sum_{k \in I} r_m |w_k| + \frac{1}{36}}.$$
   - **Exact $1/n$ Corollary**: Every separated equal-modulus inner cluster of size $m \le n - 2$ satisfies the **exact** Dual Smale Conjecture $\max_{j \in I} |P(\zeta_j)/\zeta_j| \ge 1/n$, regardless of global spread $\kappa(P) = r_{\max}/r_1$.

3. **Harmonic-Sum Dual Smale Theorems** ([`DualSmaleMultiscale/HarmonicAndThreshold.lean`](lean/DualSmaleMultiscale/HarmonicAndThreshold.lean)):
   - $S_j = \sum_{k \neq j} |\zeta_j / \zeta_k| \le 1 \implies |P(\zeta_j)/\zeta_j| \ge 3 - e > 5/18$.
   - $S_j \le 7/4 \implies |P(\zeta_j)/\zeta_j| > 18/1000$.
   - **Chebyshev-Squared Corollary**: $|\zeta_k| = k^2 r_1 \implies |P(\zeta_1)/\zeta_1| > 5/18$ for all $n \ge 2$ and arbitrary phases.

4. **Exact Closest-Critical-Point Non-Vanishing Threshold ($2 \le n \le 9$) & Sharpness at $n = 10$** ([`DualSmaleMultiscale/HarmonicAndThreshold.lean`](lean/DualSmaleMultiscale/HarmonicAndThreshold.lean)):
   - For all $2 \le n \le 9$, no closest critical point $\zeta_{j_0}$ satisfies $P(\zeta_{j_0}) = 0$ (proved via GWS + Cayley transform + exact rational Wall–Routh continued-fraction Hurwitz certificates).
   - At $n = 10$, there exists $w_0 \in D(1/8 - 7i/8, 1/50) \subset \mathbb{D} \setminus \{0\}$ such that $P'(z) = (1 - z)(1 - w_0 z)^8$ satisfies $P(1) = 0$ at its unique closest critical point $\zeta_1 = 1$.

5. **Exact Jacobi–Christoffel–Darboux Univalent Obstruction Family ($n = 2k$)** ([`DualSmaleMultiscale/JacobiObstruction.lean`](lean/DualSmaleMultiscale/JacobiObstruction.lean)):
   For every $k \ge 1$ ($n = 2k$), explicit orthogonal Jacobi-$(0, 1)$ polynomials $Q_k$ satisfy $Q_k(0) = 1$, $P'_k(x) = (1 - x) Q_k(x)^2 \ge 0$ on $[0, 1]$, and exact integral
   $$P_k(1) = \int_0^1 (1 - x) Q_k(x)^2\, dx = \frac{1}{k(k + 1)} = \frac{4}{n(n + 2)}.$$

## Reproduction

```bash
cd lean
lake exe cache get
lake build DualSmaleMultiscale
lake env lean check_axioms.lean
```

Compile the paper PDF:
```bash
tectonic paper/dual_smale_multiscale.tex
# or: pdflatex paper/dual_smale_multiscale.tex
```

## Author & License
- **Author**: Ivan Besevic (ESIEE-IT, France — `ivan.besevic@edu.esiee-it.fr`, ORCID `0009-0004-4124-1465`)
- **License**: MIT (`LICENSE`)
