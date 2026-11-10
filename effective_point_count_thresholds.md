# Effective Point-Count Thresholds and Polynomial Zeta-Recovery Bounds for Abelian Varieties over Finite Fields

## Abstract

Let $A$ be a $g$-dimensional abelian variety over $\mathbf{F}_q$ with point counts $c_n(A) = \#A(\mathbf{F}_{q^n})$ for $n \ge 1$. Chidambaram and Keller recently proved that $c_1(A), \dots, c_g(A)$ uniquely determine the zeta function of $A$ whenever $q > (16 g^3 p(2g))^{2g+2}$, studied the minimal number $N(g)$ of extension point counts required for large $q$ (showing $N(2) = 2$, $N(3) = 2$, and $N(4) = 4$), and posed several questions in Section 7 of their paper concerning $N(5)$ and $N(6)$, the growth of $N(g)$ relative to $g$, the behavior at genus $8$, and whether a polynomial threshold $Q(g)$ suffices for $g$ point counts to determine the zeta function.

In this note we establish the following results:

1. **Small genera:** Using coupled cyclotomic norm differences, we prove $N(5) = 4$ (for $q \ge 10^5$), $N(6) = 4$ (for $q \ge 10^6$), and $N(7) = 5$ (upper bound for $q \ge 10^6$, together with an explicit ordinary $\mathbf{Z}[q]$-family valid for all prime powers $q \ge 5$).
2. **Genus $8$:** We realize the perturbation direction noted in Remark 7.10 of Chidambaram and Keller by an explicit ordinary $\mathbf{Z}[q]$-family valid for all prime powers $q \ge 4$, proving $N(8) \ge 5$. Conversely, for $N = 5$ we prove that every collision at $q \ge 10^8$ takes the single-parameter form $P_B(T) - P_A(T) = m_4 T^4(T^4 - 1)(T^4 - q^4)$ with $1 \le |m_4| \le 512$, satisfies $a_2 = a_1 q + a_1^2$ and $a_1 \in \{-2, -1, 0, 1\}$ for all sufficiently large $q$, and admits no $\mathbf{Z}[q]$-family of reciprocal $q$-Weil polynomials; the exact value $N(8) \in \{5, 6, 7, 8\}$ for sporadic prime powers remains open.
3. **Higher genera:** Combining Chebyshev base polynomials with totient summation, we prove that $N(g) \ge \bigl(\frac{\pi}{\sqrt{6}} - o(1)\bigr)\sqrt{g}$ as $g \to \infty$, and construct explicit ordinary $\mathbf{Z}[q]$-families via lattice reduction establishing $N(15) \ge 7$, $N(24) \ge 8$, and $N(32) \ge 9$.
4. **Polynomial threshold $Q(g)$:** Refining the inductive error analysis in Section 5 of Chidambaram and Keller via a re-centered geometric envelope $B_j^* = 4 g q^{-j/2 - (g+1)/4} (10g)^{j - (g+1)/2}$ and the exponential generating function for elementary symmetric polynomials, we prove that $c_1(A), \dots, c_g(A)$ uniquely determine the zeta function of $A$ whenever $q > (10g)^6 = 10^6 g^6$ for all $g \ge 2$.

---

## 1. Introduction and Cyclotomic Norm Setup

Let $A$ and $B$ be $g$-dimensional abelian varieties over a finite field $\mathbf{F}_q$, with Frobenius characteristic polynomials
$$P_A(T) = T^{2g} + a_1 T^{2g-1} + \dots + a_g T^g + q a_{g-1} T^{g-1} + \dots + q^g = \prod_{j=1}^{2g} (T - \alpha_j) \in \mathbf{Z}[T]$$
and point counts $c_n(A) = \#A(\mathbf{F}_{q^n}) = \prod_{j=1}^{2g}(1 - \alpha_j^n)$. By Tate's isogeny theorem [Tat66], $P_A = P_B$ if and only if $A$ and $B$ are $\mathbf{F}_q$-isogenous. Chidambaram and Keller [CK26] define $N(g)$ as the minimal positive integer $N$ for which there exists a threshold $q_0(g)$ such that for every prime power $q \ge q_0(g)$ and all $g$-dimensional abelian varieties $A, B / \mathbf{F}_q$, equality $c_n(A) = c_n(B)$ for $1 \le n \le N$ implies $P_A = P_B$. In [CK26, Theorem 1.1] they establish $N(g) \le g$ via an explicit iterative recovery algorithm running in $\widetilde{O}(g^4 \log q)$ bit operations [CK26b] for $q > Q(g) = (16 g^3 p(2g))^{2g+2}$, and in [CK26, Section 7] they prove $N(2) = 2$, $N(3) = 2$ ($q \ge 16$), and $N(4) = 4$ (with an explicit lower-bound family for $q \ge 8$), while posing Questions 7.8 and 7.9 and Remarks 7.10 and 7.12 on higher genera and polynomial thresholds.

Write $P_A(T) = T^g h_A(T + q/T)$, where
$$h_A(X) = X^g - b_1 X^{g-1} + b_2 X^{g-2} - \dots + (-1)^g b_g \in \mathbf{Z}[X]$$
is the real Frobenius trace polynomial, whose roots $x_j = \alpha_j + q/\alpha_j \in [-2\sqrt{q},\, 2\sqrt{q}]$ ($1 \le j \le g$) satisfy the elementary symmetric Weil bounds
$$|b_k| \le B_{g,k}\, q^{k/2}, \qquad B_{g,k} := \binom{g}{k} 2^k \qquad (1 \le k \le g). \tag{1}$$

For each integer $d \ge 1$, let $\Phi_d(T)$ denote the $d$-th cyclotomic polynomial and define the $d$-th cyclotomic norm
$$F_d(A) := \prod_{\Phi_d(\zeta) = 0} P_A(\zeta) \in \mathbf{Z}.$$
Since $T^n - 1 = \prod_{d \mid n} \Phi_d(T)$ and $\deg P_A = 2g$ is even, we have $c_n(A) = \prod_{d \mid n} F_d(A) > 0$. Moreover, $F_1(A) = P_A(1) = c_1(A) > 0$, $F_2(A) = P_A(-1) = c_2(A)/c_1(A) > 0$, and for $d \ge 3$ every root $\zeta$ of $\Phi_d$ is non-real on the unit circle, so $P_A(\zeta) P_A(\bar{\zeta}) = |P_A(\zeta)|^2 > 0$ gives $F_d(A) > 0$. By Möbius inversion in $\mathbf{Q}^\times$,
$$c_n(A) = c_n(B) \quad (1 \le n \le N) \qquad \Longleftrightarrow \qquad F_d(A) = F_d(B) \quad (1 \le d \le N). \tag{2}$$

Put $u := q + 1$ and $v := q - 1$. Using $P_A(\zeta) = \zeta^g h_A(\zeta + q\zeta^{-1})$, one obtains:

- $F_1(A) = h_A(u)$ and $F_2(A) = (-1)^g h_A(-u)$;
- $F_4(A) = P_A(i) P_A(-i) = |h_A(-i v)|^2 = \bigl(\operatorname{Re} h_A(-i v)\bigr)^2 + \bigl(\operatorname{Im} h_A(-i v)\bigr)^2$;
- $F_3(A) = N_{\mathbf{Q}(\omega)/\mathbf{Q}}\bigl(P_A(\omega)\bigr)$ where $\omega^2 + \omega + 1 = 0$ and $\omega + q\omega^{-1} = -q + (1 - q)\omega$;
- for every $d \ge 3$ ($\varphi(d)$ even), defining the monic trace-cyclotomic polynomial
  $$\Psi_d(X, q) := \operatorname{Res}_z\bigl(\Phi_d(z),\, z^2 - X z + q\bigr) = \prod_{\Phi_d(\zeta) = 0} \bigl(X - (\zeta + q\zeta^{-1})\bigr) \in \mathbf{Z}[q][X] \tag{3}$$
  of degree $\varphi(d)$ (together with $\Psi_1(X, q) := X - u$ and $\Psi_2(X, q) := X + u$), pairing conjugate roots $\zeta, \zeta^{-1}$ gives $\prod_{\Phi_d(\zeta)=0} \zeta^g = 1$ and hence $F_d(A) = \operatorname{Res}_X(\Psi_d(X, q), h_A(X))$ for all $d \ge 3$.

For two $g$-dimensional abelian varieties $A, B / \mathbf{F}_q$, write $d_k := b_k(B) - b_k(A)$ ($1 \le k \le g$), so $|d_k| \le 2 B_{g,k} q^{k/2}$. Three divisibility relations hold over $\mathbf{Z}$:

1. $F_1(B) = F_1(A)$ and $F_2(B) = F_2(A)$ hold if and only if $h_B(u) = h_A(u)$ and $h_B(-u) = h_A(-u)$, i.e. if and only if $X^2 - u^2$ divides $h_B(X) - h_A(X)$ in $\mathbf{Z}[X]$.
2. Whenever $h_B(X) - h_A(X) = (X^2 - u^2) Q(X)$ with $Q \in \mathbf{Z}[X]$, evaluating at $X = -i v$ uses $(-i v)^2 - u^2 = -2(q^2 + 1)$ to give $h_B(-i v) = h_A(-i v) - 2(q^2 + 1) Q(-i v)$ in $\mathbf{Z}[i]$, whence $F_4(B) - F_4(A) = -4(q^2 + 1)\,\operatorname{Re}\bigl(\overline{h_A(-i v)}\, Q(-i v)\bigr) + 4(q^2 + 1)^2 |Q(-i v)|^2$ is divisible by $4(q^2 + 1)$ identically, with primitive polynomial quotient
   $$E_4 := \frac{F_4(B) - F_4(A)}{4(q^2 + 1)}.$$
3. For every prime $\ell$, since $\zeta_\ell \equiv 1 \pmod{1 - \zeta_\ell}$ and $F_1(B) = F_1(A)$, one has $P_B(\zeta_\ell) \equiv P_A(\zeta_\ell) \pmod{1 - \zeta_\ell}$ in $\mathbf{Z}[\zeta_\ell]$; taking norms to $\mathbf{Q}$ shows that $\ell$ divides $F_\ell(B) - F_\ell(A)$ identically. In particular we set
   $$E_3 := \frac{F_3(B) - F_3(A)}{3}, \qquad E_5 := \frac{F_5(B) - F_5(A)}{5}.$$

**Ancillary files.** Python and C scripts carrying out the symbolic resultant computations, rational dominance bounds, Sturm root counts, and modular searches in Sections 2–4, together with the coefficient data for Theorem 4.2, accompany this note.

---

## 2. Determination of $N(5) = 4$, $N(6) = 4$, and $N(7) = 5$

In [CK26, Example 7.7], Chidambaram and Keller rule out $\mathbf{Z}[q]$-families colliding on $c_1, \dots, c_4$ for $g = 5, 6$, and ask in [CK26, Question 7.8] whether $N(5) = 4$ and $N(6) = 4$ hold across all abelian varieties over $\mathbf{F}_q$ for sufficiently large $q$. Because collisions at individual prime powers need not arise from polynomial families over $\mathbf{Z}[q]$, proving $N(g) \le N$ requires an archimedean elimination valid for arbitrary integer tuples $(b_1, \dots, b_g)$ satisfying $|b_k| \le B_{g,k} q^{k/2}$. Coupling $E_4$ with $E_3$ (and with $E_5$ at $g = 7$) yields explicit effective thresholds.

### Theorem 2.1 ($g = 5$, addressing [CK26, Question 7.8])
*For every prime power $q \ge 10^5$ and any $5$-dimensional abelian varieties $A, B / \mathbf{F}_q$, if $c_n(A) = c_n(B)$ for $1 \le n \le 4$, then $P_A = P_B$. Combined with $N(5) \ge N(4) = 4$ [CK26, Section 7], we have $N(5) = 4$.*

**Proof.** Suppose $F_d(A) = F_d(B)$ for $1 \le d \le 4$ and $q \ge 10^5$. Equating the odd and even parts of $h_B(\pm u) = h_A(\pm u)$ gives
$$d_5 + u^2 d_3 + u^4 d_1 = 0, \qquad d_4 + u^2 d_2 = 0.$$
At $g = 5$, $|d_3| \le 160 q^{3/2}$ and $|d_5| \le 64 q^{5/2}$. For $q \ge 10^5$,
$$|d_1| = \frac{|u^2 d_3 + d_5|}{u^4} \le \frac{160 q^{3/2}(q + 1)^2 + 64 q^{5/2}}{(q + 1)^4} < 1,$$
and since $d_1 \in \mathbf{Z}$, we obtain $d_1 = 0$. Consequently $d_4 = -u^2 d_2$ and $d_5 = -u^2 d_3$, which refine the Weil bounds on $d_2, d_3 \in \mathbf{Z}$ to
$$|d_2| = \frac{|d_4|}{u^2} \le \frac{160 q^2}{(q + 1)^2} < 160, \qquad |d_3| = \frac{|d_5|}{u^2} \le \frac{64 q^{5/2}}{(q + 1)^2} < 64 q^{1/2}.$$

Expanding $E_4 = (F_4(B) - F_4(A))/(4(q^2 + 1)) = 0$ in $\mathbf{Z}[q, d_2, d_3, b_1, \dots, b_5]$, its unique highest-weight monomial is $-q^6 d_2$. If $|d_2| \ge 1$, dividing every remaining monomial of $E_4$ by $|d_2|$ and bounding the variables via $|d_2| \le 160$, $|d_3| \le 64 q^{1/2}$, and $|b_k| \le B_{5,k} q^{k/2}$ ($1 \le k \le 5$), every remaining term has $q$-exponent at most $11/2$, and for all $q \ge 10^5$ their absolute sum is bounded by $\frac{1}{145.55}\, q^6 |d_2| < q^6 |d_2|$, contradicting $E_4 = 0$. Hence $d_2 = d_4 = 0$.

With $d_1 = d_2 = d_4 = 0$ and $d_5 = -u^2 d_3$, the unique highest-weight monomial of $E_3 = (F_3(B) - F_3(A))/3 = 0$ is $-q^7 d_3$. If $|d_3| \ge 1$, bounding all other terms via $|d_3| \le 64 q^{1/2}$ and $|b_k| \le B_{5,k} q^{k/2}$ shows that for all $q \ge 10^5$ their absolute sum is at most $\frac{1}{2200.45}\, q^7 |d_3| < q^7 |d_3|$, contradicting $E_3 = 0$. Thus $d_3 = d_5 = 0$ and $P_A = P_B$. $\blacksquare$

### Theorem 2.2 ($g = 6$, addressing [CK26, Question 7.8])
*For every prime power $q \ge 10^6$ and any $6$-dimensional abelian varieties $A, B / \mathbf{F}_q$, if $c_n(A) = c_n(B)$ for $1 \le n \le 4$, then $P_A = P_B$. Combined with $N(6) \ge N(4) = 4$, we have $N(6) = 4$.*

**Proof.** Suppose $F_d(A) = F_d(B)$ for $1 \le d \le 4$ and $q \ge 10^6$. From $h_B(\pm u) = h_A(\pm u)$, the odd relation $d_5 + u^2 d_3 + u^4 d_1 = 0$ with $|d_3| \le 320 q^{3/2}$ and $|d_5| \le 384 q^{5/2}$ gives $|d_1| < 1$ for $q \ge 10^6$, so $d_1 = 0$ and $d_5 = -u^2 d_3$. Parameterizing the even relation $d_6 + u^2 d_4 + u^4 d_2 = 0$ over $\mathbf{Z}$ by $m_4 := d_4 + u^2 d_2 \in \mathbf{Z}$ gives
$$d_4 = m_4 - u^2 d_2, \qquad d_5 = -u^2 d_3, \qquad d_6 = -u^2 m_4.$$
Using $2 B_{6,4} = 480$, $2 B_{6,5} = 384$, $2 B_{6,6} = 128$, successive division by $u^2 = (q + 1)^2$ yields, for every $q \ge 1$,
$$|m_4| = \frac{|d_6|}{u^2} < 128 q, \qquad |d_3| = \frac{|d_5|}{u^2} < 384 q^{1/2}, \qquad |d_2| \le \frac{|d_4| + |m_4|}{u^2} < \frac{480 q^2 + 128 q}{(q + 1)^2} < 480.$$

In $E_4 = 0$, the unique highest-weight monomial is $-q^8 d_2$; for $q \ge 10^6$, assuming $|d_2| \ge 1$ bounds the sum of all remaining terms by $\frac{1}{208.16}\, q^8 |d_2| < q^8 |d_2|$, forcing $d_2 = 0$.

Once $d_2 = 0$, the remaining parameters $(d_3, m_4)$ are coupled across $E_4|_{d_2 = 0} = 0$ and $E_3|_{d_2 = 0} = 0$:

- If $d_3 = 0$, then $E_4|_{d_2 = d_3 = 0} = 0$ has leading monomial $+q^6 m_4$, which dominates all lower-order terms for $q \ge 10^6$ unless $m_4 = 0$.
- Suppose $|d_3| \ge 1$. Isolating $+q^6 m_4$ in $E_4|_{d_2 = 0} = 0$ against the leading $d_3$-term $-b_1 q^6 d_3$ (with $|b_1| \le 12 q^{1/2}$) and summing the rational bounds on all remaining terms at $q_0 = 10^6$ gives
  $$|m_4| \le 12.01\, q^{1/2}\, |d_3|.$$
  Substituting this bound into $E_3|_{d_2 = 0} = 0$, whose leading monomial is $-q^9 d_3$, every $m_4$-bearing term (starting with $+q^7 m_4$, of size at most $12.01\, q^{15/2} |d_3|$) is strictly dominated: for $q \ge 10^6$, the non-leading sum is at most $\frac{1}{81.89}\, q^9 |d_3| < q^9 |d_3|$.

Hence $d_3 = 0$, and therefore $m_4 = 0$, giving $P_A = P_B$. $\blacksquare$

### Theorem 2.3 ($g = 7$)
*We have $N(7) = 5$. Specifically:*

1. *(Ordinary lower bound for all $q \ge 5$)* *Define $h_A, h_B \in \mathbf{Z}[q][X]$ by*
   $$\begin{aligned}
   h_A(X) &= X^7 - (7q + 1) X^5 + X^4 + (14q^2 + 6q) X^3 + (q^2 - 3q + 2) X^2 \\
          &\quad - (7q^3 + 7q^2 - 1) X - (3q^3 - 3q^2 + 5q - 1), \\
   h_B(X) &= h_A(X) - 2q\bigl(X^2 - (q + 1)^2\bigr),
   \end{aligned}$$
   *and set $P_A(T) = T^7 h_A(T + q/T)$, $P_B(T) = T^7 h_B(T + q/T)$. For every prime power $q \ge 5$, $P_A$ and $P_B$ are distinct ordinary $q$-Weil polynomials realized by non-isogenous $7$-dimensional ordinary abelian varieties $A, B / \mathbf{F}_q$ satisfying $c_n(A) = c_n(B)$ for $1 \le n \le 4$ and $c_5(A) \ne c_5(B)$.*
2. *(Effective upper bound)* *For every prime power $q \ge 10^6$ and any $7$-dimensional abelian varieties $A, B / \mathbf{F}_q$, equality $c_n(A) = c_n(B)$ for $1 \le n \le 5$ implies $P_A = P_B$.*

**Proof.**
(1) Direct resultant evaluation in $\mathbf{Z}[q]$ gives $F_d(B) - F_d(A) = 0$ for $d \in \{1, 2, 3, 4\}$, while $F_5(B) - F_5(A) = -10 q (8 q^{11} + \dots) \ne 0$ has no real roots on $[5, \infty)$. Moreover, $a_7(A) \equiv a_7(B) \equiv 1 \pmod{q}$, so $\gcd(a_7, q) = 1$ in every characteristic. Writing $u_s := q^{-1/2} \in (0, 9/20]$ for $q \ge 5$ (as $(20/9)^2 = 400/81 < 5$) and setting $H_\bullet(x, u_s) := u_s^7 h_\bullet(x/u_s)$, at the eight rational nodes
$$x \in \bigl\{-2,\; -\tfrac{9}{5},\; -\tfrac{6}{5},\; -\tfrac{2}{5},\; \tfrac{2}{5},\; \tfrac{6}{5},\; \tfrac{9}{5},\; 2\bigr\}$$
both $H_A(x, 0)$ and $H_B(x, 0)$ equal $2 T_7(x/2) = x^7 - 7 x^5 + 14 x^3 - 7 x$, which alternates strictly in sign ($-, +, -, +, -, +, -, +$), and Sturm root counts confirm that none of the sixteen polynomials $H_A(x_m, u_s), H_B(x_m, u_s) \in \mathbf{Q}[u_s]$ vanishes on $(0, 9/20]$. By the intermediate value theorem, for every $q \ge 5$ both $h_A$ and $h_B$ have $7$ distinct real roots in $(-2\sqrt{q}, 2\sqrt{q})$ (the threshold $q \ge 5$ is sharp for this pair, as $h_B$ has only $5$ real roots in $(-2\sqrt{q}, 2\sqrt{q})$ at $q = 4$). Thus all roots of $P_A$ and $P_B$ lie on $|T| = \sqrt{q}$ with no real roots, and since $\gcd(a_7, q) = 1$, their $p$-adic Newton polygons have slopes $0$ and $1$ (each of multiplicity $7$), forcing all local invariants in the Brauer group to vanish. By the Honda–Tate theorem [Hon68, Tat71] and the ordinary Weil polynomial criterion [Wat69, §7; How95, §3], $P_A$ and $P_B$ are realized by non-isogenous $7$-dimensional ordinary abelian varieties over $\mathbf{F}_q$.

(2) Suppose $F_d(A) = F_d(B)$ for $1 \le d \le 5$ and $q \ge 10^6$. From $h_B(\pm u) = h_A(\pm u)$, the odd relation $d_7 + u^2 d_5 + u^4 d_3 + u^6 d_1 = 0$ with $2 B_{7,3} = 560$, $2 B_{7,5} = 1344$, $2 B_{7,7} = 256$ gives $|d_1| < 1$ for $q \ge 10^6$, hence $d_1 = 0$. Setting $m_4 := d_4 + u^2 d_2 \in \mathbf{Z}$ and $m_5 := d_5 + u^2 d_3 \in \mathbf{Z}$ gives
$$d_4 = m_4 - u^2 d_2, \qquad d_5 = m_5 - u^2 d_3, \qquad d_6 = -u^2 m_4, \qquad d_7 = -u^2 m_5.$$
Dividing successively by $u^2 = (q + 1)^2$ gives, for all $q \ge 1$ ($2 B_{7,4} = 1120$, $2 B_{7,6} = 896$),
$$|m_4| < 896 q, \qquad |m_5| < 256 q^{3/2}, \qquad |d_3| < 1344 q^{1/2}, \qquad |d_2| < 1120.$$
We eliminate $(d_2, d_3, m_4, m_5)$ sequentially for $q \ge 10^6$:

- *Step 1 ($d_2 = 0$):* In $E_4 = 0$, the leading monomial $-q^{10} d_2$ dominates the sum of all remaining terms by a factor of $50.49$, forcing $d_2 = 0$.
- *Step 2 ($d_3 = 0$):* When $d_2 = 0$ and $|d_3| \ge 1$, isolating $+q^8 m_4$ in $E_4|_{d_2 = 0} = 0$ gives $|m_4| \le 17.59\, q^{1/2}\, |d_3|$. Substituting into $E_3|_{d_2 = 0} = 0$, the leading monomial $-q^{11} d_3$ dominates all remaining terms by a factor of $46.44$, forcing $d_3 = 0$.
- *Step 3 ($m_4 = m_5 = 0$):* When $d_2 = d_3 = 0$, if $m_5 = 0$ then $+q^8 m_4$ in $E_4|_{d_2 = d_3 = 0} = 0$ forces $m_4 = 0$. If $|m_5| \ge 1$, isolating $+q^8 m_4$ in $E_4|_{d_2 = d_3 = 0} = 0$ against $-b_1 q^6 m_5$ ($|b_1| \le 14 q^{1/2}$) yields
  $$|m_4| \le 14.01\, q^{-3/2}\, |m_5| < 3585.$$
  Substituting this bound into $E_5|_{d_2 = d_3 = 0} = 0$, the leading monomial $-q^{23} m_5$ dominates the sum of all remaining terms by a factor of $69.03$ for $q \ge 10^6$. Thus $m_5 = 0$ and $m_4 = 0$, proving $P_A = P_B$. $\blacksquare$

---

## 3. Genus $8$: Realization of Remark 7.10 and Elimination of $N = 5$ $\mathbf{Z}[q]$-Families

In [CK26, Remark 7.10], Chidambaram and Keller exhibit a nonzero perturbation direction at $g = 8$ preserving $F_1, \dots, F_4$ as identities in $q$, with $\delta_5 = -(q + 1)$, $\delta_7 = q^3 + 1$, and $\delta_k = 0$ for $k \in \{1, 2, 3, 4, 6, 8\}$. We first realize this perturbation direction by an explicit ordinary $\mathbf{Z}[q]$-family valid for every prime power $q \ge 4$, and then analyze $N = 5$ collisions at $g = 8$.

### Theorem 3.1 (Realization of [CK26, Remark 7.10]: $N(8) \ge 5$ for all $q \ge 4$)
*Define $h_A, h_B \in \mathbf{Z}[q][X]$ by*
$$\begin{aligned}
h_A(X) &= X^8 - 7q X^6 - X^5 + (15q^2 - q) X^4 + (-q^2 + 6q) X^3 \\
       &\quad + (-11q^3 + 17q^2 - 37q - 2) X^2 + (3q^3 - 8q^2 + q) X + (2q^4 - 15q^3 + 40q^2 + 1), \\
h_B(X) &= h_A(X) - (q + 1) X\bigl(X^2 - (q + 1)^2\bigr),
\end{aligned}$$
*and set $P_A(T) = T^8 h_A(T + q/T)$, $P_B(T) = T^8 h_B(T + q/T)$. Then*
$$P_B(T) - P_A(T) = -(q + 1)\bigl(T^{11} + q^3 T^5\bigr) + (q^3 + 1)\bigl(T^9 + q T^7\bigr),$$
*matching the perturbation vector of [CK26, Remark 7.10], and for every prime power $q \ge 4$ the polynomials $P_A, P_B$ are distinct ordinary $q$-Weil polynomials realized by non-isogenous $8$-dimensional ordinary abelian varieties $A, B / \mathbf{F}_q$ with $c_n(A) = c_n(B)$ for $1 \le n \le 4$ and $c_5(A) \ne c_5(B)$. Consequently, $N(8) \ge 5$.*

**Proof.** Expanding $P_B(T) - P_A(T) = -(q + 1) T^5(T^2 + q)\bigl((T^2 + q)^2 - (q + 1)^2 T^2\bigr)$ gives the stated polynomial with $\delta_5 = -(q + 1)$ and $\delta_7 = q^3 + 1$. Direct resultant computation in $\mathbf{Z}[q]$ confirms $F_d(B) - F_d(A) = 0$ for $1 \le d \le 4$, while $F_5(B) - F_5(A) = -5 q(q + 1)(q^{13} + \dots)$ has no real roots on $[4, \infty)$. Moreover, $a_8(A) \equiv a_8(B) \equiv 1 \pmod{q}$, ensuring ordinariness in every characteristic. At the nine rational nodes
$$x \in \bigl\{-2,\; -\tfrac{33}{20},\; -\tfrac{27}{20},\; -\tfrac{4}{5},\; 0,\; \tfrac{4}{5},\; \tfrac{27}{20},\; \tfrac{33}{20},\; 2\bigr\},$$
both $H_A(x, 0)$ and $H_B(x, 0)$ equal $x^8 - 7 x^6 + 15 x^4 - 11 x^2 + 2$, which alternates strictly in sign ($+, -, +, -, +, -, +, -, +$). Sturm root counts show $H_A(x_m, u_s) \ne 0$ on $(0, 1/2]$ ($q \ge 4$) and $H_B(x_m, u_s) \ne 0$ on $(0, 1/3]$ ($q \ge 9$), while Sturm counts at the four remaining prime powers $q \in \{4, 5, 7, 8\}$ confirm that $h_B(X)$ has $8$ distinct real roots in $(-2\sqrt{q}, 2\sqrt{q})$ there as well (the threshold $q \ge 4$ is sharp for this pair, as $h_B$ has only $4$ real roots in $(-2\sqrt{q}, 2\sqrt{q})$ at $q = 3$). Applying Honda–Tate theory [Tat71, How95] as in Theorem 2.3(1) yields the result. $\blacksquare$

At $g = 8$ and $N = 5$, the reciprocal polynomial $T^4(T^4 - 1)(T^4 - q^4)$ of degree $12 < 16$ vanishes identically on $\Phi_1, \Phi_2$, and $\Phi_4$, so $F_4(B) = F_4(A)$ alone cannot eliminate its coefficient $m_4$. Nevertheless, combining archimedean elimination on $(E_3, E_4, E_5)$ with Newton-sum Cauchy–Schwarz bounds and modular elimination rules out all $\mathbf{Z}[q]$-families on $c_1, \dots, c_5$:

### Proposition 3.2 (Structure of $g = 8, N = 5$ collisions and non-existence of $\mathbf{Z}[q]$-families)
*Let $g = 8$.*

1. *(Effective single-parameter reduction and Cauchy–Schwarz bounds)* *For every prime power $q \ge 10^8$ and any $8$-dimensional abelian varieties $A, B / \mathbf{F}_q$ with $P_A \ne P_B$ and $c_n(A) = c_n(B)$ for $1 \le n \le 5$, one has*
   $$P_B(T) - P_A(T) = m_4\, T^4(T^4 - 1)(T^4 - q^4) \tag{4}$$
   *for a nonzero integer $m_4 \in \mathbf{Z}$ satisfying $1 \le |m_4| \le 512$ (and $1 \le |m_4| \le 520$ for every $q \ge 12$ whenever (4) holds). Moreover, for all sufficiently large $q$, any such collision satisfies*
   $$a_2(A) = a_1(A)\, q + a_1(A)^2 \qquad \text{with} \qquad a_1(A) \in \{-2, -1, 0, 1\}.$$
2. *(No $\mathbf{Z}[q]$-family of reciprocal $q$-Weil polynomials)* *There exist no distinct polynomials $P_A, P_B \in \mathbf{Z}[q][T]$ such that for infinitely many prime powers $q$, $P_A$ and $P_B$ specialize to characteristic polynomials of $8$-dimensional abelian varieties over $\mathbf{F}_q$ (or, more generally, to reciprocal $q$-Weil polynomials of the form $T^8 h(T + q/T)$ with $h \in \mathbf{Z}[X]$ having all roots in $[-2\sqrt{q}, 2\sqrt{q}]$) satisfying $c_n(A) = c_n(B)$ for $1 \le n \le 5$.*

**Proof.**
(1) Assume $q \ge 10^8$ and $F_d(A) = F_d(B)$ for $1 \le d \le 5$. From $h_B(\pm u) = h_A(\pm u)$, the odd relation $d_7 + u^2 d_5 + u^4 d_3 + u^6 d_1 = 0$ with $2 B_{8,3} = 896$, $2 B_{8,5} = 3584$, $2 B_{8,7} = 2048$ gives $|d_1| < 1$ for $q \ge 10^8$, so $d_1 = 0$. Hence $h_B(X) - h_A(X)$ is divisible by $X^2 - u^2$:
$$h_B(X) - h_A(X) = d_2(X^6 - u^2 X^4) + d_3(X^5 - u^2 X^3) + m_4(X^4 - u^2 X^2) + m_5(X^3 - u^2 X) + \mu_6(X^2 - u^2)$$
with $d_2, d_3, m_4, m_5, \mu_6 \in \mathbf{Z}$. Since $d_8 = -u^2 \mu_6$, $d_7 = -u^2 m_5$, $d_6 = \mu_6 - u^2 m_4$, $d_5 = m_5 - u^2 d_3$, and $d_4 = m_4 - u^2 d_2$, successive division by $u^2 = (q + 1)^2$ ($2 B_{8,4} = 2240$, $2 B_{8,5} = 2 B_{8,6} = 3584$, $2 B_{8,7} = 2048$, $2 B_{8,8} = 512$) gives for all $q \ge 1$:
$$|\mu_6| < 512 q^2, \quad |m_5| < 2048 q^{3/2}, \quad |m_4| < 3584 q, \quad |d_3| < 3584 q^{1/2}, \quad |d_2| < 2240.$$
We eliminate $d_2, d_3, m_5$, and $\nu_6 := \mu_6 - v^2 m_4$ at $q_0 = 10^8$:

- *Eliminating $d_2$ and $d_3$:* In $E_4 = 0$, the leading monomial $-q^{12} d_2$ dominates the sum of all remaining terms by a factor of $1637.9$ for $q \ge 10^8$, forcing $d_2 = 0$. Setting $d_2 = 0$, if $|d_3| \ge 1$ then isolating $+q^{10} m_4$ in $E_4|_{d_2 = 0} = 0$ bounds $|m_4| / |d_3| = O(q^{1/2})$, under which $-q^{13} d_3$ in $E_3|_{d_2 = 0} = 0$ dominates all remaining terms by a factor of $440.5$; hence $d_3 = 0$. Isolating $+q^{10} m_4$ in $E_4|_{d_2 = d_3 = 0} = 0$ then gives the preliminary constant bound $|m_4| \le 33280$.
- *Coupled elimination of $(m_5, \nu_6)$:* Write $\mu_6 = v^2 m_4 + \nu_6$ ($v = q - 1$). Since $(X^4 - u^2 X^2) + v^2(X^2 - u^2) = (X^2 - u^2)(X^2 + v^2)$ vanishes at $X = \pm i v$, the variable $m_4$ cancels identically in $E_4|_{d_2 = d_3 = 0}$. In the remaining variables $(m_5, \nu_6)$, $E_4|_{d_2 = d_3 = 0} = 0$ has leading terms $-q^8 \nu_6 + b_1 q^8 m_5 + \dots$; if $m_5 = 0$ this forces $\nu_6 = 0$, while for $|m_5| \ge 1$ substituting $\nu_6 = b_1 m_5 + r_6$ gives $|r_6| \le 2240.01\, q^{-1/2} |m_5|$ and $|\nu_6| \le 16.01\, q^{1/2} |m_5|$ for $q \ge 10^8$.
- In $E_5|_{d_2 = d_3 = 0} = 0$, the leading terms are $-q^{27} m_5 + b_1 q^{27} m_4 + \dots$. If $m_4 = 0$, $-q^{27} m_5$ dominates all $(m_5, \nu_6)$-terms by a factor of $623.5$, forcing $m_5 = \nu_6 = 0$ (contradicting $P_A \ne P_B$). Hence $|m_4| \ge 1$, and isolating $-q^{27} m_5$ gives $|m_5| \le 16.04\, q^{1/2} |m_4|$, so $|\nu_6| \le 256.8\, q |m_4|$. Substituting into $d_8 = -u^2(v^2 m_4 + \nu_6)$ with $|d_8| \le 512 q^4$ yields $|m_4| \le 512$ for all $q \ge 10^8$ (and $|m_4| \le 512 q^4 / (q^2 - 1)^2 \le 520$ for all $q \ge 12$ once $\nu_6 = 0$).
- Next, substituting $\nu_6 = b_1 m_5 + r_6$ into $E_3|_{d_2 = d_3 = 0} = 0$ (whose leading $b_1$-term is $-q^{11} b_1 m_4$) bounds the integer $|b_1| \le 120$. Feeding $|b_1| \le 120$ back into $E_5|_{d_2 = d_3 = 0} = 0$ refines $|m_5| \le 240.4\, |m_4|$ and $|\nu_6| \le 28901\, |m_4|$. Isolating $c_2 := b_2 + (b_1 + 8)q$ in $E_3|_{d_2 = d_3 = 0} = 0$ (leading term $-q^{10} c_2 m_4$) then gives $|c_2| \le 31001$. Finally, substituting $b_2 = (-b_1 - 8)q + c_2$ into $E_5|_{d_2 = d_3 = 0} = 0$ cancels all $q^{27} m_4$ terms so that terms involving $m_4$ alone (with $m_5 = \nu_6 = 0$) have $q$-degree at most $26$; for $q \ge 10^8$, $-q^{27} m_5$ dominates the entire remainder by a factor of $4.30$, forcing $m_5 = 0$ and hence $\nu_6 = 0$.

With $d_1 = d_2 = d_3 = m_5 = \nu_6 = 0$, we have $h_B(X) - h_A(X) = m_4(X^2 - u^2)(X^2 + v^2)$, which pulls back under $X = T + q/T$ to $P_B(T) - P_A(T) = m_4 T^4(T^4 - 1)(T^4 - q^4)$.

Now let $q$ be sufficiently large with (4). Dividing $F_3(B) - F_3(A) = 0$ by $3 m_4$ gives
$$0 = a_1(q^{11} + 1) - a_2(q^{10} + q^6 + q^4 + 1) + a_3(q^5 + q^4) + a_4(q^8 + 1) - a_5(q^7 + q^4 + q^3 + 1) + a_6(q^4 + q^2) + a_7(q^5 + 1) - a_8(q^4 + 1) + q^8 + q^4 + m_4(q^8 + q^4 + 1). \tag{5}$$
Since $|a_1| = |b_1| \le 120$ and $|a_2 - a_1 q| = |c_2| \le 31001$, write $a_2 = a_1 q + r_2$ ($r_2 \in \mathbf{Z}$, $|r_2| \le 31001$). Then $a_1 q^{11} - a_2 q^{10} = -r_2 q^{10}$, giving $a_4 = r_2 q^2 + O(q^{3/2})$. Writing $s = \sqrt{q}$ and $a_k = t_k s^k$ for $k \in \{3, 5, 6, 7, 8\}$ ($t_k = O(1)$), expanding $(F_5(B) - F_5(A))/(5 m_4) = 0$ in powers of $s$ vanishes identically at $s^{54}$ and $s^{53}$ and has $s^{52}$-coefficient $r_2 - a_1^2$; since $r_2, a_1^2 \in \mathbf{Z}$, this forces $r_2 = a_1^2$ for all sufficiently large $q$, and the $s^{50}$-coefficient gives $t_6 = a_1^3 + t_3^2 + o(1)$.

Let $x_1, \dots, x_8 \in [-2, 2]$ be the scaled Frobenius traces $(\alpha_j + \bar{\alpha}_j)/\sqrt{q}$ of $A$, with elementary symmetric polynomials $\tilde{b}_k = q^{-k/2} b_k(A)$ and power sums $p_k = \sum_{j=1}^8 x_j^k$. As $q \to \infty$,
$$\tilde{b}_1 = o(1), \quad \tilde{b}_2 = a_1 - 8 + o(1), \quad \tilde{b}_3 = -t_3 + o(1), \quad \tilde{b}_4 = a_1^2 - 6 a_1 + 20 + o(1),$$
$$\tilde{b}_5 = 5 t_3 - t_5 + o(1), \quad \tilde{b}_6 = a_1^3 + t_3^2 - 4 a_1^2 + 9 a_1 - 16 + o(1),$$
and by Newton's identities, $p_2 = 16 - 2 a_1 + o(1)$ and $p_4 = 48 - 8 a_1 - 2 a_1^2 + o(1)$. Applying Cauchy–Schwarz to $(1, \dots, 1)$ and $(x_1^2, \dots, x_8^2)$ gives
$$0 \le 8 p_4 - p_2^2 = 128 - 20 a_1^2 + o(1),$$
forcing $|a_1| \le 2$ for sufficiently large $q$. At $a_1 = 2$, Newton's identities give $p_2 = 12 + o(1)$, $p_4 = 24 + o(1)$, and $p_6 = 36 - 3 t_3^2 + o(1)$, so Cauchy–Schwarz on $(x_1, \dots, x_8)$ and $(x_1^3, \dots, x_8^3)$ yields
$$0 \le p_2 p_6 - p_4^2 = -144 - 36 t_3^2 + o(1) \le -144 + o(1),$$
which is impossible for sufficiently large $q$. Thus $a_1 \in \{-2, -1, 0, 1\}$.

(2) Note first that every step in the proof of part (1) uses only the trace representation $P_\bullet(T) = T^8 h_\bullet(T + q/T)$ with $h_\bullet \in \mathbf{Z}[X]$ having all roots in $[-2\sqrt{q}, 2\sqrt{q}]$, and hence applies directly to arbitrary reciprocal $q$-Weil polynomials of degree $16$. Suppose $P_A, P_B \in \mathbf{Z}[q][T]$ are distinct polynomials specializing for infinitely many prime powers $q$ to reciprocal $q$-Weil polynomials of degree $16$ with $c_n(A) = c_n(B)$ for $1 \le n \le 5$. Write $a_k(A) = \sum_{j=0}^{\lfloor k/2 \rfloor} c_{k,j} q^j$ ($c_{k,j} \in \mathbf{Z}$, $24$ integer unknowns). By part (1), for all sufficiently large $q$ in this infinite set, $P_B(T) - P_A(T) = m_4(q) T^4(T^4 - 1)(T^4 - q^4)$ with $1 \le |m_4(q)| \le 512$; since $P_B - P_A \in \mathbf{Z}[q][T]$, $m_4 \in \mathbf{Z} \setminus \{0\}$ is constant with $1 \le |m_4| \le 512$, $a_1 = u_1 \in \{-2, -1, 0, 1\}$, and $a_2 = u_1 q + u_2$ with $u_2 = u_1^2$.

Equating all $q$-powers to zero in $(F_3(B) - F_3(A))/(3 m_4) = 0$ yields $12$ independent linear equations over $\mathbf{Z}$. Solving them expresses $12$ coefficients linearly in the remaining $12$ coefficients and $m_4$; in particular, the constant-term equation reads
$$u_2 = c_{2,0} = -c_{6,1} + c_{6,2} - c_{7,0} + c_{8,1} - c_{8,4} + \tfrac{1}{2} m_4 + 1,$$
forcing $m_4 = 2 k_4$ with $k_4 \in \mathbf{Z}$ and $1 \le |k_4| \le 256$ (or $|k_4| \le 260$ under the $q \ge 12$ bound $|m_4| \le 520$), with every solved $c_{k,j}$ a $\mathbf{Z}$-linear combination of the $12$ free $c_{k,j}$'s and $k_4$. Substituting into $(F_5(B) - F_5(A))/(5 m_4) \in \mathbf{Z}[q]$ gives a degree-$26$ polynomial in $q$ whose $q^{26}$-coefficient is $u_2 - u_1^2$ and (upon eliminating $c_{8,4}$ via $u_2 = u_1^2$) whose $q^{25}$-coefficient is $u_1^3 - c_{6,3}$. Setting $u_1 \in \{-2, -1, 0, 1\}$, $u_2 = u_1^2$, and $c_{6,3} = u_1^3$, the coefficients of $q^{24}$ and $q^{23}$ eliminate $(c_{6,2}, c_{7,2})$ linearly, and after substituting $c_{7,1} = c_{6,1} + c_{7,0} - W$ (setting $W := c_{6,1} + c_{7,0} - c_{7,1}$), the coefficients of $q^{22}$ and $q^{21}$ eliminate $(c_{6,1}, c_{7,0})$ linearly with constant integer pivots dividing $15$; the remaining equations are polynomials in $(c_{3,1}, c_{4,1}, c_{5,1}, c_{5,0}, W, k_4)$, with the $q^{20}$-equation linear in $c_{5,0}$.

For every prime $p \ge 7$, all pivots dividing $15$ are units modulo $p$. Exhaustive modular evaluation over $\mathbf{F}_p^4 \times (\mathbf{F}_p \setminus \{0\})$ (solving linearly for $c_{5,0} \bmod p$ when its $q^{20}$-coefficient is nonzero, or testing all $c_{5,0} \in \mathbf{F}_p$ when it vanishes) across the four branches $u_1 \in \{-2, -1, 0, 1\}$ finds no solutions with $k_4 \not\equiv 0 \pmod{p}$ for each $p \in \{7, 11, 13\}$. Consequently $7 \cdot 11 \cdot 13 = 1001 \mid k_4$, contradicting $1 \le |k_4| \le 256$. $\blacksquare$

**Remark 3.3 (Status of $N(8)$).** Theorem 3.1 and [CK26, Theorem 1.1] give $5 \le N(8) \le 8$, while Proposition 3.2 shows that no $\mathbf{Z}[q]$-family can raise $N(8)$ above $5$ and restricts any sporadic prime-power collision on $c_1, \dots, c_5$ to $P_B - P_A = m_4 T^4(T^4 - 1)(T^4 - q^4)$ with $a_2 = a_1 q + a_1^2$ and $a_1 \in \{-2, -1, 0, 1\}$. Determining whether sporadic non-polynomial collisions occur for arbitrarily large $q$, or whether further archimedean positivity constraints rule out the remaining four values of $a_1$ to establish $N(8) = 5$, remains open.

---

## 4. Higher Genera: Asymptotic $\sqrt{g}$ Lower Bound and Sublinear Families

In [CK26, Question 7.9], Chidambaram and Keller ask how $N(g)$ grows relative to $g$ as $g$ increases, noting that $N(g) = g$ for $g = 1, 2, 4$ whereas $N(3) = 2 < 3$ (and recalling via DiPippo and Howe [DH98, Theorem 1.1] in Remark 7.2 that the volume of the ordinary Weil locus is substantial). Theorems 2.1–2.3 show that strict sublinearity $N(g) < g$ holds at $g = 5, 6, 7$. Conversely, combining scaled Chebyshev polynomials with cyclotomic trace factors yields an $\Omega(\sqrt{g})$ lower bound on $N(g)$, complemented by lattice-reduced ordinary $\mathbf{Z}[q]$-families in moderate genera.

### Theorem 4.1 (Asymptotic $\sqrt{g}$ lower bound, addressing [CK26, Question 7.9])
*For every integer $N \ge 2$ and every integer $g \ge 2 \sum_{d=1}^N \varphi(d)$, we have $N(g) \ge N + 1$. Consequently, since $\sum_{d=1}^N \varphi(d) = \frac{3}{\pi^2} N^2 + O(N \log N)$ [HW08, Theorem 330],*
$$N(g) \ge \left(\frac{\pi}{\sqrt{6}} - o(1)\right)\sqrt{g} \qquad (g \to \infty),$$
*where $\pi/\sqrt{6} \approx 1.28255$.*

**Proof.** Since $N(g)$ is non-decreasing in $g$ (taking products with an ordinary elliptic curve over $\mathbf{F}_q$ preserves equality of point counts while incrementing the dimension), it suffices for each $N \ge 2$ to prove $N(g) \ge N + 1$ at the even integer $g = 2 D_N \ge 4$, where $D_N := \sum_{d=1}^N \varphi(d) \ge 2$.

Define $\Lambda_N(X, q) := \prod_{d=1}^N \Psi_d(X, q) \in \mathbf{Z}[q][X]$. Here $\Psi_1(X, q)\Psi_2(X, q) = X^2 - (q + 1)^2$, and for each $d \ge 3$ ($\varphi(d)$ even), grouping conjugate roots $\{\zeta, \zeta^{-1}\}$ of $\Phi_d$ gives
$$\Psi_d(X, q) = \prod_{\substack{\Phi_d(\zeta) = 0 \\ \operatorname{Im}\zeta > 0}} \Bigl(X^2 - c_\zeta(q + 1) X + q^2 + (c_\zeta^2 - 2)q + 1\Bigr), \qquad c_\zeta = \zeta + \zeta^{-1}.$$
In every quadratic factor (including $\Psi_1\Psi_2$), the coefficient of $X^{2 - r}$ ($r \in \{0, 1, 2\}$) has $q$-degree at most $r$, with $q^2$-coefficient $+1$ (for $d \ge 3$) or $-1$ (for $\Psi_1\Psi_2$) at $r = 2$, and constant term $+1$ (for $d \ge 3$) or $-1$ (for $\Psi_1\Psi_2$) at $X = q = 0$. Multiplying over $1 \le d \le N$ shows that $\Lambda_N(X, q)$ is monic of $X$-degree $D_N$, the coefficient of $X^{D_N - r}$ ($0 \le r \le D_N$) has $q$-degree at most $r$, and $\Lambda_N(0, q) = -q^{D_N} + \dots - 1 \equiv -1 \pmod{q}$. Under $X = x\sqrt{q}$, any monomial $q^j X^{D_N - r}$ of $\Lambda_N(X, q)$ equals $x^{D_N - r} q^{j + (D_N - r)/2}$, where $j + (D_N - r)/2 \le (D_N + r)/2 \le D_N = g/2$, with equality $j = r = D_N$ occurring solely at the leading term $-q^{D_N}$ of $\Lambda_N(0, q)$.

Let $T_g(y) = \cos(g \arccos y)$ be the $g$-th Chebyshev polynomial of the first kind. Since $g = 2 D_N$ is even, $C_g(X, q) := 2 q^{g/2} T_g(X/(2\sqrt{q})) \in \mathbf{Z}[q][X]$ is monic of degree $g$ with $C_g(0, q) = 2(-q)^{D_N} \equiv 0 \pmod{q}$. Define
$$h_A(X) := C_g(X, q) + q^{g/2} + 1, \qquad h_B(X) := h_A(X) + 2\Lambda_N(X, q).$$

We check the required properties:

1. *Valid $q$-degrees and ordinariness:* For $0 \le r \le D_N$, the term $X^{D_N - r}$ of $\Lambda_N(X, q)$ sits at index $k = g - (D_N - r) = D_N + r \ge 2r$ in $h_B(X)$, so its $q$-degree $j \le r \le \lfloor k/2 \rfloor$ satisfies the Weil polynomial degree bound. Moreover, $a_g(A) = h_A(0) \equiv 1 \pmod{q}$ and $a_g(B) = h_B(0) \equiv 1 + 2(-1) = -1 \pmod{q}$, so $\gcd(a_g, q) = 1$ in every characteristic.
2. *Cyclotomic agreement:* Since $\Psi_d(X, q) \mid (h_B(X) - h_A(X))$ in $\mathbf{Z}[q][X]$ for $1 \le d \le N$, we have $F_d(B) = F_d(A)$ for $1 \le d \le N$ and hence $c_n(A) = c_n(B)$ for $1 \le n \le N$, while $h_B \ne h_A$ implies $P_B \ne P_A$.
3. *Real roots in $(-2\sqrt{q}, 2\sqrt{q})$ for $q \ge q_0(N)$:* Substituting $X = x\sqrt{q}$ ($x \in [-2, 2]$), every term of $2\Lambda_N(x\sqrt{q}, q)$ other than $-2 q^{g/2}$ has $q$-exponent at most $(g - 1)/2$, so uniformly on $[-2, 2]$ as $q \to \infty$:
   $$q^{-g/2} h_A(x\sqrt{q}) = 2 T_g(x/2) + 1 + O_N(q^{-g/2}), \qquad q^{-g/2} h_B(x\sqrt{q}) = 2 T_g(x/2) - 1 + O_N(q^{-1/2}).$$
   At the $g + 1$ Chebyshev extrema $x_m = 2\cos(m\pi/g) \in [-2, 2]$ ($0 \le m \le g$), we have $2 T_g(x_m/2) = 2(-1)^m$, so $2 T_g(x_m/2) + 1 \in \{+3, -1\}$ and $2 T_g(x_m/2) - 1 \in \{+1, -3\}$ both alternate strictly in sign across $m = 0, 1, \dots, g$ with absolute value at least $1$. Since the $O_N(q^{-1/2})$ coefficient bound is explicit, there exists an explicit threshold $q_0(N)$ such that for every prime power $q \ge q_0(N)$, both $h_A$ and $h_B$ change sign strictly between consecutive nodes $x_m$ and therefore have $g$ distinct real roots in $(-2\sqrt{q}, 2\sqrt{q})$.

By Honda–Tate theory [Tat71, How95], $P_A$ and $P_B$ arise from non-isogenous $g$-dimensional ordinary abelian varieties over $\mathbf{F}_q$ for all prime powers $q \ge q_0(N)$, proving $N(g) \ge N + 1$. Inverting $g = 2 D_N = \frac{6}{\pi^2} N^2 + O(N\log N)$ gives $N(g) \ge \bigl(\frac{\pi}{\sqrt{6}} - o(1)\bigr)\sqrt{g}$. $\blacksquare$

In moderate genera, omitting small quadratic cyclotomic factors ($d \in \{3, 4, 6\}$, each with $\varphi(d) = 2$) from the polynomial divisor of $h_B - h_A$ and instead imposing $F_3(B) = F_3(A)$, $F_4(B) = F_4(A)$, $F_6(B) = F_6(A)$ as affine-linear hyperplanes on the coefficients of $h_A$ (solved via Hermite normal form and LLL lattice reduction around $C_g(X, q)$) yields examples in smaller genera:

### Theorem 4.2 (Explicit higher-genus ordinary families)
*Explicit ordinary $\mathbf{Z}[q]$-families $(h_A, h_B)$ establish the following lower bounds:*

| $g$ | $h_B(X) - h_A(X)$ | Matched counts | Threshold $q_0$ | Lower bound |
|---|---|---|---|---|
| $15$ | $24 q\,\Psi_1\Psi_2\Psi_5$ | $c_1, \dots, c_6$ ($c_7(A) \ne c_7(B)$) | $1{,}086{,}853$ | $N(15) \ge 7$ |
| $24$ | $2\,\Psi_1\Psi_2\Psi_5\Psi_7$ | $c_1, \dots, c_7$ ($c_8(A) \ne c_8(B)$) | $3{,}618{,}624{,}025$ | $N(24) \ge 8$ |
| $32$ | $2\,\Psi_1\Psi_2\Psi_5\Psi_7\Psi_8$ | $c_1, \dots, c_8$ ($c_9(A) \ne c_9(B)$) | $11{,}921{,}384{,}751{,}788{,}836$ | $N(32) \ge 9$ |

*In each case, for every prime power $q \ge q_0$ there exist non-isogenous $g$-dimensional ordinary abelian varieties $A, B / \mathbf{F}_q$ sharing $c_1, \dots, c_N$ and differing at $c_{N+1}$.*

**Proof.** The integer coefficient arrays of $h_A, h_B \in \mathbf{Z}[q][X]$ (with maximum coefficient magnitudes $5{,}510$, $30{,}861$, and $1{,}136{,}960$, respectively) and $g + 1$ rational separating nodes $-2 \le x_0 < \dots < x_g \le 2$ are recorded in the ancillary data file. For each $g \in \{15, 24, 32\}$:

1. Every coefficient of $X^{g - k}$ in $h_A$ and $h_B$ has $q$-degree at most $\lfloor k/2 \rfloor$, and $h_A(0) \equiv \pm 1 \pmod{q}$, $h_B(0) \equiv \pm 1 \pmod{q}$, giving ordinariness in every characteristic.
2. Polynomial resultant evaluation over $\mathbf{Z}[q]$ confirms $\operatorname{Res}_X(\Psi_d, h_B) = \operatorname{Res}_X(\Psi_d, h_A)$ for $1 \le d \le N$ and $\operatorname{Res}_X(\Psi_{N+1}, h_B) - \operatorname{Res}_X(\Psi_{N+1}, h_A) \ne 0$ with no real roots on $[q_0, \infty)$.
3. Writing $u_s = q^{-1/2}$, the scaled polynomials $H_A(x_m, u_s)$ and $H_B(x_m, u_s)$ alternate strictly in sign at $u_s = 0$ and have no roots on $(0, 1/K]$ (where $(K - 1)^2 < q_0 \le K^2$), while every prime power $q \in [q_0, K^2)$ is checked via Sturm root counting on $(-2\sqrt{q}, 2\sqrt{q})$. Honda–Tate theory [Tat71, How95] completes the proof. $\blacksquare$

**Remark 4.3 (Asymptotic upper bounds on $N(g)$).** While Theorem 4.1 establishes $N(g) = \Omega(\sqrt{g})$ and Theorems 2.1–2.3 show $N(g) < g$ for $g \in \{5, 6, 7\}$, the asymptotic upper-bound half of [CK26, Question 7.9]—in particular, whether $\limsup_{g \to \infty} N(g)/g < 1$ or $N(g) = o(g)$—remains open.

### Summary of Known Values and Bounds for $N(g)$

| Genus $g$ | $N(g)$ | Effective threshold | Reference |
|---|---|---|---|
| $1$ | $1$ | all prime powers $q$ | [CK26, Section 7] |
| $2$ | $2$ | odd $q$ (lower), all $q$ (upper) | [CK26, Section 7] |
| $3$ | $2$ | odd $q$ (lower), $q \ge 16$ (upper) | [CK26, Section 7] |
| $4$ | $4$ | $q \ge 8$ (lower) | [CK26, Section 7] |
| $5$ | $4$ | $q \ge 8$ (lower), $q \ge 10^5$ (upper) | Theorem 2.1 |
| $6$ | $4$ | $q \ge 8$ (lower), $q \ge 10^6$ (upper) | Theorem 2.2 |
| $7$ | $5$ | $q \ge 5$ (lower), $q \ge 10^6$ (upper) | Theorem 2.3 |
| $8$ | $\in \{5, 6, 7, 8\}$ | $q \ge 4$ (lower); no $\mathbf{Z}[q]$-family at $N = 5$ | Theorem 3.1, Proposition 3.2 |
| $15,\; 24,\; 32$ | $\ge 7,\; \ge 8,\; \ge 9$ | explicit ordinary $\mathbf{Z}[q]$-families | Theorem 4.2 |
| $g \to \infty$ | $\ge (\frac{\pi}{\sqrt{6}} - o(1))\sqrt{g}$ | Chebyshev–totient families | Theorem 4.1 |

---

## 5. A Polynomial Threshold $Q(g) = (10g)^6$ for Zeta Recovery

In [CK26, Theorem 1.1], Chidambaram and Keller prove that $c_1(A), \dots, c_g(A)$ determine the zeta function of $A$ whenever $q > Q(g) = (16 g^3 p(2g))^{2g+2}$ (with the inductive step of [CK26, Lemma 5.2] also formalized in Lean 4 [CK26b]), and ask in [CK26, Remark 7.12] whether $Q(g)$ can be chosen polynomial in $g$. In the analysis of [CK26, Sections 5–6], super-polynomial dependence on $g$ arises in two places:

1. In [CK26, Lemma 5.2], after isolating $\tilde{s}_k - s_k$ ($k \ge i$) in Macdonald's partition expansion of $e_{2g-m}$ and $e_m$, the cofactor sum over partitions $\lambda \vdash r$ ($r \in \{2g - m - k,\, m - k\}$) in $s_1, \dots, s_{i-1}$ is bounded term-by-term via the triangle inequality $\sum_{\lambda \vdash r} \prod_\ell \frac{|s_\ell|^{m_\ell}}{m_\ell! \ell^{m_\ell}} \le p(r)(2g q^{-1/2})^r$, introducing $p(2g)$ into $D = 16 g^3 p(2g)$ (which [CK26, Remark 7.12] notes can be reduced to $D = O(g^2)$, giving $Q(g) = g^{O(g)}$, via the partition generating function).
2. In [CK26, Lemma 5.3], the error envelope $B_j = g q^{-j/2 - g/4} D^{j - g}$ carries a negative exponent $j - g < 0$ in the seed range $g/2 < j < g$; matching the initial logarithm truncation error $|\tilde{s}_j - s_j| \le 4g q^{-j} \le B_j$ at $j = \lfloor g/2 \rfloor + 1$ then requires a power of $q$ to dominate $D^{\lfloor (g-1)/2 \rfloor}$, producing the exponent $2g + 2$ on $D$.

Both sources of super-polynomial growth can be avoided within the framework of [CK26, Sections 4–6]: keeping the signed cofactor sum over $\lambda \vdash r$ intact before taking absolute values—equivalently, expanding $e_M(\tilde{s}) - e_M(s)$ via Newton's exponential generating function—identifies the coefficient of $(\tilde{s}_k - s_k)/k$ directly as $(-1)^{k-1} e_r(s)$ (with $|e_r(s)| \le \binom{2g}{r} q^{-r/2} \le \frac{(2g)^r}{r!} q^{-r/2}$), and re-centering the geometric envelope at $(g + 1)/2$ rather than $g$ keeps the exponent $j - (g + 1)/2$ non-negative across the seed range $j > g/2$. Crucially, at $D = E$ the modified envelope $B_j^*$ differs from $B_j$ by the $j$-independent scalar $B_j^* / B_j = 4 q^{-1/4} E^{(g-1)/2}$, so the homogeneous degree-$1$ linear contraction of [CK26, Lemma 5.2] is preserved automatically while transferring the $E^{\Theta(g)}$ amplification from the $q^{1/4}$-constrained seed index $j = \lfloor g/2 \rfloor + 1$ to the final rounding step $j = 2g$, where the $q^{(g+1)/4}$ margin absorbs $E^{(3g-1)/2}$ under a fixed polynomial condition $q > E^6$.

### Theorem 5.1 (Polynomial threshold $Q(g) = (10g)^6$, addressing [CK26, Remark 7.12])
*For every integer $g \ge 2$ and every prime power $q > (10g)^6 = 10^6 g^6$, the first $g$ point counts $c_1(A), \dots, c_g(A)$ uniquely determine the zeta function of any $g$-dimensional abelian variety $A / \mathbf{F}_q$. Moreover, the recovery algorithm of [CK26, Sections 4–6] recovers $f_A(T)$ without modification for all $q > (10g)^6$.*

**Proof.** Following [CK26, Section 2], let $f_A(T) = T^{2g} P_A(1/T) = \prod_{\ell=1}^{2g} (1 - \alpha_\ell T)$ be the reciprocal Frobenius polynomial of $A$, set $\beta_\ell := \alpha_\ell^{-1}$ ($|\beta_\ell| = q^{-1/2}$), and write
$$f_A(T/q) = q^{-g} P_A(T) = \prod_{\ell=1}^{2g} (1 - \beta_\ell T) = \sum_{r=0}^{2g} (-1)^r e_r T^r,$$
with power sums $s_m := \sum_{\ell=1}^{2g} \beta_\ell^m$ ($m \ge 1$, satisfying $q^m s_m \in \mathbf{Z}$ and $|s_m| \le 2g q^{-m/2}$) and elementary symmetric polynomials $e_r = e_r(s)$ satisfying $|e_r(s)| \le \binom{2g}{r} q^{-r/2} \le \frac{(2g)^r}{r!} q^{-r/2}$ and the functional equation $e_{g+n}(s) = q^{-n} e_{g-n}(s)$ for $1 \le n \le g$ [CK26, Lemma 2.2].

Let $i \in \{1, \dots, g\}$ be the step index of [CK26, Sections 4–6], assuming $s_1, \dots, s_{i-1}$ have already been recovered exactly:

- *Step 1 ($1 \le i \le g/2$, [CK26, Lemma 4.1]):* This case requires only $q > (16g)^2 = 256 g^2$, which holds for all $g \ge 2$ since $(10g)^6 \ge 20^6 = 6.4 \times 10^7 > 256 g^2$ (as $10^6 g^4 > 256$).

Fix $g/2 < i \le g$ and assume $q > E^6$, where $E := 10g \ge 20$. For any $m \in \{2i - 1, 2i\}$ with $m > g$, suppose approximations $\tilde{s}_1, \dots, \tilde{s}_{m-1}$ satisfy $\tilde{s}_k = s_k$ for $1 \le k \le i - 1$, and write $\delta_k := \tilde{s}_k - s_k$ for $i \le k \le m - 1$. In the formal power series ring $\mathbf{R}[[T]]$, Newton's exponential identity $\sum_{r \ge 0} (-1)^r e_r(s) T^r = \exp\bigl(-\sum_{k \ge 1} \frac{s_k}{k} T^k\bigr)$ gives, modulo $T^{m+1}$,
$$\sum_{r=0}^m (-1)^r e_r(\tilde{s}_{<m}, s_m) T^r \equiv \left(\sum_{r \ge 0} (-1)^r e_r(s) T^r\right) \exp\!\left(-\sum_{k=i}^{m-1} \frac{\delta_k}{k} T^k\right) \pmod{T^{m+1}}.$$
Since $2i > m - 1$ for $m = 2i - 1$, and $2i = m$ is the unique quadratic index $\le m$ when $m = 2i$, while $2g - m < g < 2i$, extracting coefficients of $T^{2g - m}$ and $T^m$ yields the identities
$$e_{2g-m}(\tilde{s}) - e_{2g-m}(s) = \sum_{k=i}^{2g-m} (-1)^{k-1} \frac{\delta_k}{k}\, e_{2g-m-k}(s), \tag{6}$$
$$e_m(\tilde{s}_{<m}, s_m) - e_m(s) = \sum_{k=i}^{m-1} (-1)^{k-1} \frac{\delta_k}{k}\, e_{m-k}(s) + \mathbf{1}_{m=2i}\, \frac{\delta_i^2}{2 i^2}, \tag{7}$$
where $e_m(\tilde{s}_{<m}, s_m) - (-1)^{m-1} \frac{s_m}{m}$ is the polynomial in $(\tilde{s}_1, \dots, \tilde{s}_{m-1})$ used in [CK26, Lemma 5.1] to compute $\tilde{s}_m$. Substituting (6)–(7) into the formula of [CK26, Lemma 5.1] for $\frac{1}{m}(\tilde{s}_m - s_m)$ gives
$$|\tilde{s}_m - s_m| \le m \sum_{k=i}^{2g-m} \frac{|\delta_k|}{k}\, q^{-(m-g)} |e_{2g-m-k}(s)| + m \sum_{k=i}^{m-1} \frac{|\delta_k|}{k}\, |e_{m-k}(s)| + \mathbf{1}_{m=2i}\, \frac{|\delta_i|^2}{i}. \tag{8}$$

Define the modified error envelope for all $j \ge (g + 1)/2$:
$$B_j^* := 4g\, q^{-j/2 - (g+1)/4}\, E^{j - (g+1)/2}, \qquad E = 10g.$$
We check the base case, inductive propagation, and final integer rounding:

1. *Base case ($g/2 < j \le g$, cf. [CK26, Lemma 5.3]):* Since $j$ is an integer strictly greater than $g/2$, we have $2j \ge g + 1$, so $j - (g + 1)/2 \ge 0$. Because $q > 1$ and $E \ge 20 > 1$, the initial logarithm truncation error $|\tilde{s}_j - s_j| \le 4g q^{-j}$ of [CK26, Lemma 5.3] satisfies
   $$\frac{4g q^{-j}}{B_j^*} = \bigl(q^{1/2} E\bigr)^{-(j - (g+1)/2)} \le 1, \qquad \text{hence} \qquad |\tilde{s}_j - s_j| \le B_j^*.$$
2. *Inductive step ($g/2 < i \le g$, refining [CK26, Lemma 5.2]):* Suppose $|\delta_k| \le B_k^*$ holds for $i \le k \le 2i - 2$. We first establish $|\delta_m| \le B_m^*$ for $m = 2i - 1$ (if $2i - 1 = g$, this already holds by the base case; otherwise $2i - 1 > g$), and then for $m = 2i$. Setting $r := m - k \in \{1, \dots, m - i\}$, note that $r \le i \le g$, $m/k \le 2i/i = 2$, $|e_r(s)| \le \frac{(2g)^r}{r!} q^{-r/2}$, and in the first sum (where $r' := 2g - m - k = r - 2(m - g) \ge 0$),
   $$q^{-(m-g)} |e_{r'}(s)| \le q^{-(m-g)} \binom{2g}{r'} q^{-r'/2} \le \binom{2g}{r} q^{-r/2} \le \frac{(2g)^r}{r!} q^{-r/2}$$
   since $0 \le r' < r \le g$ implies $\binom{2g}{r'} \le \binom{2g}{r}$. Moreover, $B_{m-r}^* q^{-r/2} = B_m^* E^{-r}$. Thus the two linear sums together contribute at most
   $$2 \sum_{r=1}^{m-i} 2 B_{m-r}^* \frac{(2g)^r}{r!} q^{-r/2} = 4 B_m^* \sum_{r=1}^{m-i} \frac{(2g/E)^r}{r!} < 4\bigl(e^{1/5} - 1\bigr) B_m^* < 0.88562\, B_m^*.$$
   When $m = 2i$, the quadratic term $\frac{|\delta_i|^2}{i} \le \frac{(B_i^*)^2}{i}$ satisfies, since $i > g/2$ and $q > E^6 \ge 20^6$,
   $$\frac{(B_i^*)^2 / i}{B_{2i}^*} = \frac{4g}{i}\, q^{-(g+1)/4}\, E^{-(g+1)/2} < 8\, E^{-2(g+1)} \le 8 \cdot 20^{-6} = 1.25 \times 10^{-7}.$$
   Hence $|\tilde{s}_m - s_m| < (0.88562 + 1.25 \times 10^{-7}) B_m^* < 0.89\, B_m^* < B_m^*$, completing the induction up to $m = 2i$.
3. *Final integer rounding ($g/2 < i \le g$, following [CK26, Section 6]):* As in [CK26, Section 6], $s_i$ is recovered from $c_i(A)$ and $\tilde{s}_{2i}$ up to error $|\hat{s}_i - s_i| \le \frac{1}{2}|\tilde{s}_{2i} - s_{2i}| + 4g q^{-3i/2} \le \frac{1}{2} B_{2i}^* + 4g q^{-3i/2}$, and rounding $q^i \hat{s}_i$ to the nearest integer recovers $q^i s_i \in \mathbf{Z}$ uniquely provided $\frac{1}{2} B_{2i}^* < \frac{1}{4} q^{-i}$ and $4g q^{-3i/2} < \frac{1}{4} q^{-i}$. Since $i > g/2 \ge 1$ implies $i \ge 2$ and $q > (10g)^6 > 256 g^2$, we have $q^{i/2} \ge q > 16g$, giving $4g q^{-3i/2} < \frac{1}{4} q^{-i}$. Finally, $\frac{1}{2} B_{2i}^* < \frac{1}{4} q^{-i}$ is equivalent to $q^{(g+1)/4} > 8g\, E^{2i - (g+1)/2}$, which is strictest at $i = g$: raising both sides to the $4$-th power gives
   $$\bigl(8g\, E^{2g - (g+1)/2}\bigr)^4 = (8g)^4 (10g)^{6g - 2} = \bigl((10g)^6\bigr)^{g+1} \left(\frac{8g}{(10g)^2}\right)^4 = \bigl((10g)^6\bigr)^{g+1} \left(\frac{2}{25g}\right)^4 < q^{g+1}$$
   for every $g \ge 2$ and $q > (10g)^6$. Thus $|\hat{s}_i - s_i| < \frac{1}{2} q^{-i}$, recovering $s_i$ (and hence $s_1, \dots, s_g$ and $f_A(T)$) uniquely. $\blacksquare$

---

## References

- **[CK26]** S. Chidambaram and T. Keller, *Point counts of abelian varieties over finite fields determining their zeta function*, preprint, 2026, [arXiv:2606.28989v2](https://arxiv.org/abs/2606.28989).
- **[CK26b]** S. Chidambaram and T. Keller, *PointCountsAbelianVarieties* (SageMath and Lean 4 code accompanying [CK26]), 2026, <https://github.com/TimoKellerMath/PointCountsAbelianVarieties>.
- **[DH98]** S. A. DiPippo and E. W. Howe, *Real polynomials with all roots on the unit circle and abelian varieties over finite fields*, J. Number Theory **73** (1998), no. 2, 426–450.
- **[HW08]** G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, 6th ed., Oxford University Press, Oxford, 2008.
- **[Hon68]** T. Honda, *Isogeny classes of abelian varieties over finite fields*, J. Math. Soc. Japan **20** (1968), 83–95.
- **[How95]** E. W. Howe, *Principally polarized ordinary abelian varieties over finite fields*, Trans. Amer. Math. Soc. **347** (1995), no. 7, 2361–2401.
- **[Tat66]** J. Tate, *Endomorphisms of abelian varieties over finite fields*, Invent. Math. **2** (1966), 134–144.
- **[Tat71]** J. Tate, *Classes d'isogénie des variétés abéliennes sur un corps fini (d'après T. Honda)*, Séminaire Bourbaki, Vol. 1968/69, Exp. No. 352, Lecture Notes in Math., vol. 175, Springer, Berlin, 1971, pp. 95–110.
- **[Wat69]** W. C. Waterhouse, *Abelian varieties over finite fields*, Ann. Sci. École Norm. Sup. (4) **2** (1969), 521–560.
