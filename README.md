# Real measurements and sharp pairing in the five-level Hardy ladder

**Research draft for a Palomar entry, November 23, 2026.**

**For every complex terminal two-plane on five Schmidt coordinates, two real terminal two-planes can be chosen once and used for every positive spectrum.** They preserve all five diagonal entries of the original projection. For each spectrum the two real success probabilities bracket the complex one. Either real plane may give the larger value as the spectrum varies. Thus real measurements attain the optimum at each fixed spectrum. The general five-level plastic-constant bound remains open.

**An exact five-level maximum.** For Schmidt coefficients proportional to $(s,2,3,4,5)$, with $0<s\le2$, the optimal measurement uses the pairs $(2,4)$ and $(3,5)$. Its success is
$$
  P_{\max}(s)=\frac{(20/11)^2+(1020/421)^2}{54+s^2}.
$$
At $s=1$ this is exactly $39356960/235907771$, or **16.6832%**. The five diagonal entries of the measurement projection are free in this result.

## The physical objective

Use the ideal ladder with three binary settings per party and five forbidden events of exactly zero probability. Write $D=\operatorname{diag}(d_1,\ldots,d_5)>0$ and let $X$ be a complex matrix with two orthonormal columns. For terminal plane $U=\mathrm{im}(X)$, the maximal success compatible with the five zeros is
$$
 \frac{F(D,X)}{\sum_i d_i^2},\qquad
 F(D,X)=\|(I-P_{D^5 U})DX\|_{\mathrm{HS}}^2
       =T_2-\operatorname{tr}(A_{10}^{-1} A_6^2),\qquad
 A_k=X^* D^k X,\quad T_k=\operatorname{tr} A_k .
$$
Indeed the projection onto $D^5 U$ has matrix $D^5X A_{10}^{-1} X^*D^5$. Given a real terminal plane, the usual construction of the other five subspaces uses just powers of the real diagonal $D$ and orthogonal complements, so all six measurements can be real. The earlier Hardy reduction also deals with binary effects and exchanges ranks two and three by the score-preserving involution $U\mapsto(D^5 U)^\perp$. For rank one the optimum is attained on two real coordinates, and rank four follows by the same involution. Ranks zero and five give zero. The assertion about preserving the five projection entries applies to the rank-two construction. [Five-zero reduction](https://github.com/stalex444/pdt-hardy-ladder-higher-dimensions/blob/c9946d77c639d89bee866ae19a47f3f5bc0fcb7f/PROOF.md#the-five-zero-conditions) · [Four-level predecessor](https://github.com/stalex444/pdt-hardy-ladder-higher-dimensions/blob/c9946d77c639d89bee866ae19a47f3f5bc0fcb7f/README.md)

## Proof at fixed diagonal entries

For row $(a_i,b_i)$ of $X$, set
$$
 p_i=|a_i|^2+|b_i|^2,\qquad
 v_i=(2\Re(\bar a_i b_i),\ 2\Im(\bar a_i b_i),\ |a_i|^2-|b_i|^2).
$$
These satisfy $\|v_i\|=p_i$, $\sum_i p_i=2$, and $\sum_i v_i=0$. Also $p_i=(P_U)_{ii}$. Conversely any such data give an orthonormal frame. In fact the row outer product is recovered from $v_i=(x_i,y_i,z_i)$ as
$$
 M_i=\tfrac12\begin{pmatrix}p_i+z_i&x_i+iy_i\\x_i-iy_i&p_i-z_i\end{pmatrix}.
$$
It has eigenvalues $p_i,0$ and the blocks sum to the identity. Factor each block as the outer product of a row with itself, using a zero row when $p_i=0$. A common orthogonal change of coordinates on the vectors preserves their Gram matrix and these constraints. If the vectors span at most a two-dimensional linear space, place them in the $xz$-plane. All blocks then have real factors.

Let $G_{ij}=v_i\cdot v_j$, $B_k=\sum_i d_i^k v_i$ and $T_k=\sum_i d_i^k p_i$. The determinant and mixed adjugate trace in these coordinates are
$$
 J_k=\det A_k=(T_k^2-B_k\cdot B_k)/4,\qquad
 C=\operatorname{tr}(\operatorname{adj}(A_{10})A_6)
    =(T_{10}T_6-B_{10}\cdot B_6)/2 .
$$
By the two-by-two Cayley–Hamilton identity,
$$
 F=N/J_{10},\qquad
 N=T_2J_{10}-T_6 C+T_{10}J_6 .
$$
At fixed $p_i,d_i$ each $T_k$ is constant. Every dot product $B_k\cdot B_l$ is linear in $G$. Thus both $N$ and $J_{10}$ are affine in $G$, and the latter is positive because $A_{10}\succeq \min_i d_i^{10} I$.

It remains to split a spatial configuration into two planar ones. If the vectors already span a plane or line, take two copies of its real representative. Otherwise they span $\mathbb R^3$. Real symmetric three-by-three matrices have six independent entries. The five homogeneous equations $v_i^T Q v_i=0$ therefore admit a nonzero symmetric solution $Q$. Both signs occur in its spectrum. A semidefinite solution would have every spanning vector in its kernel.

Write $a=\lambda_{\min}(Q)<0<b=\lambda_{\max}(Q)$. Define
$$
 L=I-Q/b,\qquad R=I-Q/a,\qquad \theta=b/(b-a).
$$
Both matrices are positive semidefinite and singular, and $I=\theta L+(1-\theta)R$ with $0<\theta<1$. The two families $L^{1/2}v_i$ and $R^{1/2}v_i$ are centered, retain each length $p_i$, and span at most a plane. Their Gram matrices satisfy $G=\theta G_L+(1-\theta)G_R$. Reconstruct two real frames as above. Their construction used only the original frame. The Schmidt coefficients have been free throughout the construction. Affineness of numerator and denominator gives
$$
 F(G)=\frac{\theta J_{10}(G_L)F(G_L)+(1-\theta)J_{10}(G_R)F(G_R)}
 {\theta J_{10}(G_L)+(1-\theta)J_{10}(G_R)} .
$$
This is a weighted average with positive weights. The two real scores bracket the original one. Compactness of the frame space and continuity give actual maxima, also on each nonempty fixed-diagonal slice.

## A five-level family with a sharp optimum

Set $d=(s,2,3,4,5)$ with $0<s\le2$. Let the two terminal outcome spaces have orthonormal bases $a_i,b_j$. The five forbidden events imply $\langle D^5 a_i,b_j\rangle=0$. Their unnormalized endpoint score is $\sum_{ij}|\langle Da_i,b_j\rangle|^2$. Conversely, for a fixed first endpoint one can choose the other settings by the maximal construction above and take the other endpoint to be any subspace orthogonal to its fifth-power image. This links the endpoint maximum to the physical experiment.

Since $D$ is invertible the two endpoint ranks sum to at most five. After interchanging parties one rank is at most two. For rank two, take an orthonormal basis on that side whose first vector has zero component on the coordinate of coefficient 5. For every unit vector $u$ in this basis and real $t$, orthogonality and Bessel's inequality give
$$
 \sum_j |\langle D u,b_j\rangle|^2
 =\sum_j|\langle (D-tD^5)u,b_j\rangle|^2
 \le \max_{i\in\mathrm{supp}(u)} |d_i-td_i^5|^2.
$$
On the first vector use $t=1/176$. The largest absolute residual on $(s,2,3,4)$ is $20/11$, attained with opposite signs at 2 and 4. On the other vector use $t=1/421$. The largest absolute residual on all five coordinates is $1020/421$, attained with opposite signs at 3 and 5. On $[0,2]$ both residual polynomials $s-s^5/176$ and $s-s^5/421$ are nonnegative and increasing. This verifies the bounds for every allowed fifth value. Direct substitution verifies the other coordinates. A rank-one endpoint needs only the second bound. A zero-dimensional endpoint gives zero.

For attainment, on a pair of coefficients $(x,y)$ take real unit vectors proportional to $(\sqrt{y^5},\sqrt{x^5})$ and $(\sqrt{y^5},-\sqrt{x^5})$ for the two parties. They are orthogonal after applying $D^5$ to the first, and their amplitude with $D$ between them is $(xy^5-yx^5)/(x^5+y^5)$. Use both disjoint pairs $(2,4),(3,5)$. The two squared amplitudes attain the upper bound simultaneously. Dividing by $54+s^2$ gives the claimed maximum. At full Schmidt rank five the extra level contributes to normalization even though an optimal measurement omits it. The general deletion estimate adapts an earlier argument in the PDT canon. [Five-level upper bound and witnesses](HardySpectator.lean) · [Coordinate-deletion lemma](HardySpectator.lean#L139)

The upper endpoint of the interval has a physical consequence. For $s$ just above 2, measuring on $(s,4)$ in place of $(2,4)$ strictly beats the preceding formula. Its signed pair amplitude is $h(s)=(1024s-4s^5)/(1024+s^5)$. Here $h(2)=20/11$ and $h'(2)=64/121>0$. Both strategies have the same normalization at each value of $s$. The check script also compares them exactly at $s=9/4$.

## An exact semidefinite test on each fixed slice

For a feasible vector of row weights $p$, consider the compact spectrahedron
$$
 \mathcal E(p)=\{G=G^T\succeq0:\ G\mathbf 1=0,\ G_{ii}=p_i^2\}.
$$
Dropping the dimension constraint could allow Gram matrices of rank four. Nevertheless **every extreme point has rank at most two**. For a rank-$r$ Gram matrix, take spanning factor vectors in $\mathbb R^r$. If $r\ge3$, there are more than five entries in a symmetric form, so a nonzero form vanishes on all five vector squares. The same singular endpoint argument splits the matrix into two distinct feasible Gram matrices. Distinctness follows from the spanning condition. Thus the extreme point is realized by a real frame. This is the fixed-diagonal semidefinite rank argument specialized to the centered slice. [Li and Tam, Extreme correlation matrices](https://doi.org/10.1137/S0895479892240683) · [Pataki, Ranks of extreme matrices in semidefinite programs](https://doi.org/10.1287/moor.23.2.339)

For any Gram factor of a feasible matrix, centering implies $\|B_{10}\|=\|\sum_i(d_i^{10}-m)v_i\|\le T_{10}-2m$ with $m=\min_i d_i^{10}>0$. Hence $J_{10}>0$ throughout the relaxation. For any unnormalized target $K$, the bound on the entire slice holds exactly when the following linear semidefinite program has nonpositive optimum:
$$
 \max_{G\in\mathcal E(p)}\big[N(G)-K J_{10}(G)\big].
$$
Indeed an affine objective attains a maximum at an extreme point and every such point is physical. The coefficients depend on $p,d$, which must still be handled uniformly for a five-level ceiling.

## Exact example, numerical checks and next inequality

For $d=(1,2,3,4,5)$ and $p=(6,5,5,8,8)/16$, take the five vectors
$$
 (6,0,6),\ (-3,4,5),\ (-3,-4,5),\ (0,8,-8),\ (0,-8,-8)
$$
divided by $16\sqrt 2$. They are centered, span three dimensions, and satisfy $x^2+y^2-z^2=0$. The two singular endpoint metrics are $\operatorname{diag}(0,0,2)$ and $\operatorname{diag}(2,2,0)$. The exact normalized scores are

| Plane | Hardy probability |
|---|---:|
| Original complex plane | $96579479142279/1509744123870004$ |
| Real plane from the first metric | $12257774865/183471096556$ |
| Real plane from the second metric | $463799782471725/7262872650915772$ |

In percentages these scores are 6.3971%, 6.6810% and 6.3859%, respectively. The original is strictly between the real scores. A seeded test reconstructs both frames in 300 cases and checks their Gram decomposition, projection diagonals, column orthonormality, the five forbidden Born probabilities, and their agreement with the moment formula. The largest discrepancy was $1.65\times10^{-13}$.

The same 300 pairs of real frames were each tested again on three fresh spectra. The largest bracketing discrepancy in those 900 comparisons was $3.05\times10^{-16}$.

### A strict certificate for every plane in this example's slice

Every complex two-plane with the stated five projection entries on spectrum proportional to $(1,2,3,4,5)$ has success probability **strictly below 7%**. This covers the entire continuous slice, including real planes other than the two displayed above.

For the certificate put $d_i=i/5$, $K=(7/100)\sum_i d_i^2$. Centering gives $G=BHB^T$, with $B$ obtained by adjoining the row $-\mathbf1^T$ below the four-by-four identity, $H\succeq0$, $H_{ii}=p_i^2$ and $\mathbf1^T H\mathbf1=p_5^2$. Write $u=B^T(d_i^{10})_i$ and $v=B^T(d_i^6)_i$. Directly from the moments above,
$$
 4(N-KJ_{10})=c+\operatorname{tr}(MH),\qquad
 c=(T_2-K)T_{10}^2-T_{10}T_6^2,
$$
$$
 M=-(T_2-K)uu^T+T_6(uv^T+vu^T)-T_{10}vv^T.
$$
Use multipliers $y=(3878,4479,3695,-9419,-107404)/10^6$. The four leading principal minors of $S=\operatorname{diag}(y_1,\ldots,y_4)+y_5\mathbf1\mathbf1^T-M$ are strictly positive, by exact rational arithmetic. Since $\operatorname{tr}(SH)\ge0$,
$$
 4(N-KJ_{10})\le c+\sum_i y_i p_i^2
 =-\frac{2306584670414281}{97656250000000000000}<0 .
$$
The determinant test and the rational upper bound can be replayed using just the Python standard library. On a general slice, the same inequality with a suitable choice of multipliers is a sufficient certificate. [Exact certificate](check_slice_certificate.py)

### The open pairing inequality

Write $E_{ij}=((d_i d_j^5-d_j d_i^5)/(d_i^5+d_j^5))^2$. There are 15 ways to choose two disjoint pairs among five coordinates. Each matching yields a real strategy with unnormalized success $E_{ij}+E_{kl}$. The open fixed-spectrum conjecture asks whether the largest of these fifteen numbers, $K_{\mathrm{pair}}(d)$, bounds every real two-plane. On 128 local searches across 16 spectra, the largest observed positive excess over that value was $5.55\times10^{-17}$. These are exploratory searches. A proof of just the plastic ceiling only requires the weaker uniform upper bound with $K=p_*\sum_i d_i^2$, where $p_*=(8\rho^2+\rho-11)/25$ and $\rho>1$ solves $\rho^3=\rho+1$. The semidefinite test identifies a concrete route to certificates for either inequality. [Four-level matching theorem](https://github.com/stalex444/pdt-hardy-ladder-higher-dimensions/blob/c9946d77c639d89bee866ae19a47f3f5bc0fcb7f/PROOF.md)

The same row-count argument stops at six. For example, the centered six vectors $e_1,e_2,e_3,(1,1,0),(1,0,1),(-3,-2,-2)$ force every symmetric form with zero evaluations to vanish. The first three rows eliminate the diagonal entries, the next two eliminate the first two off-diagonal entries, and the last eliminates the third. A common scaling makes their lengths sum to two. This example locates the limit of the rank argument. Whether complex measurements improve the Hardy optimum at six is a separate question.

## Formal verification and replay

The first two challenge statements quantify over all centered configurations and all orthonormal complex five-by-two frames, respectively. The second uses the three actual compressions of the given frame and a matrix inverse. The existential quantifiers for the two real frames precede the universal quantifier for the Schmidt spectrum. The third challenge statement proves the greatest normalized success over all admissible endpoint ranks for the entire family $(s,2,3,4,5)$, including an attaining witness. From the endpoint reduction the written proof recovers the maximal five-zero measurement strategy using the earlier subspace reduction. The semidefinite formulation and rational slice certificate are supplied separately from the Lean targets. [Challenge](Challenge.lean) · [Solution](Solution.lean) · [Gram decomposition](HardyFive.lean) · [Frame construction](HardyFrames.lean) · [Matrix score](HardyScore.lean)

The solution builds with the pinned Lean toolchain and Mathlib revision. All three declarations use only propositional extensionality, classical choice, and the quotient soundness axiom. The local comparator accepted all three statements with Nanoda and Lean's default kernel. The macOS replay used the comparator's unsandboxed mode. The public preflight results are available in the [repository’s Actions history](https://github.com/stalex444/pdt-five-level-hardy-ladder/actions).

From the package root, with the pinned toolchain and its dependencies installed:

```sh
lake build
PATH="$(lean --print-prefix)/bin:$PATH" lake comparator
python3 check_slice_certificate.py
python3 check_five.py
```

On macOS, append `--inadvisably-no-sandbox` to the comparator command for a local kernel replay. The last numerical script needs NumPy and SciPy. The only three proof placeholders occur in the separate challenge specification.

The semidefinite rank principle is classical. The proposed contribution is its application to the rank-two Hardy objective with fixed coordinate weights, including common real endpoints for every spectrum, together with the sharp five-level pairing family and the checked formal proofs. A priority determination would require further review. Chen, Mal, Tabia and Liang compare numerical bounds for the three-setting binary Hardy ladder in Table I(a). [Chen et al.](https://arxiv.org/pdf/2311.02045)
