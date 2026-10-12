# The Coloured Sand Theorem: the $p$-part of the sandpile group of the Hamming graph

Rafael Amichis Luengo · Madrid, Spain · tretoef@gmail.com · 13 October 2026 · version 1 · doi:10.5281/zenodo.23327609

**Abstract.** 
Let $H(d,q)=K_q^{\,d}$ be the Hamming graph and $K(H(d,q))$ its sandpile group (critical group). For primes $p\nmid q$ its $p$-part was determined by Jacobson, Niedermaier and Reiner in 2003, who called the remaining primes difficult, "due to bad behavior of its $p$-primary structure". We treat the primes $p\mid q$. Jacobson, Niedermaier and Reiner showed that over $\mathbb{Z}$ the Laplacian splits into explicit triangular pieces; we read these pieces as operators $q(c+H)+U$ on the Boolean lattice (A). From this we prove: (B) a closed formula for the Sylow $p$-subgroup for every prime $p>d$ and every $q$ divisible by $p$, in which ballot numbers appear; (C) the exponent of the Sylow $p$-subgroup for every prime $p$ and every $q\ge3$, namely $p^{\max_{1\le s\le d}(e s+v_p(s))}$ with $e=v_p(q)\ge1$; (D) the number of its cyclic factors when $p\mid q$, from Wilson's diagonal form of inclusion matrices. For $p\le d\le 2p-2$ we state a conjecture, the Glue Conjecture, which describes the group exactly; it was found from the cases $p=3,5$ and then predicted, before they were computed, $44$ further cases, all correctly.

## Introduction


For a connected graph $\Gamma$ with Laplacian $L(\Gamma)$, the sandpile group $K(\Gamma)$ is the torsion subgroup of $\operatorname{coker} L(\Gamma)$, and $\operatorname{coker} L(\Gamma)\cong\mathbb{Z}\oplus K(\Gamma)$; its order is the number of spanning trees [Big99]. The Hamming graph $H(d,q)$ has vertex set $(\mathbb{Z}/q)^d$, two vertices being adjacent when they differ in exactly one coordinate; it is the Cartesian power $K_q^{\,d}$ of the complete graph. Its Laplacian eigenvalues are $qs$, $0\le s\le d$, with multiplicity $\binom ds(q-1)^s$.

Jacobson, Niedermaier and Reiner [JNR03] determined the Sylow $p$-subgroup of $K(K_{n_1}\times\cdots\times K_{n_k})$ for every prime $p$ that divides none of the $n_i$ [JNR03, Theorem 2], and bounded the number of invariant factors [JNR03, Theorem 3]. About the other primes they wrote: "Describing the exact structure of the critical group $K(K_{n_1}\times\cdots\times K_{n_k})$ appears to be difficult, due to bad behavior of its $p$-primary structure for primes $p$ that divide some of $n_1,\dots,n_k$." Ducey and Jalil [DJ14] recovered the results of [JNR03] by another method. For $q=2$ the graph is the hypercube; its odd part is due to Bai [Bai03] and its $2$-part was determined in [DST].

In this paper $q\ge2$ is arbitrary, $p$ is a prime dividing $q$, and $e:=v_p(q)\ge1$, except where we say otherwise.


### The pieces

Let $B_m$ be the free abelian group on the subsets of $[m]=\{1,\dots,m\}$, graded by size: $B_m=\bigoplus_{s=0}^m B_m(s)$. Let $H$ act on $B_m(s)$ as the scalar $s$, and let $U$ and $D$ be the up and down operators,
$$
U(S)=\sum_{x\notin S}S\cup\{x\},\qquad D(S)=\sum_{x\in S}S\setminus\{x\}.
$$
For integers $c\ge0$ put
$$
X_q(m,c):=\operatorname{coker}\big(q(c+H)+U\ \text{ on } B_m\big).
$$
It is finite when $c\ge1$; for $c=0$ it is $\mathbb{Z}$ plus a finite group.


**Theorem A** (Jacobson–Niedermaier–Reiner [JNR03, Theorem 13]).
For every $q\ge2$ and $d\ge1$, as abelian groups,
$$
\operatorname{coker} L\big(H(d,q)\big)\;\cong\;\bigoplus_{j=0}^{d} X_q(d-j,\,j)^{\oplus\binom dj (q-2)^j}.
$$

This is the case $n_1=\dots=n_d=q$ of [JNR03, Theorem 13]: there the pieces are upper triangular matrices $M(N;n_S)$ of size $2^{|S|}$ with identity blocks above the diagonal, and after reversing the order of the subsets of $S$ they are the matrices $q(c+H)+U$. We include the short proof below, in the form we use. For $q=2$ only $j=0$ survives and the theorem says $\operatorname{coker} L(Q_d)\cong X_2(d,0)$, the starting point of [DST].


**Theorem B** (the primes $p>d$). 
Let $d\ge1$, let $p>d$ be a prime dividing $q$, and $e=v_p(q)$. Then
$$
\operatorname{Syl}_p K\big(H(d,q)\big)\;\cong\;\bigoplus_{v=1}^{d}\big(\mathbb{Z}/p^{ev}\big)^{n_v},\qquad
n_v=\sum_{\substack{j+2k=d+1-v\\ (j,k)\neq(0,0)}}\binom{d}{j}\,(q-2)^{j}\,b(k,v),
$$
the sum over integers $j,k\ge0$, where $b(k,v)=\frac{v}{v+2k}\binom{v+2k}{k}=[x^k]\,C(x)^v$ are the ballot numbers and $C(x)=\sum_n\frac1{n+1}\binom{2n}nx^n$ is the Catalan series.

Equivalently, with $c(z)=C(z^2)$ and $u=q-2$, $\sum_v n_v y^v=[z^{d+1}]\,(1+uz)^d\,\frac{yz\,c(z)}{1-yz\,c(z)}-y^{d+1}$. For instance, with $u=q-2$:
$$\begin{aligned}
d=2:&\quad (\mathbb{Z}/p^{e})^{u^2+1}\oplus(\mathbb{Z}/p^{2e})^{2u},\\
d=3:&\quad (\mathbb{Z}/p^{e})^{u^3+3u}\oplus(\mathbb{Z}/p^{2e})^{3u^2+2}\oplus(\mathbb{Z}/p^{3e})^{3u},\\
d=4:&\quad (\mathbb{Z}/p^{e})^{u^4+6u^2+2}\oplus(\mathbb{Z}/p^{2e})^{4u^3+8u}\oplus(\mathbb{Z}/p^{3e})^{6u^2+3}\oplus(\mathbb{Z}/p^{4e})^{4u}.
\end{aligned}$$
Theorem B is the case $m<p$ of a statement about single pieces (Theorem E in Section 3), which also gives, for every prime $p$, the contribution of all pieces with $d-j<p$.


**Theorem C** (the exponent). 
Let $q\ge3$, let $p$ be any prime and $e=v_p(q)$. The exponent of $\operatorname{Syl}_p K(H(d,q))$ is $p^{E}$, where
$$
E=\max_{1\le s\le d}\big(e\,s+v_p(s)\big)\quad\text{if } e\ge1,\qquad E=\lfloor\log_p d\rfloor\quad\text{if } e=0 .
$$

For $p>d$ this gives $E=ed$, as in Theorem B. For $p\le d$ the maximum need not be at $s=d$: for $q=3$ and $d=10$ it is at $s=9$ and $E=11$.


**Theorem D** (the number of cyclic factors). 
Let $p\mid q$. The number of cyclic factors of $\operatorname{Syl}_p K(H(d,q))$ is
$$
N=\sum_{j=0}^{d}\binom dj(q-2)^j\Big(2^{\,d-j}-\rho_p(d-j)\Big)\;-\;1,\qquad \rho_p(m)=\sum_{s=0}^{m-1}r_p(m,s),
$$
where $r_p(m,s)=\sum_{i}\big(\binom mi-\binom m{i-1}\big)$, the sum over $0\le i\le t$ with $p\nmid k-i$, and $(t,k)=(s,s+1)$ if $2s\le m-1$, $(t,k)=(m-1-s,m-s)$ otherwise.

Here $\rho_p(m)$ is the rank over $\mathbb{F}_p$ of $U$ on $B_m$. For $q=p=3$ the theorem gives $N=1,4,12,34,96,274,\dots$, and one checks from the formula that $N=3^{d-1}+2^{d-1}-1$ for $d\le 40$ (we have not proved this closed form in general). For $q=p$ the value of $N$ equals the bound $\frac12(q^d+(q-2)^d)-1$ of [JNR03, Theorem 3] for $d\le2$, is one less for $d=3$, and is strictly smaller for $4\le d\le8$ and $p\le11$ (where we compared).


**Corollary 1**. 
$\operatorname{Syl}_p K(H(d,q))$ depends on $q$ only through $e=v_p(q)$ and the multiplicities $\binom dj(q-2)^j$.

### Status
 This is a preprint. The proofs of Theorems B–D and E were re-read once by the system that wrote them (see Provenance) and checked against the computations of Section 7; they have not yet been read by an independent reader. Conjecture F is supported by computation only.

What remains is the range $d\ge p$, and there only the pieces $X_q(m,c)$ with $m\ge p$ (Theorem E). For $m\le 2p-2$ we state a precise conjecture in Section 6, with its evidence; beyond that range we leave the question open.


## The splitting (after Jacobson, Niedermaier and Reiner)

*Proof of Theorem A.* 
Let $K_q=qI-J$ be the Laplacian of the complete graph $K_q$, acting on $\mathbb{Z}^q$ with basis $e_0,\dots,e_{q-1}$, and put $f_i=e_i-e_0$ ($1\le i\le q-1$) and $\sigma=f_1+\cdots+f_{q-1}$. Then $e_0,\sigma,f_1,\dots,f_{q-2}$ is a basis of $\mathbb{Z}^q$ (unimodular change from $e_0,f_1,\dots,f_{q-1}$), and
$$
K_qe_0=-\sigma,\qquad K_q\sigma=q\sigma,\qquad K_qf_i=qf_i .
$$
So $\mathbb{Z}^q=A\oplus W$ with $A=\mathbb{Z} e_0\oplus\mathbb{Z}\sigma$ and $W=\bigoplus_{i\le q-2}\mathbb{Z} f_i$, both stable under $K_q$, and $K_q$ is the scalar $q$ on $W$. The Laplacian of $H(d,q)$ is $L=\sum_{i=1}^d 1\otimes\cdots\otimes K_q\otimes\cdots\otimes1$ on $(\mathbb{Z}^q)^{\otimes d}=\bigoplus_{T\subseteq[d]}A^{\otimes([d]\setminus T)}\otimes W^{\otimes T}$, and each summand is $L$-stable. On the summand of $T$ with $|T|=j$, $L$ acts as $(L_A+qj)\otimes1$, where $L_A=\sum_i K_q^{(i)}$ on $A^{\otimes(d-j)}$ and $W^{\otimes T}\cong\mathbb{Z}^{(q-2)^j}$. There are $\binom dj$ sets $T$ of size $j$.

Index the basis of $A^{\otimes m}$ by the subsets $S\subseteq[m]$, the factor in position $i$ being $\sigma$ if $i\in S$ and $e_0$ otherwise. Then $L_A(S)=q|S|\,S-\sum_{x\notin S}S\cup\{x\}$, that is, $L_A=qH-U$, and $L_A+qj=q(j+H)-U$. Conjugating by the diagonal matrix $(-1)^{|S|}$ turns $-U$ into $U$. Hence the summand contributes $\operatorname{coker}(q(j+H)+U\text{ on }B_{d-j})=X_q(d-j,j)$, $\binom dj(q-2)^j$ times.
 ∎

*Proof of Corollary 1.* 
By Theorem A it suffices to see that $\operatorname{Syl}_p X_q(m,c)$ depends only on the $p$-adic valuations of the diagonal entries $a_s=q(c+s)$. This is Lemma 2.
 ∎

**Lemma 2** (only the valuations matter). 
Let $a_0,\dots,a_m$ be elements of $\mathbb{Z}_{(p)}$ and $M=\operatorname{diag}(a_{|S|})+U$ on $B_m\otimes\mathbb{Z}_{(p)}$. If $a_s=p^{w_s}u_s$ with units $u_s$ (or $a_s=0$, with $u_s=1$), then $M$ is equivalent over $\mathbb{Z}_{(p)}$ to
$$\operatorname{diag}(p^{w_{|S|}})+U\qquad(\text{with } p^{w}:=0 \text{ when } a_s=0).$$

*Proof.* 
Look for units $\lambda_s,\mu_s$ such that $P=\operatorname{diag}(\lambda_{|S|})$ and $Q=\operatorname{diag}(\mu_{|S|})$ give $PMQ=\operatorname{diag}(p^{w_{|S|}})+U$. The diagonal of $PMQ$ on rank $s$ is $\lambda_s a_s\mu_s$ and its block from rank $s$ to rank $s+1$ is $\lambda_{s+1}\mu_s U$, so we need $\lambda_s\mu_su_s=1$ and $\lambda_{s+1}\mu_s=1$. Put $\mu_0=1$, $\lambda_0=u_0^{-1}$, and recursively $\lambda_{s+1}=\mu_s^{-1}$, $\mu_{s+1}=(\lambda_{s+1}u_{s+1})^{-1}$.
 ∎

## Strings, and the primes $p>m$


On $B_m$ one has $[D,U]=m-2H$: on a set $S$ of size $s$, $DU(S)=(m-s)S+\Sigma$ and $UD(S)=s\,S+\Sigma$ with the same sum $\Sigma=\sum_{y\in S,\,x\notin S}(S\setminus\{y\})\cup\{x\}$. For $0\le k\le m/2$ let $\Lambda_k=\ker D\cap B_m(k)$. By induction on $i$, for $v\in\Lambda_k$,
$$
D\,U^iv=i\,(m-2k-i+1)\,U^{i-1}v .
\tag{1}$$
Over $\mathbb{Q}$ this is the classical $\mathfrak{sl}_2$-structure of the Boolean lattice [Pro82]:
$$B_m\otimes\mathbb{Q}=\bigoplus_{k\le m/2}\ \bigoplus_{i=0}^{m-2k}U^i\Lambda_k^{\mathbb{Q}},$$
$\dim\Lambda^{\mathbb{Q}}_k=\binom mk-\binom m{k-1}$, and $U^{m-2k+1}\Lambda_k=0$. We call $\Lambda_k,U\Lambda_k,\dots,U^{m-2k}\Lambda_k$ a *string*; its ranks are $k,\dots,m-k$ and its length is $m-2k+1$.


**Lemma 3** (strings over $\mathbb{Z}_{(p)}$). 
If $p>m$, then $B_m\otimes\mathbb{Z}_{(p)}=\bigoplus_{k\le m/2}\bigoplus_{i=0}^{m-2k}U^i\Lambda_k$, each $\Lambda_k$ is free of rank $\binom mk-\binom m{k-1}$, and $U^i\colon\Lambda_k\to U^i\Lambda_k$ is an isomorphism for $i\le m-2k$.

*Proof.* 
All lattices below are over $R=\mathbb{Z}_{(p)}$. First, for $r\le m/2$ we show $B_m(r)=U B_m(r-1)\oplus\Lambda_r$, by induction on $r$ (for $r=0$, $\Lambda_0=B_m(0)$). By induction $B_m(r-1)=\bigoplus_{k<r}U^{r-1-k}\Lambda_k$, and by (1) the operator $DU$ acts on $U^{r-1-k}\Lambda_k$ as the scalar $(r-k)(m-k-r+1)$; both factors lie in $[1,m]$, so they are units. Hence $DU$ is invertible on $B_m(r-1)$, $\pi=U(DU)^{-1}D$ is an idempotent on $B_m(r)$ with image $UB_m(r-1)$, and its kernel is $\ker D\cap B_m(r)=\Lambda_r$ because $U(DU)^{-1}$ is injective. This gives the decomposition, and $\Lambda_r$ is a direct summand, so free, of rank $\binom mr-\binom m{r-1}$.

Now fix any rank $r$ and consider $\Phi\colon\bigoplus_{k\le\min(r,m-r)}\Lambda_k\to B_m(r)$, $(v_k)\mapsto\sum_kU^{r-k}v_k$. For $k'\le r$ let $\psi_{k'}\colon B_m(r)\to\Lambda_{k'}$ be $D^{r-k'}$ followed by the projection of $B_m(k')=UB_m(k'-1)\oplus\Lambda_{k'}$ onto $\Lambda_{k'}$. By (1), $D^{r-k'}U^{r-k}v_k$ is $0$ if $k>k'$ (since $Dv_k=0$), lies in $U^{k'-k}\Lambda_k\subseteq UB_m(k'-1)$ if $k<k'$, and equals $\prod_{i=1}^{r-k}i(m-2k-i+1)\,v_k$ if $k=k'$, a unit multiple of $v_k$ (all factors lie in $[1,m]$ because $k\le m-r$). So $(\psi_{k'})\circ\Phi$ is triangular with unit diagonal, $\Phi$ is split injective, and its image is a direct summand of $B_m(r)$ of full rank (compare ranks over $\mathbb{Q}$). Hence $\Phi$ is an isomorphism. Finally $U^{m-2k+1}\Lambda_k=0$ holds over $\mathbb{Q}$, hence over $R$.
 ∎


Each string is stable under $q(c+H)+U$: in the basis $v,Uv,\dots,U^{\ell-1}v$ ($\ell=m-2k+1$) the operator is lower bidiagonal with diagonal entries $q(c+k+i)$, $0\le i<\ell$, and all subdiagonal entries $1$. The cokernel of such a matrix over a principal ideal domain is cyclic of order its determinant, because the minor obtained by deleting the first row and last column equals $1$; if one diagonal entry is $0$ (only possible for $c=k=i=0$) the cokernel is $\mathbb{Z}_{(p)}$. This proves:


**Theorem E** (pieces with $m<p$). 
Let $p$ be any prime, $e=v_p(q)$, and $m<p$. Then
$$
\operatorname{Syl}_p X_q(m,c)\;\cong\;\bigoplus_{\substack{0\le k\le m/2\\(c,k)\ne(0,0)}}\big(\mathbb{Z}/p^{A_k}\big)^{\binom mk-\binom m{k-1}},\qquad A_k=\sum_{r=k}^{m-k}\big(e+v_p(c+r)\big),
$$
and for $c=0$ the string $k=0$ contributes only the free summand $\mathbb{Z}$.

*Proof of Theorem B.* 
If $p>d$, every piece $X_q(d-j,j)$ has $m=d-j<p$ and $c+r\le d<p$, so $v_p(c+r)=0$ for $c+r\ge1$ and $A_k=e(m-2k+1)$. Put $v=m-2k+1=d+1-j-2k$; then $\binom mk-\binom m{k-1}=\binom{v+2k-1}{k}-\binom{v+2k-1}{k-1}=\frac{v}{v+2k}\binom{v+2k}k=b(k,v)$. Summing over $j$ with Theorem A gives the formula. The generating function follows from $\sum_kb(k,v)x^k=C(x)^v$.
 ∎

## The exponent

**Lemma 4**. 
Let $c\ge1$ and $M=q(c+H)+U$ on $B_m$. Then $M$ is invertible over $\mathbb{Q}$, and for $S\subseteq T$ with $|S|=s$, $|T|=s+k$,
$$
(M^{-1})_{T,S}=(-1)^k\,k!\,\prod_{i=0}^{k}\frac1{q(c+s+i)},
$$
while $(M^{-1})_{T,S}=0$ if $S\not\subseteq T$.

*Proof.* 
With $\Delta=q(c+H)$, $M^{-1}=(1+\Delta^{-1}U)^{-1}\Delta^{-1}=\sum_{k\ge0}(-\Delta^{-1}U)^k\Delta^{-1}$, a finite sum. A path from $S$ to $T$ in $(\Delta^{-1}U)^k\Delta^{-1}$ is a maximal chain $S=S_0\subset\cdots\subset S_k=T$, there are $k!$ of them, and each collects $\Delta^{-1}$ once at every rank from $s$ to $s+k$.
 ∎


For a nonsingular square matrix over a discrete valuation ring with uniformizer $p$, the exponent of the cokernel is $p^{\epsilon}$ with $-\epsilon$ the least valuation of an entry of $M^{-1}$ (write $M$ in Smith form). Hence, for $c\ge1$, the exponent of $\operatorname{Syl}_pX_q(m,c)$ is $p$ to the power
$$
\max_{\substack{s,k\ge0\\ s+k\le m}}\Big(\sum_{i=0}^{k}\big(e+v_p(c+s+i)\big)-v_p(k!)\Big)
=\max_{c\le a\le b\le c+m}\Big(eL+v_p(L)+v_p\tbinom bL\Big),\quad L=b-a+1,
$$
where $a=c+s$, $b=c+s+k$, and we used $\frac{b!}{(a-1)!\,(b-a)!}=L\binom bL$.


**Lemma 5** (carries). 
For $d\ge1$ and $e\ge1$,
$$
\max_{1\le L\le b\le d}\Big(eL+v_p(L)+v_p\tbinom bL\Big)=\max_{1\le s\le d}\big(es+v_p(s)\big),
$$
and for $e=0$ the left side equals $\lfloor\log_p d\rfloor$.

*Proof.* 
Taking $L=b=s$ gives $\ge$. Let $\lambda=\lfloor\log_pb\rfloor$. By Kummer's theorem $v_p\binom bL$ is the number of carries in the addition $L+(b-L)$ in base $p$. No carry occurs at a position below $v_p(L)$, where the digits of $L$ vanish, and a carry out of position $i$ forces $b\ge p^{i+1}$, so $i\le\lambda-1$. Hence $v_p(L)+v_p\binom bL\le\lambda$. For $e=0$ this gives the bound $\lfloor\log_pd\rfloor$, attained at $L=b=p^{\lfloor\log_pd\rfloor}$.

Let $e\ge1$; we induct on $b$, the case $b=1$ being clear. Let $s^*=p^\lambda\lfloor b/p^\lambda\rfloor$, so $1\le s^*\le b<s^*+p^\lambda$ and $v_p(s^*)\ge\lambda$. If $L\le s^*$, then $eL+v_p(L)+v_p\binom bL\le es^*+\lambda\le es^*+v_p(s^*)$. If $L>s^*$, write $b=s^*+r$ and $L=s^*+r'$ with $1\le r'\le r<p^\lambda$. Then $v_p(L)=v_p(r')$, and since $(b-L)+r'=r<p^\lambda$, the additions $L+(b-L)$ and $r'+(r-r')$ have the same carries, so $v_p\binom bL=v_p\binom r{r'}$. By induction there is $1\le t\le r$ with $er'+v_p(r')+v_p\binom r{r'}\le et+v_p(t)$. Since $t<p^\lambda\le p^{v_p(s^*)}$, $v_p(s^*+t)=v_p(t)$, and so $eL+v_p(L)+v_p\binom bL\le e(s^*+t)+v_p(s^*+t)$ with $s^*+t\le b$.
 ∎

*Proof of Theorem C.* 
By Theorem A the exponent is the largest exponent of the pieces $\operatorname{Syl}_pX_q(d-j,j)$ that occur. For $j\ge1$ the piece occurs ($q\ge3$) and the computation above gives the maximum over $j\le a\le b\le d$; for $j=1$ this is the full range $1\le a\le b\le d$. For $j=0$, the row of the empty set in $M_0=qH+U$ is zero and $M_0$ maps into $B'=\bigoplus_{s\ge1}B_d(s)$, so
$$\operatorname{coker} M_0=\mathbb{Z}\oplus B'/(M"B'+\mathbb{Z} u),$$
where $M"$ is the restriction of $M_0$ to $B'$ (nonsingular, lower triangular by rank with diagonal $qs$) and $u=M_0(\emptyset)$. Its torsion is a quotient of $\operatorname{coker} M"$, whose exponent is given by Lemma 4 (with $c=0$ and $s\ge1$) as the same maximum over $1\le a\le b\le d$. So the exponent is $p$ to $\max_{1\le a\le b\le d}(eL+v_p(L)+v_p\binom bL)$, and Lemma 5 finishes.
 ∎


For $q=2$ the same argument gives only an upper bound, and it is not attained: for $Q_2$ the group is $\mathbb{Z}/4$ while the bound is $2^3$.


## The number of cyclic factors

*Proof of Theorem D.* 
The number of cyclic factors of $\operatorname{Syl}_p K$ is $\dim_{\mathbb{F}_p}(\operatorname{coker} L\otimes\mathbb{F}_p)-1$, the $1$ for the free summand. Modulo $p$, $q(j+H)+U\equiv U$, so by Theorem A $\dim_{\mathbb{F}_p}(\operatorname{coker} L\otimes\mathbb{F}_p)=\sum_j\binom dj(q-2)^j\big(2^{d-j}-\operatorname{rank}_{\mathbb{F}_p}U|_{B_{d-j}}\big)$. The rank of $U$ is the sum over $s$ of the ranks of the inclusion matrices $W_{s,s+1}$ of $s$-subsets versus $(s+1)$-subsets of $[m]$. By Wilson's diagonal form [Wil90], for $t\le\min(k,m-k)$ the matrix $W_{t,k}$ is equivalent over $\mathbb{Z}$ to a diagonal matrix with entries $\binom{k-i}{t-i}$ of multiplicity $\binom mi-\binom m{i-1}$, $0\le i\le t$ (we use the statement as given in [CSX15, (2)]); so its rank over $\mathbb{F}_p$ is $\sum_{i:\,p\nmid\binom{k-i}{t-i}}(\binom mi-\binom m{i-1})$. For $W_{s,s+1}$ with $2s\le m-1$ take $(t,k)=(s,s+1)$, so $\binom{k-i}{t-i}=s+1-i$; otherwise complementation identifies $W_{s,s+1}$ with the transpose of $W_{m-s-1,m-s}$ and we take $(t,k)=(m-1-s,m-s)$. This is $r_p(m,s)$.
 ∎

## The range $p\le d$: the Glue Conjecture


By Theorem E the only pieces not yet described are $X_q(m,c)$ with $m\ge p$. For $p\le m$ the strings of length $>p$ break: by (1) the coefficient $i(m-2k-i+1)$ vanishes modulo $p$. For $m\le 2p-2$ every broken string meets exactly one other string. In the language of the representations of $SL_2$ in characteristic $p$: $B_m\otimes\mathbb{F}_p=(\mathbb{F}_p^2)^{\otimes m}$ is a tilting module, and for $p\le\lambda\le2p-2$ the indecomposable tilting module $T(\lambda)$ has Weyl factors of highest weights $\lambda$ and $2p-2-\lambda$ [Don93; Jan03]. The conjecture says that the glue between these two strings moves exactly one factor $p$ from the long string to the short one.

For $\lambda\equiv m\pmod 2$, $0\le\lambda\le m$, write $\beta(m,\lambda)=\binom{m}{(m-\lambda)/2}-\binom m{(m-\lambda)/2-1}$ (the number of strings of length $\lambda+1$), and
$$
A_c(m,\lambda)=\sum_{r=(m-\lambda)/2}^{(m+\lambda)/2}\big(e+v_p(c+r)\big),
$$
the valuation of the determinant of $q(c+H)+U$ on one such string.


**Conjecture F** (the Glue Conjecture). 
Let $p$ be a prime, $q$ an integer with $e=v_p(q)\ge1$, $m\le2p-2$ and $c\ge0$. Then
$$
\begin{aligned}\operatorname{Syl}_pX_q(m,c)\;\cong\;&\bigoplus_{\lambda\le p-1}\big(\mathbb{Z}/p^{A_c(m,\lambda)}\big)^{\beta(m,\lambda)-\beta'(m,\lambda)}\\&\oplus\bigoplus_{p\le\lambda\le m}\Big(\mathbb{Z}/p^{A_c(m,\lambda)-1}\oplus\mathbb{Z}/p^{A_c(m,2p-2-\lambda)+1}\Big)^{\beta(m,\lambda)},\end{aligned}
$$
where $\beta'(m,\lambda)=\beta(m,2p-2-\lambda)$ if $\lambda\le p-2$ and $\beta'(m,p-1)=0$, and $\lambda$ runs over integers $\equiv m\pmod2$. When $c=0$ the string of length $m+1$ (through the empty set) has a zero on its diagonal: for $\lambda=m<p$ it gives nothing, and for $\lambda=m\ge p$ the term $\mathbb{Z}/p^{A_c(m,m)-1}$ is omitted (it is the free summand) while its partner $\mathbb{Z}/p^{A_0(m,2p-2-m)+1}$ stays.

For $m<p$ the conjecture is Theorem E. Together with Theorem A it determines $\operatorname{Syl}_pK(H(d,q))$ for every $d\le 2p-2$. The hypothesis $e\ge1$ is needed: for $p\nmid q$ the formula fails, for instance when $(q,p,d)=(4,3,4)$; there the answer of [JNR03] applies instead.


**Example 2**. 
For $p=q=3$ and $d=4$: Theorem A gives the pieces $X(4,0)$, $X(3,1)^4$, $X(2,2)^6$, $X(1,3)^4$, $X(0,4)$, and the conjecture gives $\operatorname{Syl}_3K(H(4,3))\cong(\mathbb{Z}/3)^2\oplus(\mathbb{Z}/3^2)^{7}\oplus(\mathbb{Z}/3^3)^{8}\oplus(\mathbb{Z}/3^4)^{17}$, which is the group we computed.

## Verification


All computations were exact. The Smith forms over $\mathbb{Z}_{(p)}$ were computed modulo $p^M$ with $p^M<2^{31}$, by unit pivots and Schur complements, level by level in the $p$-adic valuation; factors of valuation at least $M$ were then determined separately, by the matrix $p^E M^{-1}$ of Lemma 4, whose elementary divisors are $p^{E-a}$ for the divisors $p^a$ of $M$. The scripts, the sealed prediction files and the logs are at https://github.com/tretoef-estrella/coloured-sand-theorem and in the Zenodo record doi:10.5281/zenodo.23327609.

- Theorem A: the Sylow $p$-subgroups for $p\in\{2,3,5,7\}$ computed directly from the Laplacian and from the pieces agree in all $90$ comparisons ($27$ cells, $q\in\{3,\dots,10,12\}$, $q^d\le729$, including $p\mid q$ and $p\le d$); adding one extra copy of a piece changes the answer in $49$ of them. Independently, the cells $(d,q)=(3,7)$ and $(2,11)$ were recomputed with Sage from the full Laplacian.

- Theorem B: found first as a conjecture from the cells with $d\le4$; before the proof, ten predictions for $(d,p)=(2,11),(2,13),(2,17),(2,19),(2,23),(3,17),(3,19),(3,23),(3,29),(4,13)$ were written to a file (MD5 `d5c36be3736079cbc2349f469751c627`) and then computed: ten agreements.

- Theorem C: $143$ cells, for $q\in\{3,\dots,10,12\}$ and $p\in\{2,3,5,7\}$, both with $p\mid q$ (including $p=2$) and with $p\nmid q$, all in agreement; the guess $ed+v_p(d)$ fails in one of them and the guess $ed$ in $26$.

- Theorem D: the rank formula for $W_{s,s+1}$ checked directly in $264$ cases ($p\le7$, $m\le11$); the value of $N$ agrees with the computed groups in $23$ cells with $p\le d$.

- Conjecture F: found from $88$ pieces with $p=3,5$. Then $30$ pieces with $p=7$, $7\le m\le11$, $1\le c\le6$ were predicted before being computed (MD5 of the file `1f5cc12e88f12e375022658da3eea6ce`): $30$ agreements. Then $14$ full groups $\operatorname{Syl}_pK(H(d,q))$ with composite $q\in\{6,9,10,12,15,20,25,27\}$ and $p\le d\le 2p-2$ (MD5 `341a2c489aef1c30349bae079ddcce81`): $14$ agreements. It also agrees with the $10$ full groups computed for $q=p\in\{3,5,7\}$ and $p\le d\le2p-2$.

## Data beyond $2p-2$


For $q=p=3$ the computed groups, written as $(n_1,n_2,\dots)$ with $n_v$ the number of factors $\mathbb{Z}/3^v$, are:

| d | (n_1, n_2, ...) |
|---|---|
| 5 | $(12,10,16,53,5)$ |
| 6 | $(38,37,36,117,24,16,6)$ |
| 7 | $(86,105,127,285,85,63,41)$ |
| 8 | $(250,211,286,1078,174,133,174,8)$ |
| 9 | $(942,412,624,3339,449,292,495,133,84,37,9)$ |


For $p=2$ the whole problem is the hypercube, solved in [DST] with the tilting modules of $SL_2$ in characteristic $2$; we expect the general case $m\ge 2p-1$ to follow the same pattern, with tilting modules having more Weyl factors.


## Provenance

The results were found on the night of 12--13 October 2026 by an AI system, Claude (Anthropic), working for the author: it chose the problem after a search of the literature, wrote the computations, found the formulas, sealed and checked the predictions, and found the proofs; it also found, when checking the literature before publication, that Theorem A is [JNR03, Theorem 13]. The author takes responsibility for the paper. To the best of our knowledge, after a search of the works citing [JNR03] and of arXiv, Theorems B, C, D and E and Conjecture F are new; Theorem A is due to Jacobson, Niedermaier and Reiner.


## References

- [Bai03] H. Bai, On the critical group of the $n$-cube, *Linear Algebra Appl.* 369 (2003), 251–261.
- [Big99] N. L. Biggs, Chip-firing and the critical group of a graph, *J. Algebraic Combin.* 9 (1999), 25–45.
- [CSX15] D. B. Chandler, P. Sin, Q. Xiang, The Smith group of the hypercube graph, arXiv:1511.00272.
- [DJ14] J. E. Ducey, D. M. Jalil, Integer invariants of abelian Cayley graphs, *Linear Algebra Appl.* 445 (2014), 316–325; arXiv:1308.2335.
- [Don93] S. Donkin, On tilting modules for algebraic groups, *Math. Z.* 212 (1993), 39–60.
- [DST] R. Amichis Luengo, The Dancing Sand Theorem: the 2-part of the sandpile group of the hypercube, for every $n$, preprint (2026), hexagon:2610.00205; doi:10.5281/zenodo.23188298.
- [Jan03] J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Math. Surveys Monogr. 107, Amer. Math. Soc., 2003.
- [JNR03] B. Jacobson, A. Niedermaier, V. Reiner, Critical groups for complete multipartite graphs and Cartesian products of complete graphs, *J. Graph Theory* 44 (2003), 231–250.
- [Pro82] R. A. Proctor, Representations of $\mathfrak{sl}(2,\mathbb C)$ on posets and the Sperner property, *SIAM J. Algebraic Discrete Methods* 3 (1982), 275–280.
- [Wil90] R. M. Wilson, A diagonal form for the incidence matrices of $t$-subsets vs. $k$-subsets, *European J. Combin.* 11 (1990), 609–615.
