# The Coloured Sand Theorem: the $p$-part of the sandpile group of the Hamming graph

Rafael Amichis Luengo · Madrid, Spain · tretoef@gmail.com · 13 October 2026. Version 2 (version 1: doi:10.5281/zenodo.23327609). Concept doi:10.5281/zenodo.23327608


**Abstract.** 
Let $H(d,q)=K_q^{\,d}$ be the Hamming graph and $K(H(d,q))$ its sandpile group (critical group). For primes $p\nmid q$ its $p$-part was determined by Jacobson, Niedermaier and Reiner in 2003, who called the remaining primes difficult, "due to bad behavior of its $p$-primary structure". We treat the primes $p\mid q$. Jacobson, Niedermaier and Reiner showed that over $\mathbb{Z}$ the Laplacian splits into explicit triangular pieces; we read these pieces as operators $q(c+H)+U$ on the Boolean lattice (A). From this we prove: (B) a closed formula for the Sylow $p$-subgroup for every prime $p>d$ and every $q$ divisible by $p$, in which ballot numbers appear; (C) the exponent of the Sylow $p$-subgroup for every prime $p$ and every $q\ge3$, namely $p^{\max_{1\le s\le d}(e s+v_p(s))}$ with $e=v_p(q)\ge1$; (D) the number of its cyclic factors when $p\mid q$, from Wilson's diagonal form of inclusion matrices. For $d\le 3p-1$ ($p$ odd) we determine the group exactly (F, G), by writing down the lifts to the $p$-adic integers of the tilting modules of $SL_2$ in characteristic $p$. This proves the Glue Conjecture of version 1, which had predicted $44$ cases before they were computed, all correctly. We conjecture that the same formula holds for $d\le p^2-2$ (H, $p$ odd), and we give a closed form for the number of cyclic factors when $3\mid q$.

## 1. Introduction

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

**Theorem A** (Jacobson–Niedermaier–Reiner, [JNR03, Theorem 13]). 
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
$$
\begin{aligned}
d=2:&\quad (\mathbb{Z}/p^{e})^{u^2+1}\oplus(\mathbb{Z}/p^{2e})^{2u},\\
d=3:&\quad (\mathbb{Z}/p^{e})^{u^3+3u}\oplus(\mathbb{Z}/p^{2e})^{3u^2+2}\oplus(\mathbb{Z}/p^{3e})^{3u},\\
d=4:&\quad (\mathbb{Z}/p^{e})^{u^4+6u^2+2}\oplus(\mathbb{Z}/p^{2e})^{4u^3+8u}\oplus(\mathbb{Z}/p^{3e})^{6u^2+3}\oplus(\mathbb{Z}/p^{4e})^{4u}.
\end{aligned}
$$
Theorem B is the case $m<p$ of a statement about single pieces (Theorem E in Section 3), which also gives, for every prime $p$, the contribution of all pieces with $d-j<p$.

**Theorem C** (the exponent). 
Let $q\ge3$, let $p$ be any prime and $e=v_p(q)$. The exponent of $\operatorname{Syl}_p K(H(d,q))$ is $p^{E}$, where

$$
E=\max_{1\le s\le d}\big(e\,s+v_p(s)\big)\quad\text{if } e\ge1,\qquad E=\lfloor\log_p d\rfloor\quad\text{if } e=0 .
$$

For $p>d$ this gives $E=ed$, as in Theorem B. For $p\le d$ the maximum need not be at $s=d$: for $q=3$ and $d=10$ it is at $s=9$ and $E=11$. The case $e=0$ ($p\nmid q$) can also be read off from [JNR03, Theorem 2]; we include it because the proof below covers it at no cost.

**Theorem D** (the number of cyclic factors). 
Let $p\mid q$. The number of cyclic factors of $\operatorname{Syl}_p K(H(d,q))$ is

$$
N=\sum_{j=0}^{d}\binom dj(q-2)^j\Big(2^{\,d-j}-\rho_p(d-j)\Big)\;-\;1,\qquad \rho_p(m)=\sum_{s=0}^{m-1}r_p(m,s),
$$

where $r_p(m,s)=\sum_{i}\big(\binom mi-\binom m{i-1}\big)$, the sum over $0\le i\le t$ with $p\nmid k-i$, and $(t,k)=(s,s+1)$ if $2s\le m-1$, $(t,k)=(m-1-s,m-s)$ otherwise.

Here $\rho_p(m)$ is the rank over $\mathbb{F}_p$ of $U$ on $B_m$. For $q=p=3$ the theorem gives $N=1,4,12,34,96,274,\dots$, and $N=3^{d-1}+2^{d-1}-1$ for every $d$ (Corollary 6). For $q=p$ the value of $N$ equals the bound $\frac12(q^d+(q-2)^d)-1$ of [JNR03, Theorem 3] for $d\le2$, is one less for $d=3$, and is strictly smaller for $4\le d\le8$ and $p\le11$ (where we compared).

**Corollary 1**. 
$\operatorname{Syl}_p K(H(d,q))$ depends on $q$ only through $e=v_p(q)$ and the multiplicities $\binom dj(q-2)^j$.

### Status
 This is a preprint. The proofs of Theorems B–D and E were re-read once by the system that wrote them (see Provenance) and checked against the computations of Section 7; they have not yet been read by an independent reader. Version 2 (13 October 2026) adds Theorems F and G, Conjecture H and Corollary 6; in version 1, Theorem F was stated as a conjecture. The new proofs have been read only by the system that wrote them. Conjecture H is supported by the method of proof and by computation; see Section 8.

By Theorem G (Section 6), what remains is the range $d\ge 3p$, and there only the pieces $X_q(m,c)$ with $m\ge 3p$. For $m\le p^2-2$ we state a precise conjecture; beyond that range the tilting modules have four or more Weyl factors, and we leave the question open.

## 2. The splitting (after Jacobson, Niedermaier and Reiner)

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

## 3. Strings, and the primes $p>m$

On $B_m$ one has $[D,U]=m-2H$: on a set $S$ of size $s$, $DU(S)=(m-s)S+\Sigma$ and $UD(S)=s\,S+\Sigma$ with the same sum $\Sigma=\sum_{y\in S,\,x\notin S}(S\setminus\{y\})\cup\{x\}$. For $0\le k\le m/2$ let $\Lambda_k=\ker D\cap B_m(k)$. By induction on $i$, for $v\in\Lambda_k$,
$$
D\,U^iv=i\,(m-2k-i+1)\,U^{i-1}v . \tag{1}
$$
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

## 4. The exponent

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

## 5. The number of cyclic factors

*Proof of Theorem D.* 
The number of cyclic factors of $\operatorname{Syl}_p K$ is $\dim_{\mathbb{F}_p}(\operatorname{coker} L\otimes\mathbb{F}_p)-1$, the $1$ for the free summand. Modulo $p$, $q(j+H)+U\equiv U$, so by Theorem A $\dim_{\mathbb{F}_p}(\operatorname{coker} L\otimes\mathbb{F}_p)=\sum_j\binom dj(q-2)^j\big(2^{d-j}-\operatorname{rank}_{\mathbb{F}_p}U|_{B_{d-j}}\big)$. The rank of $U$ is the sum over $s$ of the ranks of the inclusion matrices $W_{s,s+1}$ of $s$-subsets versus $(s+1)$-subsets of $[m]$. By Wilson's diagonal form [Wil90], for $t\le\min(k,m-k)$ the matrix $W_{t,k}$ is equivalent over $\mathbb{Z}$ to a diagonal matrix with entries $\binom{k-i}{t-i}$ of multiplicity $\binom mi-\binom m{i-1}$, $0\le i\le t$ (we use the statement as given in [CSX15, (2)]); so its rank over $\mathbb{F}_p$ is $\sum_{i:\,p\nmid\binom{k-i}{t-i}}(\binom mi-\binom m{i-1})$. For $W_{s,s+1}$ with $2s\le m-1$ take $(t,k)=(s,s+1)$, so $\binom{k-i}{t-i}=s+1-i$; otherwise complementation identifies $W_{s,s+1}$ with the transpose of $W_{m-s-1,m-s}$ and we take $(t,k)=(m-1-s,m-s)$. This is $r_p(m,s)$.
 ∎

**Corollary 6** (the number of factors when $3\mid q$). 
If $3\mid q$, the number of cyclic factors of $\operatorname{Syl}_3K(H(d,q))$ is

$$
N=(q-1)^d+\frac{q^d-(q-1)^d}{3}-\frac{(q-1)^d-(q-3)^d}{6}-1 .
$$

In particular $N=3^{d-1}+2^{d-1}-1$ for $q=3$.

*Proof.* 
By Theorem D it suffices to know $f(m)=\dim_{\mathbb{F}_3}\operatorname{coker}(U|_{B_m\otimes\mathbb{F}_3})$. Identify $B_m\otimes\mathbb{F}_3$ with $V^{\otimes m}$, $V=\mathbb{F}_3^2$, so that $U=\sum_ie_i$ with $e$ the nilpotent $2\times2$ Jordan block acting on the $i$-th factor. The $e_i$ commute, so $U^3=\sum_ie_i^3=0$, and $V^{\otimes m}$ is a module over the Hopf algebra $\mathbb{F}_3[e]/(e^3)$ with $e$ primitive. Then $f(m)$ is the number of Jordan blocks of $U$. Write $J_a$ for the indecomposable module of dimension $a\le3$. Then:

- $J_1\otimes J_2=J_2$;
- $J_2\otimes J_2=J_3\oplus J_1$, since $e^2(v_0\otimes v_0)=2\,v_1\otimes v_1\ne0$;
- $J_3\otimes J_2=J_3^2$, because $J_3$ is free, a projective tensored with any module is projective, and projectives over this local algebra are free.

So $V^{\otimes m}=a_mJ_1\oplus b_mJ_2\oplus c_mJ_3$ with $(a_{m+1},b_{m+1},c_{m+1})=(b_m,a_m,b_m+2c_m)$, starting from $(1,0,0)$. Hence $a_m+b_m=1$, $b_m=[m\text{ odd}]$, and counting dimensions, $c_m=(2^m-1-[m\text{ odd}])/3$. This gives $f(m)=1+(2^m-1-[m\text{ odd}])/3$. Summing $\sum_m\binom dm(q-2)^{d-m}f(m)$ gives the formula.
 ∎

## 6. The range $p\le d$: tilting lattices

By Theorem E the only pieces not yet described are $X_q(m,c)$ with $m\ge p$. For $p\le m$ the strings of length $>p$ break: by (1) the coefficient $i(m-2k-i+1)$ vanishes modulo $p$. The way they break is governed by the representation theory of $SL_2$ in characteristic $p$.

### The dictionary

Let $V=\mathbb{Z}_p v_0\oplus\mathbb{Z}_p v_1$, where $\mathbb{Z}_p$ is the ring of $p$-adic integers, and let $f$ act on $V$ by $fv_0=v_1$, $fv_1=0$; give $v_0$ weight $1$ and $v_1$ weight $-1$. Identify $B_m\otimes\mathbb{Z}_p$ with $V^{\otimes m}$ by $S\mapsto v_{\mathbf 1_S}$. Then $U$ is the action of $f$ on the tensor power, a subset of size $s$ has weight $m-2s$, and so $H=(m-h)/2$ with $h$ the weight. The divided powers $U^{(r)}$ (add $r$ new elements, in all ways) are integral, and so is the analogous operator $e^{(r)}$ (remove $r$ elements). Hence $B_m\otimes\mathbb{Z}_p$ is a module over the distribution algebra $\mathrm{Dist}(SL_2)_{\mathbb{Z}_p}$, and

$$
q(c+H)+U \;=\; q\big(c+\tfrac{m-h}{2}\big)+f
$$

is built from that action alone.

We use three standard facts.

- (T1) $V^{\otimes m}$ is a tilting module, and it decomposes over $\mathbb{Z}_p$ as $\bigoplus_\lambda T_{\mathbb{Z}_p}(\lambda)^{n_\lambda}$, where $T_{\mathbb{Z}_p}(\lambda)$ is the unique lift of the indecomposable tilting module $T(\lambda)$ over $\mathbb{F}_p$. The reason is that $\mathrm{Ext}^1(\Delta,\nabla)=0$, so decompositions over $\mathbb{F}_p$ lift; this is standard [Jan03, Don93]. For $p=2$ the argument is written out, and checked in Lean, in [DST, Lemma 3.3, Corollary 3.4].
- (T2) For $\lambda\le p-1$, and for $\lambda+1\equiv0\pmod p$ with $\lambda\le p^2-1$, $T(\lambda)=\Delta(\lambda)$ is simple. For $\lambda=p-1+r+pa$ with $1\le r\le p-1$ and $0\le a\le p-1$, $T(\lambda)\cong T(p-1+r)\otimes\Delta(a)^{[1]}$ [Don93], and its Weyl factors are $\Delta(\lambda)$ and $\Delta(\lambda^-)$, $\lambda^-:=\lambda-2r$ (the other terms of the product of characters cancel in pairs). $T(\lambda)$ is a non-split extension $0\to\Delta(\lambda)\to T(\lambda)\to\Delta(\lambda^-)\to0$, and so is its lift over $\mathbb{Z}_p$.
- (T3) Comparing characters, the multiplicities in $V^{\otimes m}$ are given, from the top down, by $n_\lambda=\beta(m,\lambda)-n_{\lambda^+}$. Here $\lambda^+$ is the weight whose bottom factor is $\lambda$, and $n_{\lambda^+}=0$ if there is none or if $\lambda^+>m$.

For $\lambda\equiv m\pmod 2$, $0\le\lambda\le m$, write $\beta(m,\lambda)=\binom{m}{(m-\lambda)/2}-\binom m{(m-\lambda)/2-1}$ (the number of strings of length $\lambda+1$) and

$$
A_c(m,\lambda)=\sum_{r=(m-\lambda)/2}^{(m+\lambda)/2}\big(e+v_p(c+r)\big),
$$

the valuation of the determinant of $q(c+H)+U$ on one such string.

### The blocks

For $\lambda\equiv m\pmod2$ define the abelian $p$-group $G_c(m,\lambda)$ by

$$
G_c(m,\lambda)=\begin{cases}
\mathbb{Z}/p^{A_c(m,\lambda)}, & \lambda\le p-1,\\[2pt]
(\mathbb{Z}/p)^{a}\oplus\mathbb{Z}/p^{A_c(m,\lambda)-a}, & \lambda+1=(a+1)p,\ a\ge1,\\[2pt]
(\mathbb{Z}/p)^{2a}\oplus\mathbb{Z}/p^{A_c(m,\lambda^-)+1-a}\oplus\mathbb{Z}/p^{A_c(m,\lambda)-1-a}, & \lambda=p-1+r+pa,\\ &\quad 1\le r\le p-1,
\end{cases}
$$

with the convention that when $c=0$ and $\lambda=m$ (the block containing the empty set) the last factor is replaced by the free summand $\mathbb{Z}_p$.

The first theorem is the statement conjectured in version 1 of this paper. It is the case $m\le2p-2$ of Theorem G below, where only $a=0$ occurs.

**Theorem F** (the Glue Theorem; Conjecture F of version 1). 
Let $p$ be a prime, $q$ an integer with $e=v_p(q)\ge1$, $m\le2p-2$ and $c\ge0$. Then

$$
\begin{aligned}\operatorname{Syl}_pX_q(m,c)\;\cong\;&\bigoplus_{\lambda\le p-1}\big(\mathbb{Z}/p^{A_c(m,\lambda)}\big)^{\beta(m,\lambda)-\beta'(m,\lambda)}\\&\oplus\bigoplus_{p\le\lambda\le m}\Big(\mathbb{Z}/p^{A_c(m,\lambda)-1}\oplus\mathbb{Z}/p^{A_c(m,2p-2-\lambda)+1}\Big)^{\beta(m,\lambda)},\end{aligned}
$$

where $\beta'(m,\lambda)=\beta(m,2p-2-\lambda)$ if $\lambda\le p-2$ and $\beta'(m,p-1)=0$, and $\lambda$ runs over integers $\equiv m\pmod2$. When $c=0$ the string of length $m+1$ (through the empty set) has a zero on its diagonal: for $\lambda=m<p$ it gives nothing, and for $\lambda=m\ge p$ the term $\mathbb{Z}/p^{A_c(m,m)-1}$ is omitted (it is the free summand) while its partner $\mathbb{Z}/p^{A_0(m,2p-2-m)+1}$ stays.

More generally:

**Theorem G** (the tilting blocks). 
Let $p$ be a prime, $q$ an integer with $e=v_p(q)\ge1$, $c\ge0$, and $m\le 3p-1$ if $p$ is odd, $m\le3$ if $p=2$. Then

$$
\mathbb{Z}_p^{\,[c=0]}\oplus\operatorname{Syl}_pX_q(m,c)\;\cong\;\bigoplus_{\lambda}G_c(m,\lambda)^{\,n_\lambda},
$$

where $\lambda$ runs over the integers $\equiv m\pmod 2$ with $0\le\lambda\le m$ and $n_\lambda$ is as in (T3).

With Theorem A, Theorem G determines $\operatorname{Syl}_pK(H(d,q))$ for every $d\le 3p-1$ ($p$ odd). For $p=2$ the range is $d\le3$, and the whole $2$-part of the hypercube is [DST]; for $p=2$ and $m=4$ the formula fails, because the block $\lambda=4$ already has $a=p-1$ (checked). The hypothesis $e\ge1$ is needed: for $p\nmid q$ the formula fails, for instance when $(q,p,d)=(4,3,4)$; there the answer of [JNR03] applies instead.

**Conjecture H**. 
For every odd prime $p$, the isomorphism of Theorem G holds for every $m\le p^2-2$.

The bound is where the method of the proof stops. In Lemma 7 below the denominator of the glue is controlled by the coefficient $(a+1)p$ of $e$, and for $a=p-1$ this becomes $p^2$. Indeed for $p=3$ and $m=9$ the formula of Theorem G, applied beyond its range, is wrong by exactly one factor, in the block $\lambda=9$ (Section 8).

### Proofs

Fix $\lambda=p-1+r+pa$ with $1\le r\le p-1$, $a\in\{0,1\}$ and $a+1<p$, and put $\mu=\lambda^-=\lambda-2r$. Let $\ell_i=f^{(i)}x$ ($0\le i\le\lambda$) be the standard basis of $\Delta_{\mathbb{Z}_p}(\lambda)$, so $f\ell_i=(i+1)\ell_{i+1}$ and $e\ell_i=(\lambda-i+1)\ell_{i-1}$. Let $s_j=f^{(j)}y$ ($0\le j\le\mu$) be that of $\Delta_{\mathbb{Z}_p}(\mu)$.

**Lemma 7** (the glue is forced). 
$T_{\mathbb{Z}_p}(\lambda)$ is isomorphic to the lattice in $\Delta_{\mathbb{Q}_p}(\lambda)\oplus\Delta_{\mathbb{Q}_p}(\mu)$ spanned by the $\ell_i$ and by

$$
\tilde s_j=s_j+\tfrac1p\tbinom{j+r}{j}\,\ell_{j+r}\qquad(0\le j\le\mu).
$$

*Proof.* 
By (T2), $T=T_{\mathbb{Z}_p}(\lambda)$ contains $\Delta_{\mathbb{Z}_p}(\lambda)$ with quotient $\Delta_{\mathbb{Z}_p}(\mu)$. Weight spaces of $\Delta(\lambda)$ are one-dimensional, so the lifts of the $s_j$ to $T\subset\Delta_{\mathbb{Q}_p}(\lambda)\oplus\Delta_{\mathbb{Q}_p}(\mu)$ have the form $\tilde s_j=s_j+x_j\ell_{j+r}$, $x_j\in\mathbb{Q}_p$, determined modulo $\mathbb{Z}_p$.

Stability under $e$ at $j=0$ gives $x_0(\lambda-r+1)\in\mathbb{Z}_p$, and $\lambda-r+1=(a+1)p$ with $a+1<p$, so $x_0\in p^{-1}\mathbb{Z}_p$.

Stability under $f$ gives $(j+r+1)x_j-(j+1)x_{j+1}\in\mathbb{Z}_p$. For $j\not\equiv-1\pmod p$ the factor $j+1$ is a unit, so $x_{j+1}\equiv\frac{j+r+1}{j+1}x_j$ modulo $\mathbb{Z}_p$, and within each block of indices $[kp,(k+1)p-1]$ we get $x_j\equiv\binom{j+r}{j}\binom{kp+r}{kp}^{-1}x_{kp}$. At $j=p-1$ the condition reads $rx_{p-1}\in\mathbb{Z}_p$, and it holds automatically: by Lucas, $p\mid\binom{p-1+r}{p-1}$. When $a=1$, stability under $f^{(p)}$ at $j=0$ gives $\binom{r+p}{p}x_0-x_p\in\mathbb{Z}_p$, and $\binom{r+p}{p}\equiv1$ by Lucas, so $x_p\equiv x_0$. Hence $x_j\equiv\binom{j+r}{j}x_0$ for every $j$.

If $x_0\in\mathbb{Z}_p$ then $T=\Delta_{\mathbb{Z}_p}(\lambda)\oplus\Delta_{\mathbb{Z}_p}(\mu)$, which is impossible since $T\otimes\mathbb{F}_p$ is indecomposable. So $x_0=u/p$ with $u$ a unit, and rescaling $y$ makes $u=1$. The lattice so described is $T$ itself, so it is stable under all $f^{(t)}$ and $e^{(t)}$; nothing more has to be checked. (For $f^{(t)}$ this is also visible directly: $f^{(t)}\tilde s_j-\binom{j+t}{t}\tilde s_{j+t}$ vanishes by the identity $\binom{j+r}{j}\binom{j+r+t}{t}=\binom{j+t}{t}\binom{j+t+r}{j+t}$.) Stability under every $e^{(t)}$ and $f^{(t)}$ is also checked by machine in Section 7.
 ∎

**Lemma 8** (the blocks). 
Embed $T_{\mathbb{Z}_p}(\lambda)$ in $B_m\otimes\mathbb{Z}_p$ at levels $k,\dots,k+\lambda$ ($m=\lambda+2k$). Then the cokernel of $q(c+H)+U$ on it is $G_c(m,\lambda)$. The same holds for the simple blocks ($\lambda\le p-1$, or $\lambda+1\in p\mathbb{Z}$).

*Proof.* 
Put $N_t=q(c+k+t)$, so $v_p(N_t)=e+v_p(c+k+t)$, and $M=q(c+H)+U$. In the basis of Lemma 7:

- $M\ell_i=N_i\ell_i+(i+1)\ell_{i+1}$;
- $M\tilde s_j=N_{j+r}\tilde s_j+(j+1)\tilde s_{j+1}$ for $j<\mu$ (the $\ell$-component is $\frac1p[(j+r+1)\binom{j+r}{j}-(j+1)\binom{j+r+1}{j+1}]\ell_{j+r+1}=0$);
- $M\tilde s_\mu=N_{\mu+r}\tilde s_\mu+u\,\ell_{\mu+r+1}$, where $u=\frac1p\binom{\mu+r}{\mu}(\mu+r+1)=(a+1)\binom{(a+1)p-1}{\mu}$ is a unit by Lucas.

The non-unit subdiagonal entries are the $i+1\in\{p,\dots,(a+1)p\}$ on the $\ell$-chain and the $j+1\in\{p,\dots,ap\}$ on the $\tilde s$-chain, each of valuation $1$. Solving the unit subdiagonals, the cokernel is generated by the first vector of each segment between them, with one relation at the end of each segment.

For $a=0$ the generators are $\ell_0,\ell_p,\tilde s_0$. With $\alpha=\sum_{t<p}v(N_t)$, $\beta_2=\sum_{t\ge p}v(N_t)$ and $A'=\sum_{t=r}^{p-1}v(N_t)=A_c(m,\mu)$, the relations become (up to units) $p^{\alpha}\ell_0+p\,\ell_p$, $p^{\beta_2}\ell_p$, and $\ell_p=p^{A'}\tilde s_0$. So the cokernel is presented on $(\ell_0,\tilde s_0)$ by $\begin{pmatrix}p^{\alpha}&p^{1+A'}\\0&p^{\beta_2+A'}\end{pmatrix}$. Since $\alpha=A'+\sum_{t<r}v(N_t)\ge A'+1$ and $\beta_2\ge1$, its elementary divisors are $p^{A'+1}$ and $p^{\alpha+\beta_2-1}=p^{A-1}$, with $A=A_c(m,\lambda)$.

For $a=1$ the generators are $\ell_0,\ell_p,\ell_{2p},\tilde s_0,\tilde s_p$, and $\ell_{2p}$ is eliminated by the cross relation. With segment valuations $a_1,a_2,a_3$ on the $\ell$-chain and $\sigma_1,\sigma_2$ on the $\tilde s$-chain, the presentation on $(\ell_0,\ell_p,\tilde s_0,\tilde s_p)$ is

$$
\begin{pmatrix}p^{a_1}&p&0&0\\0&p^{a_2}&0&p^{1+\sigma_2}\\0&0&p^{\sigma_1}&p\\0&0&0&p^{a_3+\sigma_2}\end{pmatrix}.
$$

Every entry has valuation $\ge1$ and $p$ occurs twice in different rows and columns, so the first two elementary divisors are $p$. The smallest valuation of a $3\times3$ minor is $2+\sigma_1+\sigma_2=2+A'$, because $a_1+a_2\ge A'+1$ and $a_3\ge1$. The determinant has valuation $A+A'$. So the divisors are $p,p,p^{A'},p^{A-2}$, which is $G_c(m,\lambda)$ for $a=1$.

When $c=0$ and $k=0$, $N_0=0$: the vector $\ell_0$ generates a free summand, and the relation at the end of the first segment loses its first term. The same elimination gives $\mathbb{Z}_p\oplus$ the stated group. The simple blocks are single chains; when $\lambda+1=(a+1)p$ the chain has $a$ non-unit subdiagonal entries, each $p$, and the same elimination gives $(\mathbb{Z}/p)^a\oplus\mathbb{Z}/p^{A-a}$.
 ∎

*Proof of Theorems G and F.* 
Combine (T1)–(T3), Lemma 7 and Lemma 8. In the stated range every $\lambda\le m$ is simple or has $a\le1$ and $a+1<p$.
 ∎

**Example 9**. 
For $p=q=3$ and $d=4$: Theorem A gives the pieces $X(4,0)$, $X(3,1)^4$, $X(2,2)^6$, $X(1,3)^4$, $X(0,4)$, and Theorem F gives $\operatorname{Syl}_3K(H(4,3))\cong(\mathbb{Z}/3)^2\oplus(\mathbb{Z}/3^2)^{7}\oplus(\mathbb{Z}/3^3)^{8}\oplus(\mathbb{Z}/3^4)^{17}$, which is the group we computed.

## 7. Verification

All computations were exact. The Smith forms over $\mathbb{Z}_{(p)}$ were computed modulo $p^M$ with $p^M<2^{31}$, by unit pivots and Schur complements, level by level in the $p$-adic valuation; factors of valuation at least $M$ were then determined separately, by the matrix $p^E M^{-1}$ of Lemma 4, whose elementary divisors are $p^{E-a}$ for the divisors $p^a$ of $M$. The scripts, the sealed prediction files and the logs are at https://github.com/tretoef-estrella/coloured-sand-theorem and in the Zenodo record [doi:10.5281/zenodo.23327608](https://doi.org/10.5281/zenodo.23327608) (all versions).

- Theorem A: the Sylow $p$-subgroups for $p\in\{2,3,5,7\}$ computed directly from the Laplacian and from the pieces agree in all $90$ comparisons ($27$ cells, $q\in\{3,\dots,10,12\}$, $q^d\le729$, including $p\mid q$ and $p\le d$); adding one extra copy of a piece changes the answer in $49$ of them. Independently, the cells $(d,q)=(3,7)$ and $(2,11)$ were recomputed with Sage from the full Laplacian.
- Theorem B: found first as a conjecture from the cells with $d\le4$; before the proof, ten predictions for $(d,p)=(2,11),(2,13),(2,17),(2,19),(2,23),(3,17),(3,19),(3,23),(3,29),(4,13)$ were written to a file (MD5 `d5c36be3736079cbc2349f469751c627`) and then computed: ten agreements.
- Theorem C: $143$ cells, for $q\in\{3,\dots,10,12\}$ and $p\in\{2,3,5,7\}$, both with $p\mid q$ (including $p=2$) and with $p\nmid q$, all in agreement; the guess $ed+v_p(d)$ fails in one of them and the guess $ed$ in $26$.
- Theorem D: the rank formula for $W_{s,s+1}$ checked directly in $264$ cases ($p\le7$, $m\le11$); the value of $N$ agrees with the computed groups in $23$ cells with $p\le d$.
- Theorem F, before its proof (version 1): found from $88$ pieces with $p=3,5$. Then $30$ pieces with $p=7$, $7\le m\le11$, $1\le c\le6$ were predicted before being computed (MD5 of the file `1f5cc12e88f12e375022658da3eea6ce`): $30$ agreements. Then $14$ full groups $\operatorname{Syl}_pK(H(d,q))$ with composite $q\in\{6,9,10,12,15,20,25,27\}$ and $p\le d\le 2p-2$ (MD5 `341a2c489aef1c30349bae079ddcce81`): $14$ agreements. It also agrees with the $10$ full groups computed for $q=p\in\{3,5,7\}$ and $p\le d\le2p-2$.
- Lemmas 7 and 8, by machine:
  - the lattices of Lemma 7 are stable under every $e^{(t)}$ and $f^{(t)}$ for $p\in\{3,5,7\}$ and every $\lambda\in[p,3p-2]$ ($27$ lattices; $2200$ checks for $\lambda\le2p-2$);
  - the cokernel of $q(c+H)+U$ on the model equals the formula of Lemma 8 in $292$ random cases with $\lambda\le 2p-2$ ($p\le7$), in $180$ cases with $\lambda\le p^2-2$ ($p=3,5$; $e\in\{1,2\}$), and in $60$ cases with $c=0$;
  - removing the glue (the split lattice) changes the answer in $293$ of $293$ cases, and the formula of Theorem F applied beyond $2p-2$ fails in $12$ of $18$ pieces.
- Theorem G against direct computation: the predicted pieces equal the Smith forms of $q(c+H)+U$ computed on $B_m$ in $154$ cases ($p=3$, $m\le7$; $p=5$, $m\le10$; $e\in\{1,2\}$; $0\le c\le6$) and in $5$ cases with $p=3$, $m=8=3p-1$. The full groups for $p=q=3$ and $d=5,\dots,8$ computed in version 1 from the full Laplacian (Section 8) are reproduced exactly.
- Corollary 6: $\dim_{\mathbb{F}_p}\operatorname{coker} U$ on $B_m$ computed by ranks agrees with the count of Jordan blocks in $37$ cases ($p\in\{3,5,7\}$, $m\le12$); the characteristic-$0$ count $\binom m{\lfloor m/2\rfloor}$ differs in $7$ of them.

## 8. Data for $p=q=3$

For $q=p=3$ the computed groups, written as $(n_1,n_2,\dots)$ with $n_v$ the number of factors $\mathbb{Z}/3^v$, are:

| d | (n_1, n_2, ...) |
|---|---|
| 5 | $(12,10,16,53,5)$ |
| 6 | $(38,37,36,117,24,16,6)$ |
| 7 | $(86,105,127,285,85,63,41)$ |
| 8 | $(250,211,286,1078,174,133,174,8)$ |
| 9 | $(942,412,624,3339,449,292,495,133,84,37,9)$ |

Theorem G gives the rows $d=5,\dots,8$ exactly ($d\le3p-1$). For $d=9$ one piece has $m=9=3p$, outside the range. There the formula of Theorem G, applied anyway, gives $(942,414,623,3339,448,293,495,134,84,36,9)$ instead of the true row. The difference is one factor, in the block $\lambda=9=3p$, where $a=p-1$ and the glue of Lemma 7 may have denominator $p^2$. For $p=2$ the whole problem is the hypercube, solved in [DST] with the tilting modules of $SL_2$ in characteristic $2$; the general case $m\ge 3p$ should follow the same pattern, with tilting modules having more Weyl factors.

## Provenance

The results were found on the night of 12–13 October 2026 by an AI system, Claude (Anthropic), working for the author: it chose the problem after a search of the literature, wrote the computations, found the formulas, sealed and checked the predictions, and found the proofs; it also found, when checking the literature before publication, that Theorem A is [JNR03, Theorem 13]. Version 2 was written later the same night, also by Claude: the Glue Conjecture of version 1 was proved and extended (Theorems F, G) by writing down the tilting lattices, and the closed form of $N$ (Corollary 6) was proved. The author takes responsibility for the paper. To the best of our knowledge, after a search of the works citing [JNR03] and of arXiv, Theorems B, C (for $e\ge1$), D, E, F and G, Corollary 6 and Conjecture H are new; version 1 also claimed the case $e=0$ of Theorem C, which follows from [JNR03, Theorem 2]. Theorem A is due to Jacobson, Niedermaier and Reiner. The tilting theory used in Section 6 is classical [Don93, Jan03], and so is the decomposition of tensor powers in the proof of Corollary 6.

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
- [Wil90] R. M. Wilson, A diagonal form for the incidence matrices of $t$-subsets vs.\ $k$-subsets, *European J. Combin.* 11 (1990), 609–615.

