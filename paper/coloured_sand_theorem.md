# The Coloured Sand Theorem: the $p$-part of the sandpile group of the Hamming graph

Rafael Amichis Luengo · Madrid, Spain · tretoef@gmail.com · 13 October 2026 (version 3)


**Abstract.** 
Let $H(d,q)=K_q^{\,d}$ be the Hamming graph and $K(H(d,q))$ its sandpile group (critical group). For primes $p\nmid q$ its $p$-part was determined by Jacobson, Niedermaier and Reiner in 2003, who called the remaining primes difficult, "due to bad behavior of its $p$-primary structure". We treat the primes $p\mid q$. Jacobson, Niedermaier and Reiner showed that over $\mathbb{Z}$ the Laplacian splits into explicit triangular pieces; we read these pieces as operators $q(c+H)+U$ on the Boolean lattice (A). From this we prove: (B) a closed formula for the Sylow $p$-subgroup for every prime $p>d$ and every $q$ divisible by $p$, in which ballot numbers appear; (C) the exponent of the Sylow $p$-subgroup for every prime $p$ and every $q\ge3$, namely $p^{\max_{1\le s\le d}(e s+v_p(s))}$ with $e=v_p(q)\ge1$; (D) the number of its cyclic factors when $p\mid q$, from Wilson's diagonal form of inclusion matrices. For every prime $p$ and every $d\le p^2+p-1$ we determine the group exactly (F, G), by writing down the lifts to the $p$-adic integers of the tilting modules of $SL_2$ in characteristic $p$ that have two Weyl factors. For $p=2$ we determine it for every $d$ (H), from the results of [DST] on the hypercube. This proves the Glue Conjecture of version 1 and Conjecture H of version 2; for these results $107$ predictions were written down before they were computed ($44$ in version 1, $63$ in version 3), all correct. We give a closed form for the number of cyclic factors when $3\mid q$, and we conjecture the shape of the remaining blocks (I): the number of large cyclic factors is the number of Weyl factors of the tilting module, a power of $2$ read off the $p$-adic digits, and the small ones do not depend on $q$.

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
 This is a preprint. The proofs were re-read by the system that wrote them (see Provenance) and checked against the computations of Section 9; they have not yet been read by an independent reader. The versions are on Zenodo, concept doi:10.5281/zenodo.23327608 (version 1: doi:10.5281/zenodo.23327609; version 2: doi:10.5281/zenodo.23328702). Version 2 (13 October 2026) added Theorems F and G for $d\le3p-1$ and Corollary 6; in version 1, Theorem F was stated as a conjecture. Version 3 (13 October 2026) extends Theorem G to $d\le p^2+p-1$ and every prime, which contains Conjecture H of version 2, adds Theorem H (the prime $2$, every $d$) and the new Conjecture I.

By Theorems G and H, what remains is $p$ odd and $d\ge p^2+p$, and there only the pieces $X_q(m,c)$ with $m\ge p^2+p$, whose tilting summands can have four or more Weyl factors. For these blocks we state Conjecture I (Section 8).

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
- (T2) Let $\lambda\le p^2+p-1$. If $\lambda\le p-1$, or if $\lambda+1\equiv0\pmod p$ and $\lambda\le p^2-1$, then $T(\lambda)=\Delta(\lambda)$ is simple. Otherwise write

$$
\lambda=p-1+r+pa,\qquad 1\le r\le p,\ 0\le a\le p-1,
$$

where $r=p$ (and then $a=p-1$) occurs only for $\lambda=p^2+p-1$. Then $T(\lambda)$ has exactly two Weyl factors, $\Delta(\lambda)$ and $\Delta(\lambda^-)$ with $\lambda^-:=\lambda-2r$, and it is a non-split extension $0\to\Delta(\lambda)\to T(\lambda)\to\Delta(\lambda^-)\to0$; so is its lift over $\mathbb{Z}_p$. Indeed, by Donkin's tensor product theorem [Don93], $T(p-1+r'+pb)\cong T(p-1+r')\otimes T(b)^{[1]}$ for $0\le r'\le p-1$. For $r\le p-1$ take $r'=r$, $b=a\le p-1$, so that $T(a)=\Delta(a)$. For $\lambda=p^2+p-1$ take $r'=0$, $b=p$: then $T(p-1)$ is the Steinberg module and $T(p)$ has the Weyl factors $\Delta(p),\Delta(p-2)$. In both cases the product of characters, expanded by Brauer's formula with $\chi(-n-2)=-\chi(n)$, leaves exactly $\chi(\lambda)+\chi(\lambda-2r)$; the other terms cancel in pairs.
- (T3) Comparing characters, the multiplicities in $V^{\otimes m}$ are given, from the top down, by $n_\lambda=\beta(m,\lambda)-n_{\lambda^+}$. Here $\lambda^+$ is the weight whose bottom factor is $\lambda$, and $n_{\lambda^+}=0$ if there is none or if $\lambda^+>m$. (For $\lambda\le p^2+p-1$ the map $\lambda\mapsto\lambda^-$ is injective: $\lambda^-\equiv p-1-r\pmod p$ determines $r$, and then $a$.)

For $\lambda\equiv m\pmod 2$, $0\le\lambda\le m$, write $\beta(m,\lambda)=\binom{m}{(m-\lambda)/2}-\binom m{(m-\lambda)/2-1}$ (the number of strings of length $\lambda+1$).

### The blocks

Fix $m$, $c$ and $\lambda\equiv m\pmod2$, put $k=(m-\lambda)/2$ and

$$
v_t=e+v_p(c+k+t)\qquad(0\le t\le\lambda),
$$

with $v_0=\infty$ when $c=k=0$. Put $A=\sum_{t=0}^{\lambda}v_t$. When $T(\lambda)$ has two Weyl factors, with $(r,a)$ as in (T2), put also

$$
A'=\sum_{t=r}^{r+\lambda^-}v_t,\qquad \alpha=\sum_{t=(a+1)p}^{\lambda}v_t,\qquad \tau=1+[a=p-1],
$$

and

$$
E_{11}=A-\alpha-a,\qquad E_{12}=A'-a+\tau,\qquad E_{22}=A'-a+\alpha.
$$

Here $A'$ is the sum over the levels of the bottom factor (it is $A_c(m,\lambda^-)$ in the notation of Theorem F), and $\alpha$ is the sum over the last $r$ levels of the top factor. Define the abelian $p$-group $G_c(m,\lambda)$ by

$$
G_c(m,\lambda)=\begin{cases}
\mathbb{Z}/p^{A}, & \lambda\le p-1,\\[2pt]
(\mathbb{Z}/p)^{a}\oplus\mathbb{Z}/p^{A-a}, & \lambda+1=(a+1)p\le p^2,\\[2pt]
(\mathbb{Z}/p)^{2a}\oplus\mathbb{Z}/p^{x}\oplus\mathbb{Z}/p^{y}, & \text{two Weyl factors},
\end{cases}
$$

where $x=\min(E_{11},E_{12},E_{22})$ and $y=E_{11}+E_{22}-x$. When $c=k=0$ (the block containing the empty set) we put instead: $\mathbb{Z}_p$ for $\lambda\le p-1$; $\mathbb{Z}_p\oplus(\mathbb{Z}/p)^a$ in the second case; and $\mathbb{Z}_p\oplus(\mathbb{Z}/p)^{2a}\oplus\mathbb{Z}/p^{\min(E_{12},E_{22})}$ in the third.

When $a+1<p$ one has $\tau=1$ and $x=E_{12}=A'+1-a$, so the third case reads $(\mathbb{Z}/p)^{2a}\oplus\mathbb{Z}/p^{A'+1-a}\oplus\mathbb{Z}/p^{A-1-a}$, which is the block of version 2. When $a=p-1$ all three numbers $E_{ij}$ can be the minimum: for $p=3$, $\lambda=10$, $k=0$, $e=1$ the pairs $(x,y)$ are $(11,11)$ for $c=1$ and $(10,12)$ for $c=2$.

The first theorem is the statement conjectured in version 1 of this paper. It is the case $m\le2p-2$ of Theorem G below, where only $a=0$ occurs.

**Theorem F** (the Glue Theorem; Conjecture F of version 1). 
Let $p$ be a prime, $q$ an integer with $e=v_p(q)\ge1$, $m\le2p-2$ and $c\ge0$. Then

$$
\begin{aligned}\operatorname{Syl}_pX_q(m,c)\;\cong\;&\bigoplus_{\lambda\le p-1}\big(\mathbb{Z}/p^{A_c(m,\lambda)}\big)^{\beta(m,\lambda)-\beta'(m,\lambda)}\\&\oplus\bigoplus_{p\le\lambda\le m}\Big(\mathbb{Z}/p^{A_c(m,\lambda)-1}\oplus\mathbb{Z}/p^{A_c(m,2p-2-\lambda)+1}\Big)^{\beta(m,\lambda)},\end{aligned}
$$

where $A_c(m,\lambda)=\sum_{r=(m-\lambda)/2}^{(m+\lambda)/2}\big(e+v_p(c+r)\big)$, $\beta'(m,\lambda)=\beta(m,2p-2-\lambda)$ if $\lambda\le p-2$ and $\beta'(m,p-1)=0$, and $\lambda$ runs over integers $\equiv m\pmod2$. When $c=0$ the string of length $m+1$ (through the empty set) has a zero on its diagonal: for $\lambda=m<p$ it gives nothing, and for $\lambda=m\ge p$ the term $\mathbb{Z}/p^{A_c(m,m)-1}$ is omitted (it is the free summand) while its partner $\mathbb{Z}/p^{A_0(m,2p-2-m)+1}$ stays.

More generally:

**Theorem G** (two Weyl factors). 
Let $p$ be a prime, $q$ an integer with $e=v_p(q)\ge1$, $c\ge0$, and $m\le p^2+p-1$. Then

$$
\mathbb{Z}_p^{\,[c=0]}\oplus\operatorname{Syl}_pX_q(m,c)\;\cong\;\bigoplus_{\lambda}G_c(m,\lambda)^{\,n_\lambda},
$$

where $\lambda$ runs over the integers $\equiv m\pmod 2$ with $0\le\lambda\le m$ and $n_\lambda$ is as in (T3).

With Theorem A, Theorem G determines $\operatorname{Syl}_pK(H(d,q))$ for every $d\le p^2+p-1$. This contains Conjecture H of version 2 ($p$ odd, $d\le p^2-2$). For $p=3$ the range is $d\le11$ and for $p=5$ it is $d\le29$. For $p=2$ it is $d\le5$; the prime $2$ is treated for every $d$ in Section 7. The range is exactly the range in which every tilting summand of $V^{\otimes m}$ has at most two Weyl factors; at $m=p^2+p$ the block $\lambda=p^2+p$, with four Weyl factors, appears. The hypothesis $e\ge1$ is needed: for $p\nmid q$ the formula fails, for instance when $(q,p,d)=(4,3,4)$; there the answer of [JNR03] applies instead.

### Proofs

Fix $\lambda$ with two Weyl factors, $(r,a)$ as in (T2), $\mu=\lambda^-$. Let $\ell_i=f^{(i)}x$ ($0\le i\le\lambda$) be the standard basis of $\Delta_{\mathbb{Z}_p}(\lambda)$, so $f\ell_i=(i+1)\ell_{i+1}$, $e\ell_i=(\lambda-i+1)\ell_{i-1}$, and more generally $f^{(t)}\ell_i=\binom{i+t}{t}\ell_{i+t}$ and $e^{(t)}\ell_i=\binom{\lambda-i+t}{t}\ell_{i-t}$. Let $s_j=f^{(j)}y$ ($0\le j\le\mu$) be that of $\Delta_{\mathbb{Z}_p}(\mu)$. Put

$$
\nu=\min_{1\le t\le r}v_p\tbinom{\lambda-r+t}{t}.
$$

**Lemma 7** (the glue is forced). 
$\nu=2$ if $r\le p-1$ and $a=p-1$, and $\nu=1$ otherwise. $T_{\mathbb{Z}_p}(\lambda)$ is isomorphic to the lattice in $\Delta_{\mathbb{Q}_p}(\lambda)\oplus\Delta_{\mathbb{Q}_p}(\mu)$ spanned by the $\ell_i$ and by

$$
\tilde s_j=s_j+p^{-\nu}\tbinom{j+r}{j}\,\ell_{j+r}\qquad(0\le j\le\mu).
$$

*Proof.* 
The value of $\nu$ follows from Kummer's theorem. If $r\le p-1$, then $\lambda-r=(a+1)p-1$, and adding $t\in[1,r]$ to it carries once out of the units digit; it carries a second time exactly when $a+1=p$. If $r=p$, then $\lambda-r=p^2-1$: adding $t<p$ carries twice, while adding $t=p$ carries once.

By (T2), $T=T_{\mathbb{Z}_p}(\lambda)$ contains $\Delta_{\mathbb{Z}_p}(\lambda)$ with quotient $\Delta_{\mathbb{Z}_p}(\mu)$. Since $T\cap\Delta_{\mathbb{Q}_p}(\lambda)=\Delta_{\mathbb{Z}_p}(\lambda)$ and the weight spaces of $\Delta(\lambda)$ are one-dimensional, the lifts of the $s_j$ to $T$ can be chosen of the form $\tilde s_j=s_j+x_j\ell_{j+r}$ with $x_j\in\mathbb{Q}_p$, unique modulo $\mathbb{Z}_p$.

Stability under $f$ gives $(j+r+1)x_j-(j+1)x_{j+1}\in\mathbb{Z}_p$. Stability under $f^{(p)}$ at $j=kp$, for $(k+1)p\le\mu$, gives

$$\tbinom{(k+1)p+r}{p}x_{kp}-\tbinom{(k+1)p}{p}x_{(k+1)p}\in\mathbb{Z}_p.$$

In the range of (T2), $\mu\le p^2-2$, so $k+1\le p-1$ and $\binom{(k+1)p}{p}\equiv k+1$ is a unit; so is $\binom{(k+1)p+r}{p}$, which is $\equiv k+1$ if $r\le p-1$ and $\equiv k+2$ if $r=p$ (and then $\mu=p^2-p-1$, so $k+2\le p-1$). Inside a segment $[kp,(k+1)p-1]$ the factor $j+1$ is a unit, so $x_j\equiv\binom{j+r}{j}\binom{kp+r}{kp}^{-1}x_{kp}$ modulo $\mathbb{Z}_p$. Across segments, $x_{(k+1)p}\equiv\binom{(k+1)p+r}{p}\binom{(k+1)p}{p}^{-1}x_{kp}$, and

$$\tbinom{n+r}{p}\tbinom np^{-1}=\tbinom{n+r}{n}\tbinom{n-p+r}{n-p}^{-1}\qquad(n=(k+1)p)$$

is an identity of rational numbers (both sides equal $\frac{(n+r)!\,(n-p)!}{n!\,(n-p+r)!}$). Hence $x_j\equiv\binom{j+r}{j}x_0$ modulo $\mathbb{Z}_p$ for every $j$, and the lattice is determined by $x_0$.

Stability under $e^{(t)}$ at $j=0$ gives $x_0\binom{\lambda-r+t}{t}\ell_{r-t}\in T$ for $1\le t\le r$, so $v_p(x_0)\ge-\nu$. Suppose $v_p(x_0)\ge1-\nu$. Then $e^{(t)}\tilde s_0\in pT$ for every $t\ge1$ (also for $t>r$, where it vanishes), so the image of $\tilde s_0$ in $T\otimes\mathbb{F}_p$ is a highest weight vector of weight $\mu$. It generates the image of a map $\Delta(\mu)\to T\otimes\mathbb{F}_p$, and the composite with $T\otimes\mathbb{F}_p\to\Delta(\mu)$ is the identity on the generator, so it is an isomorphism and the extension splits. This is impossible, because $T\otimes\mathbb{F}_p=T(\lambda)$ is indecomposable. So $x_0=u\,p^{-\nu}$ with $u$ a unit, and rescaling $y$ makes $u=1$. The lattice so described is $T$ itself, so it is stable under all $f^{(t)}$ and $e^{(t)}$; nothing more has to be checked. (For $f^{(t)}$ this is also visible directly: $f^{(t)}\tilde s_j-\binom{j+t}{t}\tilde s_{j+t}$ vanishes by the identity $\binom{j+r}{j}\binom{j+r+t}{t}=\binom{j+t}{t}\binom{j+t+r}{j+t}$.) Stability under every $e^{(t)}$ and $f^{(t)}$ is also checked by machine in Section 9.
 ∎

**Lemma 8** (the blocks). 
Embed $T_{\mathbb{Z}_p}(\lambda)$ in $B_m\otimes\mathbb{Z}_p$ at levels $k,\dots,k+\lambda$ ($m=\lambda+2k$). Then the cokernel of $q(c+H)+U$ on it is $G_c(m,\lambda)$. The same holds for the simple blocks.

*Proof.* 
Put $N_t=q(c+k+t)$, so $v_p(N_t)=v_t$, and $M=q(c+H)+U$. In the basis of Lemma 7:

- $M\ell_i=N_i\ell_i+(i+1)\ell_{i+1}$;
- $M\tilde s_j=N_{j+r}\tilde s_j+(j+1)\tilde s_{j+1}$ for $j<\mu$; the $\ell$-component is $p^{-\nu}[(j+r+1)\binom{j+r}{j}-(j+1)\binom{j+r+1}{j+1}]\ell_{j+r+1}=0$;
- $M\tilde s_\mu=N_{\mu+r}\tilde s_\mu+u\,\ell_{\mu+r+1}$, where $\mu+r+1=(a+1)p$ and $u=p^{-\nu}\binom{\mu+r}{\mu}(a+1)p$.

By Lucas, $\binom{\mu+r}{\mu}$ is a unit: $\mu+r=(a+1)p-1$ has digits $(a,p-1)$, or $(p-1,p-1)$ when $r=p$. So $v_p(u)=v_p((a+1)p)-\nu$. This is $0$ when $r\le p-1$, and $1$ when $r=p$.

The non-unit subdiagonal entries are:

- on the $\ell$-chain, the $i+1=tp$ with $1\le t\le a+1$, of valuation $1$ except the last, of valuation $\tau$;
- on the $\tilde s$-chain, the $j+1=tp\le\mu$, of valuation $1$. There are $a$ of them if $r\le p-1$, and $a-1$ if $r=p$.

Solving the unit subdiagonals, the cokernel is generated by the first vector of each segment between them, with one relation at the end of each segment. Write $g_t=\ell_{tp}$ and $h_t=\tilde s_{tp}$, and let $\alpha_t$, $\sigma_t$ be the sums of the $v$'s over the segments, so that $\sum_t\alpha_t=A$, $\sum_t\sigma_t=A'$ and the last $\alpha_t$ is $\alpha$. After rescaling the generators by units, the relations are:

- $p^{\alpha_t}g_t+p\,g_{t+1}$ on the $\ell$-chain, the last link having $p^{\tau}$ instead of $p$;
- $p^{\alpha}g_{a+1}$ at the end of the $\ell$-chain;
- $p^{\sigma_t}h_t+p\,h_{t+1}$ on the $\tilde s$-chain;
- at the end of the $\tilde s$-chain, $p^{\sigma}h_{\rm last}+p^{v_p(u)}g_{a+1}$.

Every entry has valuation $\ge1$, so the relation matrix is $pM'$ with $M'$ integral.

If $r\le p-1$ the last relation has a unit coefficient on $g_{a+1}$. Eliminating $g_{a+1}$ turns the last link of the $\ell$-chain into $p^{\tau+\sigma_a}h_a$ and the end relation into $p^{\alpha+\sigma_a}h_a$. In $M'$ the links with coefficient $1$ form $a$ units on the $\ell$-chain and $a$ on the $\tilde s$-chain, in distinct rows and columns. Clearing them (column operations along each chain, then row operations) splits off $I_{2a}$. The $2\times2$ matrix that remains, on the rows of the last link of the $\ell$-chain and of the end relation $p^{\alpha+\sigma_a}h_a$, and on the columns $g_0,h_0$, is upper triangular with diagonal valuations $E_{11}-1$, $E_{22}-1$ and corner $E_{12}-1$.

If $r=p$ the $\tilde s$-chain has $a-1$ unit links and its end relation has a unit coefficient on $g_{a+1}=g_p$ in $M'$. These give $2a$ units again, and clearing them leaves the same $2\times2$ matrix.

So the relation matrix is equivalent to $pI_{2a}\oplus\begin{pmatrix}p^{E_{11}}&\ast\,p^{E_{12}}\\0&p^{E_{22}}\end{pmatrix}$, with a unit $\ast$. The Smith form of such a matrix is $(p^{x},p^{E_{11}+E_{22}-x})$ with $x$ the least of the three valuations, and this is $G_c(m,\lambda)$.

When $c=k=0$, $N_0=0$: the column $g_0$ is zero and gives the free summand, and what remains on $h_0$ are the relations $p^{E_{12}}$ and $p^{E_{22}}$. The simple blocks are single chains. When $\lambda+1=(a+1)p\le p^2$ the chain has $a$ non-unit subdiagonal entries, $i+1=tp$ with $1\le t\le a\le p-1$, each of valuation $1$. The same elimination gives $(\mathbb{Z}/p)^a\oplus\mathbb{Z}/p^{A-a}$.

When $a+1<p$ we have $E_{12}\le E_{22}$ (since $\alpha\ge1$) and $E_{12}\le E_{11}$, because $A-\alpha=A'+\sum_{t<r}v_t\ge A'+1$. So $x=E_{12}$ and $y=A-1-a$.
 ∎

*Proof of Theorems G and F.* 
Combine (T1)–(T3), Lemma 7 and Lemma 8. For $m\le p^2+p-1$ every $\lambda\le m$ is simple or has two Weyl factors, by (T2).
 ∎

**Example 9**. 
For $p=q=3$ and $d=4$: Theorem A gives the pieces $X(4,0)$, $X(3,1)^4$, $X(2,2)^6$, $X(1,3)^4$, $X(0,4)$, and Theorem F gives $\operatorname{Syl}_3K(H(4,3))\cong(\mathbb{Z}/3)^2\oplus(\mathbb{Z}/3^2)^{7}\oplus(\mathbb{Z}/3^3)^{8}\oplus(\mathbb{Z}/3^4)^{17}$, which is the group we computed.

## 7. The prime $2$

For $p=2$ the blocks are the families of [DST], and [DST] computes them for every family and every power of $2$. This gives the whole $2$-part of $K(H(d,q))$ for every $d$ and every even $q$.

For a family $\lambda\ge1$ write $\lambda+1=2^{\theta}+\sum_{t\in I}2^t$ with $I\subseteq\{0,\dots,\theta-1\}$, $\Theta=2^\theta$, $h_t=\mathrm{next}(t)-t$ (with $\mathrm{next}(t)$ the next element of $I\cup\{\theta\}$), $o_D=\sum_{t\in D}2^t$ for $D\subseteq I$, and $\kappa(a,b)=v_2\binom{a+b}{a}$. Following [DST, §3.4] put

$$
X^{(\alpha)}(\lambda,i)=\operatorname{coker}\big(f+2^\alpha(D_\lambda+i)\ \text{on}\ T_{\mathbb{Z}_2}(\lambda)\big)\qquad(\alpha\ge1,\ i\ge0),
$$

where $D_\lambda$ is the floor operator $(\lambda-h)/2$. By [DST, Theorem D, Proposition 5.4, Theorem 7.10], which are stated and proved for every $\alpha\ge1$,

$$
X^{(\alpha)}(\lambda,i)\cong\bigoplus_{b=1}^{\theta-1}\big(\mathbb{Z}/2^b\big)^{2^{|I|+\theta-1-b}}\oplus\bigoplus_{D\subseteq I}\mathbb{Z}/2^{\,\theta+\alpha\Theta+\kappa(i-1,\Theta)+\hat y_D}\qquad(i\ge1),
$$

where $\hat y$ is the integer antitonic fit [DST, §1.2], in the order of increasing $o_D$, of the clocks

$$
x_D=R_{i-1}(D)-R_{i-1+\Theta}(I\setminus D),\qquad R_\mu(E)=\sum_{t\in E}\big(h_t-\alpha2^t\big)-\kappa(\mu,o_E).
$$

For $i=0$ the summand $D=\emptyset$ is $\mathbb{Z}_2$, and the others are $\mathbb{Z}/2^{\theta+\alpha\Theta+\hat y^\sharp_D}$, with $\hat y^\sharp$ the fit of $x^\sharp_D=R^\sharp(D)-R^\sharp(I\setminus D)$, $R^\sharp(E)=\sum_{t\in E}(h_t-\alpha2^t)-\kappa(\Theta-1,o_E)$, over $D\ne\emptyset$. For $\lambda=0$, $X^{(\alpha)}(0,i)=\mathbb{Z}/2^{\alpha+v_2(i)}$ ($\mathbb{Z}_2$ if $i=0$). Let $m_\lambda(n)$ be the multiplicity of $T(\lambda)$ in $V^{\otimes n}$ in characteristic $2$ [DST, §1.2, Theorem 3.6].

**Theorem H** (the prime $2$). 
Let $q$ be even, $e=v_2(q)$, $m\ge0$ and $c\ge0$. Then

$$
\mathbb{Z}_2^{\,[c=0]}\oplus\operatorname{Syl}_2X_q(m,c)\;\cong\;\bigoplus_{\lambda}X^{(e)}\big(\lambda,\,c+\tfrac{m-\lambda}{2}\big)^{m_\lambda(m)}.
$$

Consequently, for every $d\ge1$,

$$
\mathbb{Z}_2\oplus\operatorname{Syl}_2K\big(H(d,q)\big)\;\cong\;\bigoplus_{j=0}^{d}\ \bigoplus_{\lambda}X^{(e)}\big(\lambda,\,j+\tfrac{d-j-\lambda}{2}\big)^{\binom dj(q-2)^j\,m_\lambda(d-j)} .
$$

*Proof.* 
By (T1) for $p=2$ [DST, Theorem 3.6], $B_m\otimes\mathbb{Z}_2=V^{\otimes m}=\bigoplus_\lambda T_{\mathbb{Z}_2}(\lambda)^{m_\lambda(m)}$ as $\mathrm{Dist}$-modules. On a summand $T(\lambda)$, placed at the levels $k=(m-\lambda)/2,\dots,k+\lambda$, a vector of weight $h$ has $H=(m-h)/2=k+D_\lambda$, so $q(c+H)+U=f+q(c+k+D_\lambda)$. Write $q=2^eu$ with $u$ odd. The proof of Lemma 2 applies verbatim to any lattice graded by the floor on which $f$ raises the floor by one; it rescales the floors by units and turns $f+2^eu(D_\lambda+i)$ into $f+2^e(D_\lambda+i)$. So the cokernel on the summand is $X^{(e)}(\lambda,c+k)$. The second statement follows from Theorem A.
 ∎

For $q=2$ only $j=0$ survives, $e=1$, and this is the Main Theorem of [DST]. For $e\ge1$ arbitrary, the theorem was checked against the Smith forms of $q(c+H)+U$ on $B_m$ in $384$ cases ($m\le11$, $e\le4$, $c\le4$) and against the full Laplacians of $H(d,q)$ for $(d,q)=(3,4),(4,4),(3,6),(3,8),(2,12),(2,16),(3,10)$. Two controls fail: using $\alpha=1$ instead of $\alpha=e$ changes the answer in all $112$ cases with $e\ge2$ tried, and omitting the antitonic fit changes it in $16$ of $128$.

## 8. The remaining blocks: a conjecture

For a prime $p$, $\lambda\ge0$, $i\ge0$ and $e\ge1$ put

$$
Y_p(\lambda,i,e)=\operatorname{coker}\big(f+p^{e}(D_\lambda+i)\ \text{on}\ T_{\mathbb{Z}_p}(\lambda)\big),
$$

with $D_\lambda=(\lambda-h)/2$ the floor operator, as in Section 7. By (T1), and by Lemma 2 applied as in the proof of Theorem H, for every $m$ and $c$

$$
\mathbb{Z}_p^{\,[c=0]}\oplus\operatorname{Syl}_pX_q(m,c)\;\cong\;\bigoplus_\lambda Y_p\big(\lambda,\,c+\tfrac{m-\lambda}2,\,v_p(q)\big)^{n_\lambda(m)},
$$

where $n_\lambda(m)$ is the multiplicity of $T(\lambda)$ in $V^{\otimes m}$. So everything comes down to the groups $Y_p(\lambda,i,e)$. Theorem G computes them for $\lambda\le p^2+p-1$, and Theorem H for $p=2$.

Two things are known about $Y_p(\lambda,i,e)$ for every $\lambda$. Write $\lambda+1=\sum_{t=0}^{k}d_tp^t$ with $0\le d_t\le p-1$ and $d_k\ne0$, and put $I(\lambda)=\{t<k:d_t\ne0\}$.

- *The number of cyclic summands* (the free summand included when $i=0$) is the number of Jordan blocks of $f$ on $T(\lambda)$ over $\mathbb{F}_p$, because $p^e(D_\lambda+i)\equiv0$. For $\lambda\ge p-1$ the module $T(\lambda)$ is projective over the first Frobenius kernel [Jan03, Part II, Chapter E], so $f$ acts freely over $\mathbb{F}_p[f]/(f^p)$ and the number is $\dim T(\lambda)/p$.
- *The number of Weyl factors* of $T(\lambda)$ is $2^{|I(\lambda)|}$. Indeed, by Donkin's theorem $T(p-1+r'+pb)\cong T(p-1+r')\otimes T(b)^{[1]}$ ($0\le r'\le p-1$), and $\chi(p-1)\cdot\chi(n)(z^p)=\chi(pn+p-1)$, while for $r'\ge1$ the character of $T(p-1+r')$ is $\chi(p-1)(z^{r'}+z^{-r'})$; so each Weyl factor $\Delta(n)$ of $T(b)$ gives one Weyl factor of $T(\lambda)$ if $r'=0$ and two, $\Delta(pn+p-1\pm r')$, if $r'\ge1$. Since $\lambda+1=r'+p(b+1)$, this is the recursion $|I(\lambda)|=[r'\ne0]+|I(b)|$, starting from $T(\lambda)=\Delta(\lambda)$ for $\lambda\le p-2$.

**Conjecture I**. 
Let $p$ be a prime, $\lambda\ge0$, $i\ge0$ and $e\ge1$, and let $k$ and $I(\lambda)$ be as above. Then:

- (i) exactly $2^{|I(\lambda)|}$ of the cyclic summands of $Y_p(\lambda,i,e)$ have order larger than $p^k$ (the free summand, when $i=0$, counting as one of them), one for each Weyl factor of $T(\lambda)$;
- (ii) the others have order at most $p^k$, and together they form a group that does not depend on $i$ or on $e$.

The conjecture holds whenever the groups are known. For $\lambda\le p^2+p-1$ it follows from Theorem G: there $k\le2$, the small summands are $(\mathbb{Z}/p)^{a}$ or $(\mathbb{Z}/p)^{2a}$, and the large ones are the $\mathbb{Z}/p^{x}$, $\mathbb{Z}/p^{y}$ or $\mathbb{Z}/p^{A-a}$ of the block; since every $v_t\ge1$, one has $A'\ge\lambda^-+1$, $\alpha\ge r$ and $A-\alpha\ge\lambda+1-r$, which gives $E_{11},E_{12},E_{22}\ge k+1$ and $A-a\ge k+1$. For $p=2$ it follows from Theorem H: the large summands are the "big clocks" indexed by $D\subseteq I$, and the small ones are $\bigoplus_{b<\theta}(\mathbb{Z}/2^b)^{2^{|I|+\theta-1-b}}$. We checked both statements on the formulas: $9045$ groups for $p=2$ ($\lambda\le200$, $e\le5$, $i\le8$) and $4704$ for $p\in\{3,5,7\}$ ($\lambda\le p^2+p-1$), with no exception; and the count of Weyl factors for $p\le5$, $\lambda\le120$.

The first block outside both cases is $\lambda=12$ for $p=3$ ($\lambda+1=111_3$, four Weyl factors). Here $\dim T(12)=36$, $k=2$ and $I=\{0,1\}$, so the conjecture predicts $(\mathbb{Z}/3)^8$ and four summands of order at least $27$. The block occurs once in $V^{\otimes12}$, at the top, and every other block of $V^{\otimes12}$ has $\lambda\le10$ and is given by Theorem G. So we computed the Smith form of $q(c+H)+U$ on $B_{12}$ for $q\in\{3,6\}$ and $0\le c\le3$, and removed the blocks $\lambda\le10$. We stated the conjecture after seeing the cell $(q,c)=(3,0)$ alone, and sealed a prediction for the other seven (Section 9). The block is:

| c | block λ=12, for q=3 and for q=6 |
|---|---|
| 0 | $\mathbb{Z}_3\oplus(\mathbb{Z}/3)^8\oplus\mathbb{Z}/3^{7}\oplus\mathbb{Z}/3^{10}\oplus\mathbb{Z}/3^{12}$ |
| 1, 2 | $(\mathbb{Z}/3)^8\oplus(\mathbb{Z}/3^{9})^2\oplus(\mathbb{Z}/3^{13})^2$ |
| 3 | $(\mathbb{Z}/3)^8\oplus\mathbb{Z}/3^{8}\oplus\mathbb{Z}/3^{10}\oplus\mathbb{Z}/3^{12}\oplus\mathbb{Z}/3^{14}$ |

All seven predictions hold. The large summands depend on $c$; we have no formula for them. For two Weyl factors their exponents are the numbers $x,y$ of Theorem G, and for $p=2$ they are the big clocks of [DST]; we expect a common form.

## 9. Verification

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
- Theorem G against direct computation (version 2): the predicted pieces equal the Smith forms of $q(c+H)+U$ computed on $B_m$ in $154$ cases ($p=3$, $m\le7$; $p=5$, $m\le10$; $e\in\{1,2\}$; $0\le c\le6$) and in $5$ cases with $p=3$, $m=8=3p-1$. The full groups for $p=q=3$ and $d=5,\dots,8$ computed in version 1 from the full Laplacian (Section 10) are reproduced exactly.
- Corollary 6: $\dim_{\mathbb{F}_p}\operatorname{coker} U$ on $B_m$ computed by ranks agrees with the count of Jordan blocks in $37$ cases ($p\in\{3,5,7\}$, $m\le12$); the characteristic-$0$ count $\binom m{\lfloor m/2\rfloor}$ differs in $7$ of them.
- Theorem G up to $m\le p^2+p-1$ (version 3):
  - the formula of Lemma 8 against the Smith form on the model lattice of Lemma 7, for $p\in\{5,7\}$ and every $\lambda\le p^2-1$, $c=k=0$ included: $216$ of $216$; the split lattice differs in $52$ of $52$; the lattices of Lemma 7 are stable under every $e^{(t)}$ and $f^{(t)}$ for every $\lambda\le p^2-1$ with two Weyl factors, $p\in\{5,7\}$ ($52$ lattices);
  - a first sealed prediction (MD5 `9ef6b4fec30a93192b0de995519d75f3`), written after the formula was derived and before the computation: $36$ pieces ($p=3$, $m\in\{9,10\}$, $q\in\{12,15,21\}$, $5\le c\le8$; $p=2$, $m=4$, $q\in\{6,8,10\}$, $5\le c\le8$), the four full groups $\operatorname{Syl}_3K(H(10,3))$, $\operatorname{Syl}_3K(H(9,6))$, $\operatorname{Syl}_2K(H(4,6))$, $\operatorname{Syl}_2K(H(4,10))$, and $\operatorname{Syl}_2K(H(4,6))$ again from its full Laplacian: $41$ agreements;
  - a second one (MD5 `a092c60102cfca163c8449b60680b1e1`): $18$ pieces ($p=3$, $m=11$, $q\in\{12,15\}$, $4\le c\le6$; $p=2$, $m=5$, $q\in\{6,8,10\}$, $4\le c\le7$), the full groups $\operatorname{Syl}_3K(H(11,3))$, $\operatorname{Syl}_2K(H(5,4))$, $\operatorname{Syl}_2K(H(5,6))$, and $\operatorname{Syl}_2K(H(5,4))$ from its full Laplacian: $22$ agreements;
  - the row $d=9$ of Section 10, which version 2 did not explain, is reproduced exactly.
- Theorem H: $384$ pieces against Smith forms on $B_m$ ($m\le11$, $e\le4$, $c\le4$) and seven full Laplacians, with the two controls described after the theorem.
- Conjecture I: on the formulas of Theorems G and H, $9045$ groups for $p=2$ ($\lambda\le200$, $e\le5$, $i\le8$) and $4704$ for $p\in\{3,5,7\}$, with no exception; the number of summands equals $\dim T(\lambda)/p$ in $286$ of $286$ cases; the count $2^{|I(\lambda)|}$ of Weyl factors from the characters for $p\le5$, $\lambda\le120$ ($363$ cases). For the block $\lambda=12$, $p=3$: a third sealed prediction (MD5 `a739d9c18622ab0c5dfc811f4cbd49f7`), written after one cell, for seven cells; seven agreements.

## 10. Data for $p=q=3$

For $q=p=3$ the computed groups, written as $(n_1,n_2,\dots)$ with $n_v$ the number of factors $\mathbb{Z}/3^v$, are:

| d | (n_1, n_2, ...) |
|---|---|
| 5 | $(12,10,16,53,5)$ |
| 6 | $(38,37,36,117,24,16,6)$ |
| 7 | $(86,105,127,285,85,63,41)$ |
| 8 | $(250,211,286,1078,174,133,174,8)$ |
| 9 | $(942,412,624,3339,449,292,495,133,84,37,9)$ |
| 10 | $(3314,1388,1768,7310,1690,1364,1388,1392,316,190,74)$ |
| 11 | $(11035,4345,5127,11339,10099,4994,4432,7162,704,419,416)$ |

Theorem G gives every row exactly. In version 2 the row $d=9$ was outside the range: its piece $X_3(9,0)$ contains the block $\lambda=9$, which has $a=p-1$, and the version-2 formula, with glue $1/p$, gave $(942,414,623,3339,448,293,495,134,84,36,9)$. With the glue $1/p^2$ of Lemma 7 and the minimum in the definition of $G_c(m,\lambda)$ the row comes out right. The rows $d=10$ and $d=11$ were computed piece by piece and assembled by Theorem A; both were predicted before they were computed (the first two sealed predictions of item 9 of Section 9 contain them).

## Provenance

The results were found on the night of 12–13 October 2026 by an AI system, Claude (Anthropic), working for the author: it chose the problem after a search of the literature, wrote the computations, found the formulas, sealed and checked the predictions, and found the proofs; it also found, when checking the literature before publication, that Theorem A is [JNR03, Theorem 13]. Version 2 was written later the same night, also by Claude: the Glue Conjecture of version 1 was proved and extended (Theorems F, G) by writing down the tilting lattices, and the closed form of $N$ (Corollary 6) was proved. Version 3 was written later the same night, also by Claude: Theorem G was extended to $m\le p^2+p-1$ and every prime by computing the glue of the blocks with $a=p-1$ (denominator $p^2$), Theorem H was obtained by reading the results of [DST], which are stated for every power of $2$, at $2^{v_2(q)}$, and Conjecture I was stated from one computed cell. The author takes responsibility for the paper. To the best of our knowledge, after a search of the works citing [JNR03] and of arXiv, Theorems B, C (for $e\ge1$), D, E, F, G and H, Corollary 6 and Conjecture I are new; version 1 also claimed the case $e=0$ of Theorem C, which follows from [JNR03, Theorem 2]. Theorem A is due to Jacobson, Niedermaier and Reiner. The tilting theory used in Sections 6 and 8, including the count of Weyl factors, is classical [Don93, Jan03], and so is the decomposition of tensor powers in the proof of Corollary 6.

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

