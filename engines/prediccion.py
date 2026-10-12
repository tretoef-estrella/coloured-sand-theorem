#!/usr/bin/env python3
# Theorem B (proved; first stated and sealed as a conjecture): Syl_p K(H(d,p)) for primes p > d:  n_v = sum over j+2k = d+1-v, (j,k) != (0,0), of
#   C(d,j) (p-2)^j * v/(v+2k) * C(v+2k,k)      ([x^k] C(x)^v, C(x) the Catalan series)
import sys, math
def pred(d,p):
    u=p-2; out={}
    for v in range(1,d+2):
        s=0
        for k in range(0,(d+1-v)//2+1):
            j=d+1-v-2*k
            if j<0 or (j==0 and k==0): continue
            s+=math.comb(d,j)*u**j*(v*math.comb(v+2*k,k)//(v+2*k))
        if s: out[v]=s
    return out
if __name__=='__main__':
    d=int(sys.argv[1]); p=int(sys.argv[2]); print(pred(d,p))
