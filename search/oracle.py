import sys
def add(s,t):
    n=max(len(s),len(t)); s=s+[0]*(n-len(s)); t=t+[0]*(n-len(t)); return [a+b for a,b in zip(s,t)]
def mullin(A,B,h): return add([A*c for c in h+[0]],[B*c for c in [0]+h])
def mpow(D,n):
    r=[1]
    for _ in range(n): r=mullin(D,D,r)
    return r
def bern(A,B,D,cs):
    if len(cs)==1: return cs[:]
    return add([cs[0]*c for c in mpow(D,len(cs)-1)], mullin(A,B,bern(A,B,D,cs[1:])))
def search(cs,A,B,D,depth=0):
    if all(c>0 for c in bern(A,B,D,cs)): return "PolyPos.Cert.leaf"
    if depth>40: raise SystemExit("no certificate")
    l=search(cs,2*A,A+B,2*D,depth+1); r=search(cs,A+B,2*B,2*D,depth+1)
    return f"(PolyPos.Cert.split {l} {r})"
cs=eval(sys.argv[1]); A,B,D=map(int,sys.argv[2:5])
print(search(cs,A,B,D))
