"""Independent exact checks for the additional publication calculations."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json
import random
from exact_utils import bareiss, matrix

ROOT = Path(__file__).resolve().parent

def mul(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]

def transpose(a):
    return list(map(list,zip(*a)))

def transitive(n):
    return [[(j>i)-(j<i) for j in range(n)] for i in range(n)]

def trace4_check(s):
    n=len(s)
    square=mul(s,s)
    trace4=sum(x*x for row in square for x in row)
    d4=sum(bareiss([[s[i][j] for j in u] for i in u])==9
           for u in combinations(range(n),4))
    choose4=0 if n<4 else n*(n-1)*(n-2)*(n-3)//24
    assert trace4 == 2*(n*(n-1)//2)**2-4*choose4-32*d4
    signs=[1]+[s[0][j] for j in range(1,n)]
    switched=[[signs[i]*s[i][j]*signs[j] for j in range(n)] for i in range(n)]
    cycles=sum(switched[i][j]==switched[j][k]==switched[k][i]
               for i,j,k in combinations(range(1,n),3))
    assert (d4==0)==(cycles==0)

def run():
    determinant_cases=0
    matrix_cases=0
    carousel_cases=0
    for n in range(1,25):
        tmat=transitive(n)
        for t in (F(-1),F(0),F(1,3),F(1),F(2)):
            a,b=t.numerator,t.denominator
            actual=F(bareiss([[b*(i==j)+a*tmat[i][j] for j in range(n)]
                              for i in range(n)]),b**n)
            assert actual==((1+t)**n+(1-t)**n)/2
            determinant_cases+=1
        k=[[1 if i+j<=n else 0 if i+j==n+1 else (-1)**(i+j-n-2)
            for j in range(1,n+1)] for i in range(1,n+1)]
        order=list(range(0,n,2))+list(reversed(range(1,n,2)))
        m=[[(-1)**i*k[i][n-1-j] for j in range(n)] for i in range(n)]
        assert [[m[i][j] for j in order] for i in order]==tmat
        z=[[0]*n for _ in range(n)]
        for j in range(n-1):z[j+1][j]=1
        z[0][n-1]=-1
        assert mul(mul(transpose(z),tmat),z)==tmat
        k2=mul(k,k)
        signed=[(-1)**i for i in range(n)]
        transformed=[[signed[i]*k2[i][j]*signed[j] for j in order] for i in order]
        assert transformed==mul(tmat,transpose(tmat))
        matrix_cases+=1
        if n%2:
            for i in range(n):
                for j in range(n):
                    delta=(((n+1)//2)*(j-i))%n
                    carousel=0 if i==j else (1 if 1<=delta<=n//2 else -1)
                    assert signed[i]*tmat[i][j]*signed[j]==carousel
            carousel_cases+=1
    four_cases=0
    for bits in range(64):
        s=matrix(4,bits)
        a,b,c,d,e,f=s[0][1],s[0][2],s[0][3],s[1][2],s[1][3],s[2][3]
        assert bareiss(s)==(a*f-b*e+c*d)**2
        four_cases+=1
    trace_cases=0
    for n in range(1,6):
        for bits in range(1<<(n*(n-1)//2)):
            trace4_check(matrix(n,bits));trace_cases+=1
    rng=random.Random(20261019)
    for n in range(6,14):
        for _ in range(20):
            trace4_check(matrix(n,rng.getrandbits(n*(n-1)//2)));trace_cases+=1
    report={"result":"passed","rational_determinant_cases":determinant_cases,
            "comparison_matrix_and_signed_shift_orders":matrix_cases,
            "explicit_carousel_isomorphism_orders":carousel_cases,
            "four_vertex_determinant_cases":four_cases,
            "trace4_and_equality_cases":trace_cases,
            "scope":"Exact finite identities only; not an asymptotic or peer-review certification."}
    (ROOT/"qa").mkdir(exist_ok=True)
    (ROOT/"qa/publication_identity_checks.json").write_text(json.dumps(report,indent=2),encoding="utf-8")
    print(json.dumps(report))

if __name__=="__main__":
    run()

