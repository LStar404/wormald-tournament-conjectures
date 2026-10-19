"""Independent formal-series and weighted-row checks; standard library only."""
from fractions import Fraction as F
from itertools import permutations
from math import factorial,ceil
from pathlib import Path
import random,json
from exact_utils import matrix

ROOT=Path(__file__).resolve().parent
ORDER=9

class Poly(dict):
    """A polynomial in independent indeterminates b and h over the rationals."""
    def __add__(self,other):
        if not isinstance(other,Poly):other=constant(other)
        result=Poly(self)
        for m,c in other.items():result[m]=result.get(m,F(0))+c
        return Poly({m:c for m,c in result.items() if c})
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.items()})
    def __sub__(self,other):return self+-constant(other) if not isinstance(other,Poly) else self+-other
    def __rsub__(self,other):return constant(other)+-self
    def __mul__(self,other):
        if not isinstance(other,Poly):other=constant(other)
        result=Poly()
        for (i,j),c in self.items():
            for (k,l),e in other.items():
                m=(i+k,j+l);result[m]=result.get(m,F(0))+c*e
        return Poly({m:c for m,c in result.items() if c})
    __rmul__=__mul__
    def __truediv__(self,other):return self*F(1,other)

def constant(c):return Poly({(0,0):F(c)}) if c else Poly()
def series(c=0):return [constant(c)]+[Poly() for _ in range(ORDER)]
def plus(a,b):return [x+y for x,y in zip(a,b)]
def scale(a,c):return [x*c for x in a]
def times(a,b):
    return [sum((a[j]*b[k-j] for j in range(k+1)),Poly()) for k in range(ORDER+1)]
def inverse(a):
    assert a[0]==constant(1)
    out=series(1)
    for k in range(1,ORDER+1):
        out[k]=-sum((a[j]*out[k-j] for j in range(1,k+1)),Poly())
    return out

def formal_coefficients():
    b=Poly({(1,0):F(1)});h=Poly({(0,1):F(1)})
    da=series();db=series();p=series()
    for k in range(1,ORDER//2+1):
        da[2*k]=constant(F((-1)**k,2*k+1))
        db[2*k]=constant(F(1,2*k+1))
    for j in range(1,(ORDER-1)//4+1):
        p[4*j+1]=constant(F(-1,2*j+1))
    # Expand the addition identities directly, rather than differentiating log.
    numerator=series();denominator=series();pb=series(1);pa=series(1)
    for k in range(ORDER+1):
        numerator=plus(numerator,scale(pb,(b if k%2 else constant(1))/factorial(k)))
        coefficient=constant((-1)**(k//2)) if k%2==0 else h*(-(-1)**((k-1)//2))
        denominator=plus(denominator,scale(pa,coefficient/factorial(k)))
        pb=times(pb,db);pa=times(pa,da)
    exponential=series();power=series(1)
    for k in range(ORDER+1):
        exponential=plus(exponential,scale(power,F(1,factorial(k))))
        power=times(power,p)
    result=times(times(exponential,numerator),inverse(denominator))
    a2=(b-h)/3
    a4=(b+h)/5+(2+h*h-b*b+(b-h)*(b-h))/18
    expected={0:constant(1),1:Poly(),2:a2,3:Poly(),4:a4,
              5:constant(F(-1,3)),7:-a2/3,9:-a4/3-constant(F(1,5))}
    for k,value in expected.items():assert result[k]==value,(k,result[k],value)
    return {str(k):{str(m):str(c) for m,c in value.items()} for k,value in expected.items()}

def permanent(a):
    n=len(a)
    return sum((__import__("functools").reduce(lambda x,ij:x*a[ij[0]][ij[1]],
                  enumerate(p),F(1)) for p in permutations(range(n))),F(0))

def cofactor(a,row,col):
    return permanent([[v for j,v in enumerate(r) if j!=col]
                      for i,r in enumerate(a) if i!=row])

def row_checks():
    rng=random.Random(2026101903)
    cases=movements=zero_inputs=0
    for n in range(1,6):
        for _ in range(32):
            a=[[F(rng.randrange(5),4) for _ in range(n)] for _ in range(n)]
            before=permanent(a)
            zero_inputs+=before==0
            targets=[ceil(sum(row)) for row in a]
            for i,row in enumerate(a):
                needed=targets[i]-sum(row)
                for j in range(n):
                    amount=min(1-row[j],needed)
                    row[j]+=amount;needed-=amount
                assert needed==0
                while True:
                    fractional=[j for j in range(n) if row[j] not in (0,1)]
                    if len(fractional)<2:break
                    x,y=fractional[:2]
                    if cofactor(a,i,x)<cofactor(a,i,y):x,y=y,x
                    old=permanent(a)
                    amount=min(1-row[x],row[y])
                    row[x]+=amount;row[y]-=amount
                    assert permanent(a)>=old
                    movements+=1
                assert all(v in (0,1) for v in row)
                assert sum(row)==targets[i]
            after=permanent(a)
            assert after>=before
            if 0 in targets:assert before==after==0
            cases+=1
    # An actual augmented tournament can have permanent zero: the new vertex
    # points to all old vertices, so its incoming column is identically zero.
    a=[[0,1,0,0],[0,0,1,0],[1,0,0,0],[1,1,1,0]]
    assert permanent(a)==0
    return dict(weighted_row_cases=cases,exact_mass_transfers=movements,
                zero_permanent_inputs=zero_inputs,augmented_zero_witness=True)

def odd_moment_checks():
    def mul(a,b):
        return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
    def norms(s):
        current=[[int(i==j) for j in range(len(s))] for i in range(len(s))]
        result={}
        for p in range(1,8):
            current=mul(current,s)
            result[p]=sum(x*x for row in current for x in row)
        return result
    cases=comparisons=0
    rng=random.Random(2026101904)
    for n in range(2,10):
        ref=norms([[(j>i)-(j<i) for j in range(n)] for i in range(n)])
        bits=range(1<<(n*(n-1)//2)) if n<=5 else [
            rng.getrandbits(n*(n-1)//2) for _ in range(20)]
        for value in bits:
            actual=norms(matrix(n,value))
            for p in (1,3,5,7):
                assert actual[p]<=ref[p],(n,value,p)
                comparisons+=1
            assert (actual[3]==ref[3])==(actual[2]==ref[2])
            cases+=1
    return {"all_tournament_odd_moment_cases":cases,
            "exact_odd_moment_inequalities":comparisons,
            "sixth_to_fourth_equality_checks":cases}

def run():
    result={"result":"passed","formal_order":ORDER,
            "exact_symbolic_coefficients":formal_coefficients(),**row_checks(),**odd_moment_checks(),
            "scope":"Exact finite formal-series coefficients and finite row-operation checks; no asymptotic convergence certification."}
    (ROOT/"qa/expansion_and_rounding_checks.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(result))

if __name__=="__main__":run()
