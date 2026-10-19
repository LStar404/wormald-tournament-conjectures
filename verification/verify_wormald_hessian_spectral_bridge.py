"""Exact implicit-determinant Hessians versus a closed spectral formula."""
from fractions import Fraction as F
from pathlib import Path
from math import comb, factorial
from decimal import Decimal, localcontext
import json
import random
from exact_utils import bareiss
from exact_utils import (
    invert, mm, matrix, principal_determinants,
)

ROOT = Path(__file__).resolve().parent
(ROOT / "qa").mkdir(exist_ok=True)


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def add(a,b):
    return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]


def scale(a,c):
    return [[c*x for x in row] for row in a]


def carousel(n):
    return [[0 if i == j else (1 if 0 < (j-i)%n <= n//2 else -1)
             for j in range(n)] for i in range(n)]


def triangle_flip(s,rng):
    n = len(s)
    triples = [(i,j,k) for i in range(n) for j in range(i+1,n)
               for k in range(j+1,n) if s[i][j] == s[j][k] == s[k][i]]
    if triples:
        i,j,k = rng.choice(triples)
        for u,v in ((i,j),(j,k),(k,i)):
            s[u][v] *= -1
            s[v][u] *= -1


def direct_log_implicit_hessian(s):
    n = len(s)
    # det(I-P diag(exp(t))) is evaluated by every principal minor,
    # independently of the proposed inverse/Hessian formula.
    weights = []
    for mask in range(1 << n):
        keep = [i for i in range(n) if mask >> i & 1]
        determinant = bareiss([[1+s[i][j] for j in keep] for i in keep])
        weights.append(F((-1)**len(keep)*determinant,n**len(keep)))
    assert sum(weights) == 0
    first = [sum(w for mask,w in enumerate(weights) if mask >> i & 1)
             for i in range(n)]
    second = [[sum(w for mask,w in enumerate(weights)
                   if mask >> i & 1 and mask >> j & 1)
               for j in range(n)] for i in range(n)]
    assert first[0] != 0 and all(v == first[0] for v in first)
    return first,second


def run_hessians():
    rng = random.Random(2026101917)
    specs = []
    for n in (3,5):
        for bits in range(1 << (n*(n-1)//2)):
            s = matrix(n,bits)
            if all(sum(row) == 0 for row in s):
                specs.append((f"exhaustive_{n}_{bits}",s))
    for n,count in ((7,24),(9,12),(11,6)):
        s = carousel(n)
        seen = set()
        while len(seen) < count:
            for _ in range(7):
                triangle_flip(s,rng)
            key = tuple(v for row in s for v in row)
            if key not in seen:
                specs.append((f"regular_walk_{n}_{len(seen)}",[row[:] for row in s]))
                seen.add(key)
    for n in (7,9,11,13):
        specs.append((f"carousel_{n}",carousel(n)))
    c3 = carousel(3)
    blowup = [[c3[i%3][j%3] if i//3 == j//3 else c3[i//3][j//3]
               for j in range(9)] for i in range(9)]
    specs.append(("C3_of_C3",blowup))
    count = entries = determinant_checks = 0
    table = []
    paper = {3:F(2),5:F(44,19),7:F(3032,1231),9:F(437584,171769),
             11:F(108859552,41833969),13:F(41637757888,15769379963)}
    for name,s in specs:
        n = len(s)
        assert all(sum(row) == 0 for row in s)
        ii,c = eye(n),scale(s,F(1,n))
        c2 = mm(c,c)
        minus = add(ii,scale(c2,-1))
        mi,_ = invert(minus)
        closed = mm(add(ii,c2),mi)
        first,second = direct_log_implicit_hessian(s)
        dets = principal_determinants(s)
        q = sum(F(v,n**mask.bit_count()) for mask,v in dets.items())
        den = sum(F(v*(-1)**(mask.bit_count()//2),n**mask.bit_count())
                  for mask,v in dets.items())
        rho = q/den
        assert q > 0 and den > 0 and first[0] == -q/n
        for pivot in (range(n) if n <= 7 else (0,n-1)):
            keep = [i for i in range(n) if i != pivot]
            direct = [[(second[i][j]-second[i][pivot]-second[pivot][j]
                        +second[pivot][pivot])/first[pivot]
                       for j in keep] for i in keep]
            expected = [[closed[i][j]-closed[i][pivot]-closed[pivot][j]
                         +closed[pivot][pivot] for j in keep] for i in keep]
            assert direct == expected
            _,hd = invert(direct)
            assert hd == n/(rho*rho) and hd > 0
            entries += (n-1)**2
            determinant_checks += 1
        if name.startswith("carousel_") or n in (3,5):
            assert rho == paper[n]
        if name == "C3_of_C3":
            assert rho == F(5488,2197)
        if name.startswith("carousel_") or name == "C3_of_C3":
            table.append(dict(name=name,d=n,rho=str(rho),
                              hessian_determinant=str(n/(rho*rho))))
        count += 1
    return dict(exact_regular_cases=count,exhaustive_regular_orders=[3,5],
                exact_hessian_entries=entries,
                exact_elimination_coordinate_determinants=determinant_checks,
                source_rational_table_checks=table)


def dsin(x):
    term,total = x,x
    for k in range(1,200):
        term *= -x*x/Decimal((2*k)*(2*k+1))
        total += term
        if abs(term) < Decimal("1e-90"):
            break
    return total


def dcos(x):
    term,total = Decimal(1),Decimal(1)
    for k in range(1,200):
        term *= -x*x/Decimal((2*k-1)*(2*k))
        total += term
        if abs(term) < Decimal("1e-90"):
            break
    return total


def datan(x):
    total = Decimal(0)
    power = x
    for k in range(250):
        term = power/Decimal(2*k+1)
        total += term if k%2 == 0 else -term
        power *= x*x
        if abs(term) < Decimal("1e-90"):
            break
    return total


def expansion_and_monotonicity():
    # Exact rational margins used by the analytic monotonicity proof.
    a = F(26,27)
    lower_tan = a+a**3/3
    upper_hyperbolic_ratio = F(7,9)*F(25,16)
    assert lower_tan > upper_hyperbolic_ratio
    rows = []
    with localcontext() as ctx:
        ctx.prec = 85
        one = Decimal(1)
        h = dsin(one)/dcos(one)
        b = (2*one).exp()
        b = (b-1)/(b+1)
        ll = (one.exp()+(-one).exp())/(2*dcos(one))
        a2 = (b-h)/3
        ell4 = (b+h)/5+(2+h*h-b*b)/18
        a4 = ell4+a2*a2/2
        old = Decimal(0)
        for n in (3,5,7,9,11,13,21,41,81,101,201,401,801,1601):
            x = one/n
            q = ((1+x)**n+(1-x)**n)/2
            den = (1+x*x)**(Decimal(n)/2)*dcos(Decimal(n)*datan(x))
            actual = x.exp()*q/den
            prediction = ll*(1+a2*x*x+a4*x**4-x**5/3)
            assert old < actual < ll
            old = actual
            rows.append(dict(d=n,regular_block_constant=str(actual),
                             d2_gap=str(Decimal(n)**2*(ll-actual)),
                             d6_remainder=str(Decimal(n)**6*(actual-prediction))))
        coefficients = dict(L=str(ll),normalized_d2=str(a2),
                            normalized_d4=str(a4),normalized_d5="-1/3",
                            d2_coefficient=str(ll*a2),d4_coefficient=str(ll*a4))
    return dict(monotonicity_rational_margin=str(lower_tan-upper_hyperbolic_ratio),
                explicit_expansion_coefficients=coefficients,
                decimal_diagnostics=rows)


def run():
    result = dict(result="passed",**run_hessians(),**expansion_and_monotonicity(),
                  scope="Exact rational determinant/implicit-derivative identities "
                        "and exact monotonicity margin. Decimal asymptotic remainders "
                        "are diagnostics; general theorems require the written proof.")
    (ROOT/"qa/wormald_hessian_spectral_bridge_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps({k:v for k,v in result.items() if k != "decimal_diagnostics"}),
          flush=True)


if __name__ == "__main__":
    run()
