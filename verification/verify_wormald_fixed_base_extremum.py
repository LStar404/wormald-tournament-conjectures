"""Finite exact checks of fixed-base spectral comparison and model identities."""
from fractions import Fraction as F
from math import factorial, lcm
from pathlib import Path
import json
from exact_utils import matrix, principal_determinants
from exact_utils import perm
from verify_wormald_hessian_spectral_bridge import carousel

ROOT = Path(__file__).resolve().parent
(ROOT / "qa").mkdir(exist_ok=True)


def regular_tournaments(n):
    target = (n-1)//2
    edges = [(i,j) for i in range(n) for j in range(i+1,n)]
    s = [[0]*n for _ in range(n)]
    out,remaining = [0]*n,[n-1]*n
    def rec(pos):
        if pos == len(edges):
            assert all(v == target for v in out)
            yield [r[:] for r in s]
            return
        i,j = edges[pos]
        remaining[i] -= 1
        remaining[j] -= 1
        for sign,winner in ((1,i),(-1,j)):
            out[winner] += 1
            if all(out[v] <= target <= out[v]+remaining[v] for v in (i,j)):
                s[i][j],s[j][i] = sign,-sign
                yield from rec(pos+1)
            out[winner] -= 1
        remaining[i] += 1
        remaining[j] += 1
    yield from rec(0)


def imul(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]


def norm3(s):
    cubed = imul(imul(s,s),s)
    assert all(cubed[i][j] % 2 for i in range(len(s))
               for j in range(len(s)) if i != j)
    return sum(x*x for row in cubed for x in row)


def rho(s):
    n = len(s)
    dets = principal_determinants(s)
    q = sum(F(v,n**mask.bit_count()) for mask,v in dets.items())
    den = sum(F(v*(-1)**(mask.bit_count()//2),n**mask.bit_count())
              for mask,v in dets.items())
    return q/den,dets


def spectral_checks():
    by_order = []
    for n in (3,5,7):
        tr = [[(j > i)-(j < i) for j in range(n)] for i in range(n)]
        ref,_ = rho(carousel(n))
        ref_norm = norm3(tr)
        cases = equal = strict = 0
        min_gap = None
        for s in regular_tournaments(n):
            value,dets = rho(s)
            d4 = sum(mask.bit_count() == 4 and det == 9 for mask,det in dets.items())
            gap = ref_norm-norm3(s)
            assert value <= ref
            assert (value == ref) == (d4 == 0) == (gap == 0)
            if gap:
                assert gap >= 16 and gap % 16 == 0
                min_gap = gap if min_gap is None else min(min_gap,gap)
                strict += 1
            else:
                equal += 1
            cases += 1
        by_order.append(dict(d=n,regular_cases=cases,equalities=equal,
                             strict_cases=strict,min_positive_sixth_gap=min_gap))
    nonregular = 0
    for n in (3,5):
        for bits in range(1 << (n*(n-1)//2)):
            s = matrix(n,bits)
            degrees = [sum(x == 1 for x in row) for row in s]
            power = F(1)
            for degree in degrees:
                power *= F(2*degree+1,n)
            regular = len(set(degrees)) == 1
            assert (power == 1) == regular
            if not regular:
                assert 0 < power < 1
                scores = [2*v-(n-1) for v in degrees]
                assert sum(scores) == 0 and sum(v*v for v in scores) >= 8
                nonregular += 1
    return dict(exhaustive_regular_spectral_checks=by_order,
                exact_nonregular_kappa_checks=nonregular)


def paths_cycles(a):
    n = len(a)
    dp = [[0]*n for _ in range(1 << n)]
    for i in range(n):
        dp[1 << i][i] = 1
    for mask in range(1,1 << n):
        for j in range(n):
            if mask >> j & 1:
                old = mask ^ (1 << j)
                if old:
                    dp[mask][j] = sum(dp[old][i]*a[i][j] for i in range(n))
    hp = sum(dp[-1])
    cp = [[0]*n for _ in range(1 << n)]
    cp[1][0] = 1
    for mask in range(1,1 << n,2):
        for j in range(1,n):
            if mask >> j & 1:
                old = mask ^ (1 << j)
                cp[mask][j] = sum(cp[old][i]*a[i][j] for i in range(n))
    hc = sum(cp[-1][j]*a[j][0] for j in range(1,n))
    return hp,hc


def blown_adjacency(base,blocks):
    d,m = len(base),len(blocks[0])
    n = d*m
    return [[0 if i == j else (
        int(blocks[i//m][i%m][j%m] == 1) if i//m == j//m
        else int(base[i//m][j//m] == 1)) for j in range(n)] for i in range(n)]


def model_checks():
    actual = model_sums = weighted_bounds = 0
    for d,m,bases in ((3,2,[matrix(3,b) for b in range(8)]),
                       (3,3,[carousel(3)])):
        edge_count = m*(m-1)//2
        total = 1 << (d*edge_count)
        for base in bases:
            hp = hc = 0
            for bits in range(total):
                blocks = [matrix(m,(bits >> (j*edge_count)) & ((1 << edge_count)-1))
                          for j in range(d)]
                h,c = paths_cycles(blown_adjacency(base,blocks))
                hp += h
                hc += c
                actual += 1
            n = d*m
            twice_w = [[0 if i == j else (1 if i//m == j//m else
                2*int(base[i//m][j//m] == 1)) for j in range(n)] for i in range(n)]
            wh,wc = paths_cycles(twice_w)
            assert F(hp,total) == F(wh,2**(n-1))
            assert F(hc,total) == F(wc,2**n)
            wp = perm(twice_w)
            assert wc <= wp
            row_bounds = [(sum(row)+1)//2 for row in twice_w]
            if all(row_bounds):
                exponent = lcm(*row_bounds)
                assert wp**exponent <= 2**(n*exponent)*(
                    __import__("math").prod(factorial(r)**(exponent//r)
                                            for r in row_bounds))
                weighted_bounds += 1
            # Exact normalized relation for adding one uniform random vertex.
            assert 4*F(factorial(n),2**(n+1)) == F(factorial(n),2**(n-1))
            model_sums += 1
    regular_samples = 0
    for bits in range(8):
        base = matrix(3,bits)
        for inner in range(8):
            blocks = [carousel(3) if inner >> j & 1 else
                      [[-v for v in row] for row in carousel(3)] for j in range(3)]
            a = blown_adjacency(base,blocks)
            for i,row in enumerate(a):
                di = sum(v == 1 for v in base[i//3])
                assert sum(row) == 3*di+1
            regular_samples += 1
    return dict(exact_random_blowup_realizations=actual,
                exact_expected_path_cycle_identities=model_sums,
                exact_weighted_bregman_bounds=weighted_bounds,
                exact_regular_block_degree_cases=regular_samples)


def run():
    result = dict(result="passed",**spectral_checks(),**model_checks(),
                  scope="Finite exact spectral, arithmetic, expected-value and "
                        "degree checks. No finite sample certifies asymptotic "
                        "convergence, a uniform block-size threshold or novelty.")
    (ROOT/"qa/wormald_fixed_base_extremum_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False),flush=True)


if __name__ == "__main__":
    run()
