"""Small exact-arithmetic helpers; Python standard library only."""

from fractions import Fraction as F

from functools import lru_cache

from itertools import combinations



def matrix(n, bits):
    s = [[0]*n for _ in range(n)]
    for h, (i, j) in enumerate(combinations(range(n), 2)):
        s[i][j] = 1 if (bits >> h) & 1 else -1
        s[j][i] = -s[i][j]
    return s

def mm(a, b):
    return [
        [sum((x*y for x, y in zip(row, col)), F(0))
         for col in zip(*b)]
        for row in a
    ]

def invert(a):
    n = len(a)
    z = [list(row) + [F(i == j) for j in range(n)]
         for i, row in enumerate(a)]
    determinant = F(1)
    for i in range(n):
        pivot = next(j for j in range(i, n) if z[j][i])
        if pivot != i:
            z[i], z[pivot] = z[pivot], z[i]
            determinant = -determinant
        value = z[i][i]
        determinant *= value
        z[i] = [x/value for x in z[i]]
        for j in range(n):
            if i != j and z[j][i]:
                value = z[j][i]
                z[j] = [x-value*y for x, y in zip(z[j], z[i])]
    return [row[n:] for row in z], determinant

def principal_determinants(s):
    n = len(s)

    @lru_cache(None)
    def pfaff(u):
        if not u:
            return 1
        return sum(
            (-1)**(j+1)*s[u[0]][u[j]]*pfaff(u[1:j]+u[j+1:])
            for j in range(1, len(u))
        )

    return {
        sum(1 << i for i in u): pfaff(u)**2
        for k in range(0, n+1, 2)
        for u in combinations(range(n), k)
    }

def bareiss(a):
    n = len(a)
    if not n:
        return 1
    a = [r[:] for r in a]
    sign, last = 1, 1
    for k in range(n-1):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        p = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                numerator = p*a[i][j]-a[i][k]*a[k][j]
                assert numerator % last == 0
                a[i][j] = numerator//last
        for i in range(k+1, n):
            a[i][k] = 0
        last = p
    return sign*a[-1][-1]

def perm(a):
    n = len(a)
    dp = [0]*(1 << n)
    dp[0] = 1
    for mask in range(1, 1 << n):
        row = mask.bit_count()-1
        dp[mask] = sum(a[row][j]*dp[mask ^ (1 << j)]
                       for j in range(n) if mask >> j & 1)
    return dp[-1]
