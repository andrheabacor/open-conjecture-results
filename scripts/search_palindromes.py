"""Find sparse multipliers and produce Lucas witnesses for Lean to verify."""

from collections import Counter
from math import gcd


def probable_prime(n):
    if n < 3 or n % 2 == 0:
        return n == 2
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for base in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41):
        if base >= n:
            break
        x = pow(base, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def factor(n):
    if n == 1:
        return []
    if probable_prime(n):
        return [n]
    for p in (2, 3, 5, 7, 11, 13):
        if n % p == 0:
            return [p] + factor(n // p)
    c = 1
    while True:
        x = y = 2
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = gcd(abs(x - y), n)
        if d != n:
            return factor(d) + factor(n // d)
        c += 1


def find_multiplier(min_gap):
    for mid in range(2 * min_gap, 100):
        for a in range(min_gap, mid - min_gap + 1):
            shifts = (0, a, mid, 2 * mid - a, 2 * mid)
            p = sum(10**i for i in shifts)
            if probable_prime(p):
                return shifts, p
    raise ValueError("no multiplier in this search")


def lucas_certificates(p, seen):
    if p < 1024 or p in seen:
        return
    seen.add(p)
    qs = sorted(set(factor(p - 1)))
    g = 2
    while pow(g, p - 1, p) != 1 or any(pow(g, (p - 1) // q, p) == 1 for q in qs):
        g += 1
    print(f"p={p}: .lucas {{ root := {g}, primeFactors := {qs} }}", flush=True)
    for q in qs:
        lucas_certificates(q, seen)


if __name__ == "__main__":
    shifts, p = find_multiplier(9)
    print(f"shifts={shifts}, p={p}", flush=True)
    for seed in (2977792, 40955904, 677707776):
        product = seed * p
        assert str(product) == str(product)[::-1]
        factors = Counter(factor(seed))
        print(f"{seed} * p = {product}, index={1 + sum(factors.values())}, seed factors={factors}")
    lucas_certificates(p, set())
