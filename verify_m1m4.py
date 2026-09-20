#!/usr/bin/env python3
# verify_m1m4.py — independent numerical cross-check for JSP-000301 / Erdős #365.
# Verifies that four witness integers m each form a counterexample pair (m, m+1):
# consecutive, both powerful, and neither a perfect square. Deterministic (seeded
# Pollard-rho + deterministic Miller-Rabin). Exit code 0 iff all four pass.
# Note: the formal disproof is the Lean proof; this script is a supplementary,
# independent numerical spot-check of explicit witness pairs.
import math
import random
import sys

random.seed(20260920)  # deterministic runs

WITNESSES = [
    ("m1", 68272646647195749782087, "(23,2) single-cube family"),
    ("m2", 2554676357655727907786187326407, "(7,2) single-cube family"),
    ("m3", 161722121962021270972777151960327, "(23,2) single-cube family"),
    ("m4", 1846854021059276557510708523604613977616827, "(3,7) single-cube family"),
]

_MR_BASES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


def is_prime(n):
    if n < 2:
        return False
    for p in _MR_BASES:
        if n % p == 0:
            return n == p
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in _MR_BASES:
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def _pollard_rho(n):
    if n % 2 == 0:
        return 2
    while True:
        x = random.randrange(2, n)
        y, c, d = x, random.randrange(1, n), 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n:
            return d


def factor(n):
    out = {}
    stack = [n]
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if is_prime(m):
            out[m] = out.get(m, 0) + 1
            continue
        d = _pollard_rho(m)
        stack.append(d)
        stack.append(m // d)
    return out


def is_powerful(n):
    return n != 0 and all(e >= 2 for e in factor(n).values())


def is_square(n):
    r = math.isqrt(n)
    return r * r == n


def main():
    all_ok = True
    for label, m, fam in WITNESSES:
        a, b = m, m + 1
        ok = (b == a + 1) and is_powerful(a) and is_powerful(b) \
            and not is_square(a) and not is_square(b)
        all_ok &= ok
        print(f"{label} = {m}")
        print(f"  factor(m)   = {factor(a)}")
        print(f"  factor(m+1) = {factor(b)}")
        print(f"  powerful(m)={is_powerful(a)} powerful(m+1)={is_powerful(b)} "
              f"square(m)={is_square(a)} square(m+1)={is_square(b)}")
        print(f"  >>> valid counterexample pair: {ok}   [{fam}]")
    print("=" * 60)
    print(f"ALL PASS: {all_ok}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
