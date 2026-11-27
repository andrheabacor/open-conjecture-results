"""Independent checks of the examples and the finite pieces of MSE 5152147."""

from math import isqrt


def direct_sum(x, y):
    """Enumerate positive divisors of y and take each Euclidean remainder."""
    return sum(x % d for d in range(1, y + 1) if y % d == 0)


def sieve_sums(x, largest_y):
    """For each d, add x - d floor(x/d) to the total at every multiple of d."""
    sums = [0] * (largest_y + 1)
    for d in range(1, largest_y + 1):
        remainder = x - d * (x // d)
        for multiple in range(d, largest_y + 1, d):
            sums[multiple] += remainder
    return sums


def witnesses(x):
    direct = [direct_sum(x, y) for y in range(x)]
    sieved = sieve_sums(x, x - 1)
    assert direct == sieved

    by_root = {y for y in range(1, x)
               if direct[y] > 1 and isqrt(direct[y]) ** 2 == direct[y]}
    # For positive y there are at most y divisors, each remainder is < y.
    # Thus every possible positive square root is < y < x.
    squares = {k * k for k in range(2, x)}
    by_squares = {y for y in range(1, x) if sieved[y] in squares}
    assert by_root == by_squares
    return by_root


def verify_values(cases):
    for x, y, expected in cases:
        assert direct_sum(x, y) == sieve_sums(x, y)[y] == expected


if __name__ == "__main__":
    verify_values([(7, 6, 3), (7, 4, 4), (11, 4, 4)])
    print("Source examples: S(7,6)=3, S(7,4)=4, S(11,4)=4.")

    exceptions = [x for x in range(2, 14) if not witnesses(x)]
    assert exceptions == [2, 3, 4, 5, 6, 13]
    initial_witnesses = [4, 6, 5, 8, 4, 8]
    verify_values([(x, y, 4) for x, y in zip(range(7, 13), initial_witnesses)])
    totals_at_13 = [0, 1, 1, 2, 3, 3, 6, 7, 5, 7, 2, 5]
    assert [direct_sum(13, y) for y in range(1, 13)] == totals_at_13
    assert sieve_sums(13, 12)[1:] == totals_at_13
    print("Exceptions on the source's initial interval 2..13:", exceptions)

    verify_values([(4, 8, 4), (4, 27, 9), (14, 5, 4),
                   (16, 12, 9), (22, 13, 9), (40, 12, 9)])
    print("Prime and prime-cube examples and the three residual witnesses agree.")

    by_division = [m for m in range(10, 37) if 36 % m == 0]
    by_exponents = sorted(2**a * 3**b for a in range(3) for b in range(3)
                          if 2**a * 3**b > 9)
    assert by_division == by_exponents == [12, 18, 36]
    print("Divisors of 36 above 9 by enumeration and by exponents:", by_division)
