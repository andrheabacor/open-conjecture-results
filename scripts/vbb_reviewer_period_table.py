# Reviewer check for van Berkel-Bosma Conjecture 4 (arXiv:2609.16843v2).
# Computes the exact least preperiod k, period p and modulus m of S_{1,d-1,2d-1}
# from its characteristic sequence, using bitsets of sums of 1, 2 and 3 distinct terms.
from itertools import combinations


def greedy(init, limit):
    """All terms <= limit of the strict greedy 3-sumfree sequence with the given seeds."""
    ones = twos = threes = 0
    terms = []

    def add(x):
        nonlocal ones, twos, threes
        threes |= twos << x
        twos |= ones << x
        ones |= 1 << x
        terms.append(x)

    for x in init:
        add(x)
    for x in range(init[-1] + 1, limit + 1):
        if not (threes >> x) & 1:
            add(x)
    return terms


def brute(init, count):
    s = list(init)
    x = s[-1] + 1
    while len(s) < count:
        if x not in {a + b + c for a, b, c in combinations(s, 3)}:
            s.append(x)
        x += 1
    return s


def eventual(chars, max_period):
    """Least period P (and its least preperiod K) holding over at least 2/3 of the data."""
    n = len(chars)
    for period in range(1, max_period + 1):
        start = 0
        for i in range(n - period - 1, -1, -1):
            if chars[i] != chars[i + period]:
                start = i + 1
                break
        if start < n // 3:
            return start, period
    return None


def stats(init, limit=200000, max_period=5000):
    terms = greedy(init, limit)
    present = set(terms)
    chars = [1 if i in present else 0 for i in range(1, limit + 1)]
    start, period = eventual(chars, max_period)
    return sum(chars[:start]), sum(chars[start:start + period]), period


if __name__ == "__main__":
    for d in (4, 6, 7):
        assert brute([1, d - 1, 2 * d - 1], 45) == greedy([1, d - 1, 2 * d - 1], 3000)[:45]
    print("bitset algorithm agrees with brute force (d = 4, 6, 7; 45 terms)")
    print("paper's worked example S_{1,2,3} (k, p, m) =", stats([1, 2, 3], 20000), "expected (6, 5, 23)")
    for d in range(3, 21):
        k, p, m = stats([1, d - 1, 2 * d - 1])
        predicted = None if d in (3, 5) else (d + 3, d, 8 * d - 1)
        note = "excepted" if predicted is None else ("matches" if (k, p, m) == predicted else f"conjecture says {predicted}")
        print(f"d={d:2d}: (k, p, m) = ({k}, {p}, {m})  {note}")
